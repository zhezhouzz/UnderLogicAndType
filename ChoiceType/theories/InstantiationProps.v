(** * ChoiceType.InstantiationProps

    Multi-substitution instances for ChoiceType syntax, reusing the generic
    infrastructure from [CoreLang.InstantiationProps].  Contexts are tree-like
    and include binders in [ctx_fv], so only freshness-style context instances
    are registered here; exact fv-shrinking instances are intentionally avoided. *)

From CoreLang Require Export InstantiationProps.
From CoreLang Require Import Instantiation.
From ChoiceType Require Export LocallyNamelessProps LocallyNamelessInstances.
From ChoiceType Require Import Qualifier Syntax.

(** ** Freshness under multi-substitution *)

#[global] Instance MsubstFresh_qualifier : MsubstFresh type_qualifier.
Proof. eapply MsubstFresh_all; typeclasses eauto. Qed.

#[global] Instance MsubstFresh_cty : MsubstFresh choice_ty.
Proof. eapply MsubstFresh_all; typeclasses eauto. Qed.

#[global] Instance MsubstFresh_ctx : MsubstFresh ctx.
Proof. eapply MsubstFresh_all; typeclasses eauto. Qed.

(** ** Free-variable upper bounds under closed environments *)

#[global] Instance MsubstFv_qualifier : MsubstFv type_qualifier.
Proof. eapply MsubstFv_all; typeclasses eauto. Qed.

#[global] Instance MsubstFv_cty : MsubstFv choice_ty.
Proof. eapply MsubstFv_all; typeclasses eauto. Qed.

Lemma ctx_msubst_fv_subset σ Γ :
  closed_env σ →
  stale (m{σ} Γ) ⊆ stale Γ ∪ stale σ.
Proof.
  unfold msubst.
  refine (fin_maps.map_fold_ind
    (fun σ => closed_env σ ->
      stale (map_fold (fun x vx acc => {x := vx} acc) Γ σ) ⊆ stale Γ ∪ dom σ) _ _ σ).
  - intros _. set_solver.
  - intros x vx σ' Hfresh Hfold IH Hclosed.
    destruct (closed_env_insert σ' x vx Hfresh Hclosed) as [Hvx Hclosed'].
    rewrite Hfold.
    pose proof (ctx_fv_subst_subset x vx
      (map_fold (fun y vy acc => {y := vy} acc) Γ σ')) as Hstep.
    pose proof (IH Hclosed') as HIH.
    rewrite dom_insert_L. rewrite Hvx in Hstep. set_solver.
Qed.
