(** * ChoiceTyping.Naming

    Small proof-layer helpers for binder representatives.  These definitions
    keep the tlet proofs from repeatedly rebuilding the same freshness,
    context-domain, and open/substitution side conditions. *)

From CoreLang Require Import Instantiation InstantiationProps.
From ChoiceTyping Require Export LetResultWorld.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

(** ** Fresh representatives for tlet body binders *)

Definition tlet_fresh_avoid
    (L X : aset) (τ : choice_ty) (e : tm) (m : WfWorld) : aset :=
  L ∪ world_dom (m : World) ∪ X ∪ fv_cty τ ∪ fv_tm e.

Record tlet_fresh_name
    (L X : aset) (τ : choice_ty) (e : tm) (m : WfWorld) (x : atom) : Prop := {
  tlet_fresh_notin_L : x ∉ L;
  tlet_fresh_notin_world : x ∉ world_dom (m : World);
  tlet_fresh_notin_body : x ∉ X ∪ fv_cty τ ∪ fv_tm e;
}.

Lemma tlet_fresh_name_notin_X
    L X τ e (m : WfWorld) x :
  tlet_fresh_name L X τ e m x →
  x ∉ X.
Proof. intros Hfresh. destruct Hfresh. set_solver. Qed.

Lemma tlet_fresh_name_notin_fv_cty
    L X τ e (m : WfWorld) x :
  tlet_fresh_name L X τ e m x →
  x ∉ fv_cty τ.
Proof. intros Hfresh. destruct Hfresh. set_solver. Qed.

Lemma tlet_fresh_name_notin_fv_tm
    L X τ e (m : WfWorld) x :
  tlet_fresh_name L X τ e m x →
  x ∉ fv_tm e.
Proof. intros Hfresh. destruct Hfresh. set_solver. Qed.

Lemma tlet_fresh_name_notin_erased
    L X τ e (m : WfWorld) x :
  tlet_fresh_name L X τ e m x →
  x ∉ X ∪ fv_cty τ ∪ fv_tm e.
Proof. intros [HL HW HB]. exact HB. Qed.

Lemma tlet_fresh_name_for
    L X τ e (m : WfWorld) :
  tlet_fresh_name L X τ e m
    (fresh_for (tlet_fresh_avoid L X τ e m)).
Proof.
  pose proof (fresh_for_not_in (tlet_fresh_avoid L X τ e m)) as Hfresh.
  constructor; unfold tlet_fresh_avoid in Hfresh; set_solver.
Qed.

Ltac pick_tlet_fresh x L X τ e m :=
  let Hfresh := fresh "Hfresh" in
  set (x := fresh_for (tlet_fresh_avoid L X τ e m));
  pose proof (tlet_fresh_name_for L X τ e m) as Hfresh;
  change (tlet_fresh_name L X τ e m x) in Hfresh.

(** ** Context binder normal forms *)

Lemma erase_ctx_under_comma_bind_dom_nf Σ Γ x τ :
  dom (erase_ctx_under Σ (CtxComma Γ (CtxBind x τ))) =
  dom (erase_ctx_under Σ Γ) ∪ {[x]}.
Proof.
  unfold erase_ctx_under. simpl.
  rewrite !dom_union_L, dom_singleton_L. set_solver.
Qed.

Lemma erase_ctx_under_comma_bind_env_fresh Σ Γ x τ :
  x ∉ dom (erase_ctx_under Σ Γ) →
  erase_ctx_under Σ (CtxComma Γ (CtxBind x τ)) =
  <[x := erase_ty τ]> (erase_ctx_under Σ Γ).
Proof.
  intros Hfresh.
  unfold erase_ctx_under. simpl.
  apply (map_eq (M := gmap atom)). intros z.
  rewrite lookup_insert.
  destruct (decide (z = x)) as [->|Hzx].
  - rewrite decide_True by reflexivity.
    rewrite lookup_union_r.
    + rewrite lookup_union_r.
      * rewrite lookup_singleton. rewrite decide_True by reflexivity.
        reflexivity.
      * apply not_elem_of_dom. set_solver.
    + apply not_elem_of_dom. set_solver.
  - rewrite decide_False by congruence.
    rewrite !lookup_union.
    rewrite lookup_singleton.
    rewrite decide_False by congruence.
    destruct (Σ !! z); destruct (erase_ctx Γ !! z); reflexivity.
Qed.

Ltac ctx_name_norm :=
  repeat match goal with
  | H : context[dom (erase_ctx_under ?Σ (CtxComma ?Γ (CtxBind ?x ?τ)))] |- _ =>
      rewrite (erase_ctx_under_comma_bind_dom_nf Σ Γ x τ) in H
  | |- context[dom (erase_ctx_under ?Σ (CtxComma ?Γ (CtxBind ?x ?τ)))] =>
      rewrite (erase_ctx_under_comma_bind_dom_nf Σ Γ x τ)
  | Hfresh : ?x ∉ dom (erase_ctx_under ?Σ ?Γ),
    H : context[erase_ctx_under ?Σ (CtxComma ?Γ (CtxBind ?x ?τ))] |- _ =>
      rewrite (erase_ctx_under_comma_bind_env_fresh Σ Γ x τ Hfresh) in H
  | Hfresh : ?x ∉ dom (erase_ctx_under ?Σ ?Γ)
      |- context[erase_ctx_under ?Σ (CtxComma ?Γ (CtxBind ?x ?τ))] =>
      rewrite (erase_ctx_under_comma_bind_env_fresh Σ Γ x τ Hfresh)
  end.

(** ** Opening a body through an inserted result store *)

Lemma msubst_open_body_result
    X σ e x vx :
  x ∉ X →
  x ∉ fv_tm e →
  closed_env (store_restrict σ X) →
  stale vx = ∅ →
  is_lc vx →
  lc_env (store_restrict σ X) →
  subst_map (<[x := vx]> (store_restrict σ X)) (e ^^ x) =
  open_tm 0 vx (subst_map (store_restrict σ X) e).
Proof.
  intros HxX Hxe Hclosed Hvx_closed Hvx_lc Hlc.
  change (e ^^ x) with (open_tm 0 (vfvar x) e).
  apply msubst_intro_open_tm; eauto.
  change (x ∉ dom (store_restrict σ X) ∪ fv_tm e).
  rewrite store_restrict_dom. set_solver.
Qed.

Lemma steps_msubst_open_body_result
    X σ e x vx v :
  x ∉ X →
  x ∉ fv_tm e →
  closed_env (store_restrict σ X) →
  stale vx = ∅ →
  is_lc vx →
  lc_env (store_restrict σ X) →
  subst_map (<[x := vx]> (store_restrict σ X)) (e ^^ x) →* tret v →
  open_tm 0 vx (subst_map (store_restrict σ X) e) →* tret v.
Proof.
  intros HxX Hxe Hclosed Hvx_closed Hvx_lc Hlc Hsteps.
  rewrite <- (msubst_open_body_result X σ e x vx) by eauto.
  exact Hsteps.
Qed.

Lemma steps_open_body_to_msubst_result
    X σ e x vx v :
  x ∉ X →
  x ∉ fv_tm e →
  closed_env (store_restrict σ X) →
  stale vx = ∅ →
  is_lc vx →
  lc_env (store_restrict σ X) →
  open_tm 0 vx (subst_map (store_restrict σ X) e) →* tret v →
  subst_map (<[x := vx]> (store_restrict σ X)) (e ^^ x) →* tret v.
Proof.
  intros HxX Hxe Hclosed Hvx_closed Hvx_lc Hlc Hsteps.
  rewrite (msubst_open_body_result X σ e x vx) by eauto.
  exact Hsteps.
Qed.
