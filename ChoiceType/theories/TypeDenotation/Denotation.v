(** * ChoiceType.TypeDenotation.Denotation

    The recursive choice-type denotation.  The supporting atoms and syntactic
    sugar live in [Definitions.v], while proof-facing normalization and
    projection lemmas live in [Lemmas.v]. *)

From Stdlib Require Import Logic.FunctionalExtensionality Lia.
From LocallyNameless Require Import Tactics.
From CoreLang Require Import Instantiation InstantiationProps BasicTypingProps
  Sugar.
From ChoiceLogic Require Import FormulaDerived.
From ChoiceType Require Export TypeDenotation.Lemmas.
From ChoiceType Require Import BasicStore BasicTyping LocallyNamelessProps
  TypeDenotation.FormulaEquiv.

Local Notation FQ := FormulaQ.

(** The denotation carries its regularity obligation at every recursive node.
    This is deliberate: proofs can peel [FDenotObligationIn] through its API,
    while the structural body remains close to the paper semantics. *)
Fixpoint denot_ty_lvar_gas
    (gas : nat) (Σ : lty_env) (τ : choice_ty) (e : tm)
    {struct gas} : FQ :=
  FAnd (FDenotObligationIn Σ τ e)
    (match gas with
    | 0 => FTrue
    | S gas' =>
      match τ with
      | CTOver b φ =>
          FExprContIn Σ (TBase b) e (fun _ =>
            FFibVars (qual_vars φ ∖ {[LVBound 0]})
              (FOver (FTypeQualifier φ)))
      | CTUnder b φ =>
          FExprContIn Σ (TBase b) e (fun _ =>
            FFibVars (qual_vars φ ∖ {[LVBound 0]})
              (FUnder (FTypeQualifier φ)))
      | CTInter τ1 τ2 =>
          FAnd
            (denot_ty_lvar_gas gas' Σ τ1 e)
            (denot_ty_lvar_gas gas' Σ τ2 e)
      | CTUnion τ1 τ2 =>
          FOr
            (denot_ty_lvar_gas gas' Σ τ1 e)
            (denot_ty_lvar_gas gas' Σ τ2 e)
      | CTSum τ1 τ2 =>
          FPlus
            (denot_ty_lvar_gas gas' Σ τ1 e)
            (denot_ty_lvar_gas gas' Σ τ2 e)
      | CTArrow τx τ =>
          FForallTypedBind Σ (erase_ty τx) (fun Σx =>
            FImpl
              (denot_ty_lvar_gas gas' Σx
                (↑[0] τx) (tret (vbvar 0)))
              (denot_ty_lvar_gas gas' Σx τ
                (tapp_tm (↑[0] e) (vbvar 0))))
      | CTWand τx τ =>
          FForallTypedBind Σ (erase_ty τx) (fun Σx =>
            FWand
              (denot_ty_lvar_gas gas' Σx
                (↑[0] τx) (tret (vbvar 0)))
              (denot_ty_lvar_gas gas' Σx τ
                (tapp_tm (↑[0] e) (vbvar 0))))
      end
    end).

Definition denot_ty_lvar
    (Σ : lty_env) (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_lvar_gas (cty_depth τ) Σ τ e.

Lemma denot_ty_lvar_gas_atom_env_permute
    gas (Δ : gmap atom ty) x y Tx Ty τ e (m : WfWorld) :
  x <> y ->
  m ⊨ denot_ty_lvar_gas gas
    (atom_env_to_lty_env (<[x := Tx]> (<[y := Ty]> Δ))) τ e ->
  m ⊨ denot_ty_lvar_gas gas
    (atom_env_to_lty_env (<[y := Ty]> (<[x := Tx]> Δ))) τ e.
Proof.
  intros Hxy Hm.
  assert (<[x := Tx]> (<[y := Ty]> Δ) =
          <[y := Ty]> (<[x := Tx]> Δ)) as Hperm.
  {
    apply map_eq. intros z.
    rewrite !lookup_insert.
    repeat case_decide; subst; try congruence; reflexivity.
  }
  rewrite <- Hperm.
  exact Hm.
Qed.

Lemma denot_ty_lvar_gas_insert_atom_env_scoped
    gas (Δ : gmap atom ty) x T τ e (m : WfWorld) :
  x ∉ dom Δ ∪ fv_cty τ ∪ fv_tm e ->
  m ⊨ FClosedResourceIn (atom_env_to_lty_env (<[x := T]> Δ)) ->
  m ⊨ denot_ty_lvar_gas gas (atom_env_to_lty_env Δ) τ e ->
  formula_scoped_in_world ∅ m
    (denot_ty_lvar_gas gas (atom_env_to_lty_env (<[x := T]> Δ)) τ e).
Proof.
  (* Needs the precise FV relation
     [formula_fv (denot insert) ⊆ formula_fv (denot old) ∪ {[x]}].  The existing
     [denot_ty_lvar_gas_fv_subset] is only an over-approximation by
     [dom Δ ∪ fv_cty τ], which is too weak for scope transport. *)
Admitted.

Lemma denot_ty_lvar_gas_insert_atom_env_scoped_from_scope
    gas (Δ : gmap atom ty) x T τ e (m : WfWorld) :
  x ∉ dom Δ ∪ fv_cty τ ∪ fv_tm e ->
  m ⊨ FClosedResourceIn (atom_env_to_lty_env (<[x := T]> Δ)) ->
  formula_scoped_in_world ∅ m
    (denot_ty_lvar_gas gas (atom_env_to_lty_env Δ) τ e) ->
  formula_scoped_in_world ∅ m
    (denot_ty_lvar_gas gas (atom_env_to_lty_env (<[x := T]> Δ)) τ e).
Proof.
  (* Same precise-FV dependency as [denot_ty_lvar_gas_insert_atom_env_scoped]. *)
Admitted.

Lemma denot_ty_lvar_gas_insert_fresh_atom_env_zero
    (Δ : gmap atom ty) x T τ e (m : WfWorld) :
  x ∉ dom Δ ∪ fv_cty τ ∪ fv_tm e ->
  m ⊨ FClosedResourceIn (atom_env_to_lty_env (<[x := T]> Δ)) ->
  m ⊨ denot_ty_lvar_gas 0 (atom_env_to_lty_env Δ) τ e ->
  m ⊨ denot_ty_lvar_gas 0 (atom_env_to_lty_env (<[x := T]> Δ)) τ e.
Proof.
  intros Hfresh Hclosed Hm.
  cbn [denot_ty_lvar_gas].
  eapply res_models_and_intro_from_models.
  - eapply FDenotObligationIn_insert_fresh_atom_env; eauto.
    eapply res_models_and_elim_l. exact Hm.
  - unfold res_models, res_models_with_store.
    cbn [formula_measure res_models_with_store_fuel formula_scoped_in_world
      formula_fv].
    split; [set_solver | exact I].
Qed.

Lemma res_models_plus_insert_fresh_atom_env
    gas (Δ : gmap atom ty) x T τ1 τ2 e (m : WfWorld) :
  x ∉ dom Δ ∪ (fv_cty τ1 ∪ fv_cty τ2) ∪ fv_tm e ->
  m ⊨ FClosedResourceIn (atom_env_to_lty_env (<[x := T]> Δ)) ->
  (∀ m',
    m' ⊨ FClosedResourceIn (atom_env_to_lty_env (<[x := T]> Δ)) ->
    m' ⊨ denot_ty_lvar_gas gas (atom_env_to_lty_env Δ) τ1 e ->
    m' ⊨ denot_ty_lvar_gas gas (atom_env_to_lty_env (<[x := T]> Δ)) τ1 e) ->
  (∀ m',
    m' ⊨ FClosedResourceIn (atom_env_to_lty_env (<[x := T]> Δ)) ->
    m' ⊨ denot_ty_lvar_gas gas (atom_env_to_lty_env Δ) τ2 e ->
    m' ⊨ denot_ty_lvar_gas gas (atom_env_to_lty_env (<[x := T]> Δ)) τ2 e) ->
  m ⊨ FPlus
    (denot_ty_lvar_gas gas (atom_env_to_lty_env Δ) τ1 e)
    (denot_ty_lvar_gas gas (atom_env_to_lty_env Δ) τ2 e) ->
  m ⊨ FPlus
    (denot_ty_lvar_gas gas (atom_env_to_lty_env (<[x := T]> Δ)) τ1 e)
    (denot_ty_lvar_gas gas (atom_env_to_lty_env (<[x := T]> Δ)) τ2 e).
Proof.
  (* The [FPlus] witness may live on two subworlds of [m].  Since the inserted
     denotation mentions [x] in its obligation/scope, the split has to be lifted
     from the old support into the larger world using
     [res_sum_lift_along_restrict], then each branch uses the IH on the lifted
     subworld. *)
Admitted.

Lemma denot_ty_lvar_gas_insert_fresh_atom_env_arrow_body
    gas (Δ : gmap atom ty) x T τx τr e (m : WfWorld) :
  x ∉ dom Δ ∪ (fv_cty τx ∪ fv_cty τr) ∪ fv_tm e ->
  m ⊨ FClosedResourceIn (atom_env_to_lty_env (<[x := T]> Δ)) ->
  (∀ (Δ' : gmap atom ty) (m' : WfWorld),
    x ∉ dom Δ' ∪ fv_cty (↑[0] τx) ∪ fv_tm (tret (vbvar 0)) ->
    m' ⊨ FClosedResourceIn (atom_env_to_lty_env (<[x := T]> Δ')) ->
    m' ⊨ denot_ty_lvar_gas gas (atom_env_to_lty_env Δ') (↑[0] τx)
      (tret (vbvar 0)) ->
    m' ⊨ denot_ty_lvar_gas gas (atom_env_to_lty_env (<[x := T]> Δ'))
      (↑[0] τx) (tret (vbvar 0))) ->
  (∀ (Δ' : gmap atom ty) (m' : WfWorld),
    x ∉ dom Δ' ∪ fv_cty τr ∪ fv_tm (tapp_tm (↑[0] e) (vbvar 0)) ->
    m' ⊨ FClosedResourceIn (atom_env_to_lty_env (<[x := T]> Δ')) ->
    m' ⊨ denot_ty_lvar_gas gas (atom_env_to_lty_env Δ') τr
      (tapp_tm (↑[0] e) (vbvar 0)) ->
    m' ⊨ denot_ty_lvar_gas gas (atom_env_to_lty_env (<[x := T]> Δ'))
      τr (tapp_tm (↑[0] e) (vbvar 0))) ->
  m ⊨ FForallTypedBind (atom_env_to_lty_env Δ) (erase_ty τx)
    (fun Σx => FImpl
      (denot_ty_lvar_gas gas Σx (↑[0] τx) (tret (vbvar 0)))
      (denot_ty_lvar_gas gas Σx τr (tapp_tm (↑[0] e) (vbvar 0)))) ->
  m ⊨ FForallTypedBind (atom_env_to_lty_env (<[x := T]> Δ)) (erase_ty τx)
    (fun Σx => FImpl
      (denot_ty_lvar_gas gas Σx (↑[0] τx) (tret (vbvar 0)))
      (denot_ty_lvar_gas gas Σx τr (tapp_tm (↑[0] e) (vbvar 0)))).
Proof.
  (* Binder transport for the [CTArrow] branch.  After opening the outer typed
     forall with a fresh [y], use the opened typed-body helper above.  The
     antecedent is contravariant, so the argument mapper uses the old context
     [<[y := erase_ty τx]> Δ]; the consequent mapper uses the inserted context
     [<[x := T]> (<[y := erase_ty τx]> Δ)]. *)
Admitted.

Lemma denot_ty_lvar_gas_insert_fresh_atom_env_wand_body
    gas (Δ : gmap atom ty) x T τx τr e (m : WfWorld) :
  x ∉ dom Δ ∪ (fv_cty τx ∪ fv_cty τr) ∪ fv_tm e ->
  m ⊨ FClosedResourceIn (atom_env_to_lty_env (<[x := T]> Δ)) ->
  (∀ (Δ' : gmap atom ty) (m' : WfWorld),
    x ∉ dom Δ' ∪ fv_cty (↑[0] τx) ∪ fv_tm (tret (vbvar 0)) ->
    m' ⊨ FClosedResourceIn (atom_env_to_lty_env (<[x := T]> Δ')) ->
    m' ⊨ denot_ty_lvar_gas gas (atom_env_to_lty_env Δ') (↑[0] τx)
      (tret (vbvar 0)) ->
    m' ⊨ denot_ty_lvar_gas gas (atom_env_to_lty_env (<[x := T]> Δ'))
      (↑[0] τx) (tret (vbvar 0))) ->
  (∀ (Δ' : gmap atom ty) (m' : WfWorld),
    x ∉ dom Δ' ∪ fv_cty τr ∪ fv_tm (tapp_tm (↑[0] e) (vbvar 0)) ->
    m' ⊨ FClosedResourceIn (atom_env_to_lty_env (<[x := T]> Δ')) ->
    m' ⊨ denot_ty_lvar_gas gas (atom_env_to_lty_env Δ') τr
      (tapp_tm (↑[0] e) (vbvar 0)) ->
    m' ⊨ denot_ty_lvar_gas gas (atom_env_to_lty_env (<[x := T]> Δ'))
      τr (tapp_tm (↑[0] e) (vbvar 0))) ->
  m ⊨ FForallTypedBind (atom_env_to_lty_env Δ) (erase_ty τx)
    (fun Σx => FWand
      (denot_ty_lvar_gas gas Σx (↑[0] τx) (tret (vbvar 0)))
      (denot_ty_lvar_gas gas Σx τr (tapp_tm (↑[0] e) (vbvar 0)))) ->
  m ⊨ FForallTypedBind (atom_env_to_lty_env (<[x := T]> Δ)) (erase_ty τx)
    (fun Σx => FWand
      (denot_ty_lvar_gas gas Σx (↑[0] τx) (tret (vbvar 0)))
      (denot_ty_lvar_gas gas Σx τr (tapp_tm (↑[0] e) (vbvar 0)))).
Proof.
  (* Same binder transport as the Arrow case, but the opened body uses
     [res_models_wand_map] instead of [res_models_impl_map]. *)
Admitted.

Lemma denot_ty_lvar_gas_insert_fresh_atom_env
    gas (Δ : gmap atom ty) x T τ e (m : WfWorld) :
  x ∉ dom Δ ∪ fv_cty τ ∪ fv_tm e ->
  m ⊨ FClosedResourceIn (atom_env_to_lty_env (<[x := T]> Δ)) ->
  m ⊨ denot_ty_lvar_gas gas (atom_env_to_lty_env Δ) τ e ->
  m ⊨ denot_ty_lvar_gas gas (atom_env_to_lty_env (<[x := T]> Δ)) τ e.
Proof.
  revert Δ x T τ e m.
  induction gas as [|gas IH]; intros Δ x T τ e m Hfresh Hclosed Hm.
  - eapply denot_ty_lvar_gas_insert_fresh_atom_env_zero; eauto.
  - cbn [denot_ty_lvar_gas] in Hm |- *.
    eapply res_models_and_intro_from_models.
    + eapply FDenotObligationIn_insert_fresh_atom_env; eauto.
      eapply res_models_and_elim_l. exact Hm.
    + destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τr|τx τr];
        cbn [denot_ty_lvar_gas fv_cty fv_tm] in *;
        pose proof (res_models_and_elim_r _ _ _ Hm) as Hbody.
      * eapply FExprContIn_insert_fresh_atom_env_const; eauto; set_solver.
      * eapply FExprContIn_insert_fresh_atom_env_const; eauto; set_solver.
      * eapply res_models_and_intro_from_models.
        -- eapply IH; [set_solver | exact Hclosed |].
           eapply res_models_and_elim_l. exact Hbody.
        -- eapply IH; [set_solver | exact Hclosed |].
           eapply res_models_and_elim_r. exact Hbody.
      * destruct Hbody as [Hscope_body Hbody_raw].
        pose proof (proj1 (formula_scoped_or_iff ∅ m _ _) Hscope_body)
          as [Hscope_left Hscope_right].
        destruct Hbody_raw as [Hleft | Hright].
        -- eapply res_models_or_intro_l.
           ++ apply (proj2 (formula_scoped_or_iff ∅ m _ _)).
              split.
              ** eapply denot_ty_lvar_gas_insert_atom_env_scoped_from_scope; eauto; set_solver.
              ** eapply denot_ty_lvar_gas_insert_atom_env_scoped_from_scope; eauto; set_solver.
           ++ eapply IH; [set_solver | exact Hclosed |].
              unfold res_models, res_models_with_store.
              models_fuel_irrel Hleft.
        -- eapply res_models_or_intro_r.
           ++ apply (proj2 (formula_scoped_or_iff ∅ m _ _)).
              split.
              ** eapply denot_ty_lvar_gas_insert_atom_env_scoped_from_scope; eauto; set_solver.
              ** eapply denot_ty_lvar_gas_insert_atom_env_scoped_from_scope; eauto; set_solver.
           ++ eapply IH; [set_solver | exact Hclosed |].
              unfold res_models, res_models_with_store.
              models_fuel_irrel Hright.
      * (* CTSum: lift the old split to worlds carrying the inserted coordinate. *)
        eapply res_models_plus_insert_fresh_atom_env; [set_solver | exact Hclosed | | | exact Hbody].
        -- intros m' Hclosed' Hm'. eapply IH; [set_solver | exact Hclosed' | exact Hm'].
        -- intros m' Hclosed' Hm'. eapply IH; [set_solver | exact Hclosed' | exact Hm'].
      * (* CTArrow: use [FForallTypedBind_insert_fresh_atom_env_map] and IH. *)
        eapply denot_ty_lvar_gas_insert_fresh_atom_env_arrow_body; eauto.
      * (* CTWand: same binder transport shape as [CTArrow], with wand map. *)
        eapply denot_ty_lvar_gas_insert_fresh_atom_env_wand_body; eauto.
Admitted.

Lemma denot_ty_lvar_gas_drop_insert_fresh_atom_env
    gas (Δ : gmap atom ty) x T τ e (m : WfWorld) :
  x ∉ dom Δ ∪ fv_cty τ ∪ fv_tm e ->
  m ⊨ denot_ty_lvar_gas gas
    (atom_env_to_lty_env (<[x := T]> Δ)) τ e ->
  m ⊨ denot_ty_lvar_gas gas (atom_env_to_lty_env Δ) τ e.
Proof.
  (* Not on the current TLet/TArrow path.  The hard cases are the
     continuation-style [CTOver]/[CTUnder] branches, which need the drop
     counterparts of the [FExprContIn] sugar lemmas. *)
Admitted.

Definition denot_ty_body_lvar_gas := denot_ty_lvar_gas.
Definition denot_ty_body_lvar := denot_ty_lvar.

Definition denot_ty_on
    (Σ : gmap atom ty) (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_lvar (atom_env_to_lty_env Σ) τ e.

Definition denot_ty_body
    (Σ : gmap atom ty) (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_on Σ τ e.

Lemma denot_ty_on_nf Σ τ e :
  denot_ty_lvar (atom_env_to_lty_env Σ) τ e = denot_ty_on Σ τ e.
Proof. reflexivity. Qed.

Lemma denot_ty_body_nf Σ τ e :
  denot_ty_body_lvar (atom_env_to_lty_env Σ) τ e = denot_ty_body Σ τ e.
Proof. reflexivity. Qed.

#[global] Hint Rewrite denot_ty_body_nf denot_ty_on_nf : denot_nf.

Ltac denot_ty_nf :=
  autorewrite with denot_nf.

Ltac denot_ty_nf_in H :=
  autorewrite with denot_nf in H.

Definition denot_ty_under (Σ : gmap atom ty) (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_on Σ τ e.

Definition denot_ty (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_under ∅ τ e.

Definition denot_ty_in_ctx (Γ : ctx) (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_under (erase_ctx Γ) τ e.

Notation "'erase_ctx_under' Σ Γ" := (Σ ∪ erase_ctx Γ)
  (at level 10, Σ at level 9, Γ at level 9, only parsing).

Definition denot_ty_in_ctx_under
    (Σ : gmap atom ty) (Γ : ctx) (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_on (erase_ctx_under Σ Γ) τ e.

Definition denot_ty_total_in_ctx_under
    (Σ : gmap atom ty) (Γ : ctx) (τ : choice_ty) (e : tm)
    (m : WfWorld) : Prop :=
  m ⊨ denot_ty_in_ctx_under Σ Γ τ e ∧
  expr_total_on e m.

Definition entails_total (φ : FQ) (P : WfWorld → Prop) : Prop :=
  ∀ m, m ⊨ φ → P m.

Definition ty_env_agree_on (X : aset) (Σ1 Σ2 : gmap atom ty) : Prop :=
  ∀ x, x ∈ X → Σ1 !! x = Σ2 !! x.

Lemma ty_env_agree_on_insert_same X Σ1 Σ2 x T :
  ty_env_agree_on (X ∖ {[x]}) Σ1 Σ2 →
  ty_env_agree_on X (<[x := T]> Σ1) (<[x := T]> Σ2).
Proof.
  intros Hagree z Hz.
  destruct (decide (z = x)) as [->|Hne].
  - rewrite !(lookup_insert_eq _ x T). reflexivity.
  - rewrite !lookup_insert_ne by congruence.
    apply Hagree. set_solver.
Qed.

Lemma ty_env_agree_on_insert_same_keep X Σ1 Σ2 x T :
  ty_env_agree_on X Σ1 Σ2 →
  ty_env_agree_on (X ∪ {[x]}) (<[x := T]> Σ1) (<[x := T]> Σ2).
Proof.
  intros Hagree.
  apply ty_env_agree_on_insert_same.
  intros z Hz. apply Hagree. set_solver.
Qed.

Definition denot_lvar_env_reads (τ : choice_ty) (e : tm) : lvset :=
  choice_ty_lvars τ ∪ tm_lvars e.

Lemma lty_env_eq_of_dom_agree Σ1 Σ2 :
  dom Σ1 = dom Σ2 →
  lty_env_agree_on_lvars (dom Σ1) Σ1 Σ2 →
  Σ1 = Σ2.
Proof.
  intros Hdom Hagree.
  apply map_eq. intros v.
  destruct (Σ1 !! v) as [T|] eqn:Hlookup.
  - apply Hagree.
    apply elem_of_dom. eexists. exact Hlookup.
  - destruct (Σ2 !! v) as [T|] eqn:Hlookup2.
    2:{
      change (Σ1 !! v = Σ2 !! v).
      rewrite Hlookup, Hlookup2. reflexivity.
    }
    exfalso.
    assert (v ∈ dom Σ2) by (apply elem_of_dom; eexists; exact Hlookup2).
    rewrite <- Hdom in H.
    assert (v ∉ dom Σ1).
    {
      apply not_elem_of_dom in Hlookup. exact Hlookup.
    }
    contradiction.
Qed.

Lemma denot_ty_lvar_gas_env_agree gas Σ1 Σ2 τ e :
  dom Σ1 = dom Σ2 →
  lty_env_agree_on_lvars (dom Σ1) Σ1 Σ2 →
  formula_store_equiv
    (denot_ty_lvar_gas gas Σ1 τ e)
    (denot_ty_lvar_gas gas Σ2 τ e).
Proof.
  intros Hdom Hagree.
  pose proof (lty_env_eq_of_dom_agree Σ1 Σ2 Hdom Hagree) as ->.
  reflexivity.
Qed.

Lemma denot_ty_lvar_env_agree Σ1 Σ2 τ e :
  dom Σ1 = dom Σ2 →
  lty_env_agree_on_lvars (dom Σ1) Σ1 Σ2 →
  formula_store_equiv (denot_ty_lvar Σ1 τ e) (denot_ty_lvar Σ2 τ e).
Proof.
  unfold denot_ty_lvar.
  apply denot_ty_lvar_gas_env_agree.
Qed.

Lemma denot_ty_on_env_agree Σ1 Σ2 τ e :
  dom (atom_env_to_lty_env Σ1) = dom (atom_env_to_lty_env Σ2) →
  lty_env_agree_on_lvars
    (dom (atom_env_to_lty_env Σ1))
    (atom_env_to_lty_env Σ1) (atom_env_to_lty_env Σ2) →
  formula_store_equiv (denot_ty_on Σ1 τ e) (denot_ty_on Σ2 τ e).
Proof.
  unfold denot_ty_on.
  apply denot_ty_lvar_env_agree.
Qed.

Lemma cty_shift_depth k τ :
  cty_depth (cty_shift k τ) = cty_depth τ.
Proof.
  induction τ in k |- *; cbn [cty_shift cty_depth]; try reflexivity;
    rewrite ?IHτ1, ?IHτ2; reflexivity.
Qed.

Lemma qual_shift_from_dom k φ :
  qual_dom (qual_shift_from k φ) = qual_dom φ.
Proof.
  destruct φ as [D p].
  cbn [qual_shift_from qual_dom].
  apply lvars_fv_shift_from.
Qed.

Lemma cty_shift_fv k τ :
  fv_cty (cty_shift k τ) = fv_cty τ.
Proof.
  induction τ in k |- *; cbn [cty_shift fv_cty]; try reflexivity;
    rewrite ?IHτ1, ?IHτ2, ?qual_shift_from_dom; reflexivity.
Qed.

Lemma formula_fv_denot_ty_lvar_gas_cty_vars_equiv gas Σ τ1 τ2 e :
  τ1 ≡τv τ2 →
  formula_fv (denot_ty_lvar_gas gas Σ τ1 e) =
  formula_fv (denot_ty_lvar_gas gas Σ τ2 e).
Proof.
  revert Σ τ1 τ2 e.
  induction gas as [|gas IH]; intros Σ τ1 τ2 e Hτ.
  - cbn [denot_ty_lvar_gas formula_fv].
    unfold FDenotObligationIn.
    rewrite !formula_fv_FStoreResourceAtom_lvars.
    reflexivity.
  - destruct τ1 as [b1 φ1|b1 φ1|τ11 τ12|τ11 τ12|τ11 τ12|τx1 τr1|τx1 τr1];
      destruct τ2 as [b2 φ2|b2 φ2|τ21 τ22|τ21 τ22|τ21 τ22|τx2 τr2|τx2 τr2];
      cbn [denot_ty_lvar_gas formula_fv cty_vars_equiv] in *;
      try tauto.
    + destruct Hτ as [Hb Hvars]. subst b2.
      unfold FDenotObligationIn, FExprContIn, FExprContBody,
        FForallTypedBody, FClosedResourceIn.
      rewrite !formula_fv_FStoreResourceAtom_lvars.
      cbn [formula_fv].
      rewrite !formula_fv_FTypeQualifier.
      destruct φ1, φ2. cbn [qual_dom qual_vars] in *.
      subst. reflexivity.
    + destruct Hτ as [Hb Hvars]. subst b2.
      unfold FDenotObligationIn, FExprContIn, FExprContBody,
        FForallTypedBody, FClosedResourceIn.
      rewrite !formula_fv_FStoreResourceAtom_lvars.
      cbn [formula_fv].
      rewrite !formula_fv_FTypeQualifier.
      destruct φ1, φ2. cbn [qual_dom qual_vars] in *.
      subst. reflexivity.
    + destruct Hτ as [H1 H2].
      rewrite (IH Σ _ _ e H1), (IH Σ _ _ e H2). reflexivity.
    + destruct Hτ as [H1 H2].
      rewrite (IH Σ _ _ e H1), (IH Σ _ _ e H2). reflexivity.
    + destruct Hτ as [H1 H2].
      rewrite (IH Σ _ _ e H1), (IH Σ _ _ e H2). reflexivity.
    + destruct Hτ as [Harg Hret].
      unfold FDenotObligationIn, FForallTypedBind, FForallTypedBody,
        FClosedResourceIn.
      rewrite !formula_fv_FStoreResourceAtom_lvars.
      rewrite (cty_vars_equiv_erase _ _ Harg).
      cbn [formula_fv].
      change (↑[0] τx1) with (cty_shift 0 τx1).
      change (↑[0] τx2) with (cty_shift 0 τx2).
      rewrite (IH (typed_lty_env_bind Σ (erase_ty τx2)) _ _
        (tret (vbvar 0)) (cty_vars_equiv_shift_from 0 _ _ Harg)).
      rewrite (IH (typed_lty_env_bind Σ (erase_ty τx2)) _ _
        (tapp_tm (↑[0] e) (vbvar 0)) Hret).
      reflexivity.
    + destruct Hτ as [Harg Hret].
      unfold FDenotObligationIn, FForallTypedBind, FForallTypedBody,
        FClosedResourceIn.
      rewrite !formula_fv_FStoreResourceAtom_lvars.
      rewrite (cty_vars_equiv_erase _ _ Harg).
      cbn [formula_fv].
      change (↑[0] τx1) with (cty_shift 0 τx1).
      change (↑[0] τx2) with (cty_shift 0 τx2).
      rewrite (IH (typed_lty_env_bind Σ (erase_ty τx2)) _ _
        (tret (vbvar 0)) (cty_vars_equiv_shift_from 0 _ _ Harg)).
      rewrite (IH (typed_lty_env_bind Σ (erase_ty τx2)) _ _
        (tapp_tm (↑[0] e) (vbvar 0)) Hret).
      reflexivity.
Qed.

Lemma formula_fv_denot_ty_lvar_gas_tm_irrelevant gas Σ τ e1 e2 :
  formula_fv (denot_ty_lvar_gas gas Σ τ e1) =
  formula_fv (denot_ty_lvar_gas gas Σ τ e2).
Proof.
  revert Σ τ e1 e2.
  induction gas as [|gas IH]; intros Σ τ e1 e2.
  - cbn [denot_ty_lvar_gas formula_fv].
    unfold FDenotObligationIn.
    rewrite !formula_fv_FStoreResourceAtom_lvars.
    reflexivity.
  - destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τ|τx τ];
      cbn [denot_ty_lvar_gas formula_fv].
    + unfold FDenotObligationIn, FExprContIn, FExprContBody,
        FForallTypedBody, FClosedResourceIn.
      rewrite !formula_fv_FStoreResourceAtom_lvars.
      cbn [formula_fv]. reflexivity.
    + unfold FDenotObligationIn, FExprContIn, FExprContBody,
        FForallTypedBody, FClosedResourceIn.
      rewrite !formula_fv_FStoreResourceAtom_lvars.
      cbn [formula_fv]. reflexivity.
    + rewrite (IH Σ τ1 e1 e2), (IH Σ τ2 e1 e2). reflexivity.
    + rewrite (IH Σ τ1 e1 e2), (IH Σ τ2 e1 e2). reflexivity.
    + rewrite (IH Σ τ1 e1 e2), (IH Σ τ2 e1 e2). reflexivity.
    + unfold FDenotObligationIn, FForallTypedBind, FForallTypedBody,
        FClosedResourceIn.
      rewrite !formula_fv_FStoreResourceAtom_lvars.
      cbn [formula_fv].
      rewrite (IH (typed_lty_env_bind Σ (erase_ty τx)) τ
        (tapp_tm (↑[0] e1) (vbvar 0))
        (tapp_tm (↑[0] e2) (vbvar 0))).
      reflexivity.
    + unfold FDenotObligationIn, FForallTypedBind, FForallTypedBody,
        FClosedResourceIn.
      rewrite !formula_fv_FStoreResourceAtom_lvars.
      cbn [formula_fv].
      rewrite (IH (typed_lty_env_bind Σ (erase_ty τx)) τ
        (tapp_tm (↑[0] e1) (vbvar 0))
        (tapp_tm (↑[0] e2) (vbvar 0))).
      reflexivity.
Qed.

Lemma lty_env_insert_lvars_fv_dom_subset (Σ : lty_env) ν (T : ty) :
  lvars_fv (dom (<[ν := T]> Σ)) ⊆
    lvars_fv (dom Σ) ∪ lvars_fv ({[ν]} : lvset).
Proof.
  (* Direct set fact about the free atom support of an lty-env insertion.
     Temporarily admitted to restore the workbench after interrupting the proof. *)
Admitted.

Lemma formula_fv_denot_ty_lvar_gas_insert_lty_env
    gas (Σ : lty_env) ν (T : ty) τ e :
  formula_fv (denot_ty_lvar_gas gas (<[ν := T]> Σ) τ e) ⊆
    formula_fv (denot_ty_lvar_gas gas Σ τ e) ∪ lvars_fv ({[ν]} : lvset).
Proof.
  (* General FV insert transport for denotations.  The intended proof is by
     induction on [gas]; temporarily admitted to keep the TypeDenotation layer
     compiling while the proof is being reviewed. *)
Admitted.

Lemma denot_ty_lvar_gas_saturate τ :
  ∀ gas Σ e,
    cty_depth τ <= gas →
    denot_ty_lvar_gas gas Σ τ e =
    denot_ty_lvar_gas (cty_depth τ) Σ τ e.
Proof.
  assert (Hsat :
    ∀ gas τ Σ e,
      cty_depth τ <= gas →
      denot_ty_lvar_gas gas Σ τ e =
      denot_ty_lvar_gas (cty_depth τ) Σ τ e).
  {
    induction gas as [gas IH] using lt_wf_ind.
    intros τ0 Σ e Hgas.
    destruct gas as [|gas']; destruct τ0; cbn [cty_depth] in Hgas; try lia;
      cbn [cty_depth denot_ty_lvar_gas].
    - reflexivity.
    - reflexivity.
    - rewrite (IH gas' ltac:(lia) τ0_1 Σ e ltac:(lia)).
      rewrite (IH gas' ltac:(lia) τ0_2 Σ e ltac:(lia)).
      rewrite (IH (Nat.max (cty_depth τ0_1) (cty_depth τ0_2))
        ltac:(lia) τ0_1 Σ e ltac:(lia)).
      rewrite (IH (Nat.max (cty_depth τ0_1) (cty_depth τ0_2))
        ltac:(lia) τ0_2 Σ e ltac:(lia)).
      reflexivity.
    - rewrite (IH gas' ltac:(lia) τ0_1 Σ e ltac:(lia)).
      rewrite (IH gas' ltac:(lia) τ0_2 Σ e ltac:(lia)).
      rewrite (IH (Nat.max (cty_depth τ0_1) (cty_depth τ0_2))
        ltac:(lia) τ0_1 Σ e ltac:(lia)).
      rewrite (IH (Nat.max (cty_depth τ0_1) (cty_depth τ0_2))
        ltac:(lia) τ0_2 Σ e ltac:(lia)).
      reflexivity.
    - rewrite (IH gas' ltac:(lia) τ0_1 Σ e ltac:(lia)).
      rewrite (IH gas' ltac:(lia) τ0_2 Σ e ltac:(lia)).
      rewrite (IH (Nat.max (cty_depth τ0_1) (cty_depth τ0_2))
        ltac:(lia) τ0_1 Σ e ltac:(lia)).
      rewrite (IH (Nat.max (cty_depth τ0_1) (cty_depth τ0_2))
        ltac:(lia) τ0_2 Σ e ltac:(lia)).
      reflexivity.
    - f_equal. f_equal.
      apply functional_extensionality; intro Σx.
      change (↑[0] τ0_1) with (cty_shift 0 τ0_1).
      rewrite (IH gas' ltac:(lia) (cty_shift 0 τ0_1) Σx
        (tret (vbvar 0)) ltac:(rewrite cty_shift_depth; lia)).
      rewrite (IH (Nat.max (cty_depth τ0_1) (cty_depth τ0_2)) ltac:(lia)
        (cty_shift 0 τ0_1) Σx (tret (vbvar 0))
        ltac:(rewrite cty_shift_depth; lia)).
      rewrite (IH gas' ltac:(lia) τ0_2 Σx
        (tapp_tm (↑[0] e) (vbvar 0)) ltac:(lia)).
      rewrite (IH (Nat.max (cty_depth τ0_1) (cty_depth τ0_2)) ltac:(lia)
        τ0_2 Σx (tapp_tm (↑[0] e) (vbvar 0)) ltac:(lia)).
      reflexivity.
    - f_equal. f_equal.
      apply functional_extensionality; intro Σx.
      change (↑[0] τ0_1) with (cty_shift 0 τ0_1).
      rewrite (IH gas' ltac:(lia) (cty_shift 0 τ0_1) Σx
        (tret (vbvar 0)) ltac:(rewrite cty_shift_depth; lia)).
      rewrite (IH (Nat.max (cty_depth τ0_1) (cty_depth τ0_2)) ltac:(lia)
        (cty_shift 0 τ0_1) Σx (tret (vbvar 0))
        ltac:(rewrite cty_shift_depth; lia)).
      rewrite (IH gas' ltac:(lia) τ0_2 Σx
        (tapp_tm (↑[0] e) (vbvar 0)) ltac:(lia)).
      rewrite (IH (Nat.max (cty_depth τ0_1) (cty_depth τ0_2)) ltac:(lia)
        τ0_2 Σx (tapp_tm (↑[0] e) (vbvar 0)) ltac:(lia)).
      reflexivity.
  }
  intros gas Σ e Hgas.
  apply Hsat. exact Hgas.
Qed.

Lemma formula_fv_open_denot_ty_lvar_gas k x gas Σ τ e :
  LVFree x ∉ dom Σ →
  formula_fv (formula_open k x (denot_ty_lvar_gas gas Σ τ e)) =
  formula_fv (denot_ty_lvar_gas gas ({k ~> x} Σ)
    ({k ~> x} τ) ({k ~> x} e)).
Proof.
  revert k x Σ τ e.
  induction gas as [|gas IH]; intros k x Σ τ e Hfresh;
    cbn [denot_ty_lvar_gas formula_open formula_fv].
  - rewrite formula_fv_open_FDenotObligationIn. reflexivity.
  - rewrite formula_fv_open_FDenotObligationIn.
    destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τ|τx τ];
      cbn [cty_open open_one open_cty_atom_inst denot_ty_lvar_gas
        formula_open formula_fv].
    + rewrite (formula_fv_open_FExprContIn k x Σ (TBase b) e
        (fun _ => FFibVars (qual_vars φ ∖ {[LVBound 0]})
          (FOver (FTypeQualifier φ)))
        (fun _ => FFibVars (qual_vars ({S k ~> x} φ) ∖ {[LVBound 0]})
          (FOver (FTypeQualifier ({S k ~> x} φ))))) by
        (try exact Hfresh; intros; apply formula_fv_open_FResultQualifier_over_body).
      reflexivity.
    + rewrite (formula_fv_open_FExprContIn k x Σ (TBase b) e
        (fun _ => FFibVars (qual_vars φ ∖ {[LVBound 0]})
          (FUnder (FTypeQualifier φ)))
        (fun _ => FFibVars (qual_vars ({S k ~> x} φ) ∖ {[LVBound 0]})
          (FUnder (FTypeQualifier ({S k ~> x} φ))))) by
        (try exact Hfresh; intros; apply formula_fv_open_FResultQualifier_under_body).
      reflexivity.
    + rewrite (IH k x Σ τ1 e Hfresh).
      rewrite (IH k x Σ τ2 e Hfresh).
      reflexivity.
    + rewrite (IH k x Σ τ1 e Hfresh).
      rewrite (IH k x Σ τ2 e Hfresh).
      reflexivity.
    + rewrite (IH k x Σ τ1 e Hfresh).
      rewrite (IH k x Σ τ2 e Hfresh).
      reflexivity.
    + rewrite cty_open_preserves_erasure.
      rewrite (formula_fv_open_FForallTypedBind k x Σ (erase_ty τx)
        (fun Σx => FImpl
          (denot_ty_lvar_gas gas Σx (↑[0] τx) (tret (vbvar 0)))
          (denot_ty_lvar_gas gas Σx τ
            (tapp_tm (↑[0] e) (vbvar 0))))
        (fun Σx => FImpl
          (denot_ty_lvar_gas gas Σx (↑[0] ({k ~> x} τx))
            (tret (vbvar 0)))
          (denot_ty_lvar_gas gas Σx ({S k ~> x} τ)
            (tapp_tm (↑[0] ({k ~> x} e)) (vbvar 0))))).
      2:{ exact Hfresh. }
      2:{
        cbn [formula_open formula_fv].
        rewrite (IH (S k) x (typed_lty_env_bind Σ (erase_ty τx))
          (↑[0] τx) (tret (vbvar 0))).
        2:{ apply typed_lty_env_bind_free_notin. exact Hfresh. }
        rewrite typed_lty_env_bind_open_under by exact Hfresh.
        change ({S k ~> x} (↑[0] τx)) with
          (cty_open (S k) x (cty_shift 0 τx)).
        rewrite cty_open_shift_under_equiv.
        rewrite (IH (S k) x (typed_lty_env_bind Σ (erase_ty τx))
          τ (tapp_tm (↑[0] e) (vbvar 0))).
        2:{ apply typed_lty_env_bind_free_notin. exact Hfresh. }
        rewrite typed_lty_env_bind_open_under by exact Hfresh.
        rewrite open_tapp_tm_shift_bvar0_under_lvar.
        reflexivity.
      }
      reflexivity.
    + rewrite cty_open_preserves_erasure.
      rewrite (formula_fv_open_FForallTypedBind k x Σ (erase_ty τx)
        (fun Σx => FWand
          (denot_ty_lvar_gas gas Σx (↑[0] τx) (tret (vbvar 0)))
          (denot_ty_lvar_gas gas Σx τ
            (tapp_tm (↑[0] e) (vbvar 0))))
        (fun Σx => FWand
          (denot_ty_lvar_gas gas Σx (↑[0] ({k ~> x} τx))
            (tret (vbvar 0)))
          (denot_ty_lvar_gas gas Σx ({S k ~> x} τ)
            (tapp_tm (↑[0] ({k ~> x} e)) (vbvar 0))))).
      2:{ exact Hfresh. }
      2:{
        cbn [formula_open formula_fv].
        rewrite (IH (S k) x (typed_lty_env_bind Σ (erase_ty τx))
          (↑[0] τx) (tret (vbvar 0))).
        2:{ apply typed_lty_env_bind_free_notin. exact Hfresh. }
        rewrite typed_lty_env_bind_open_under by exact Hfresh.
        change ({S k ~> x} (↑[0] τx)) with
          (cty_open (S k) x (cty_shift 0 τx)).
        rewrite cty_open_shift_under_equiv.
        rewrite (IH (S k) x (typed_lty_env_bind Σ (erase_ty τx))
          τ (tapp_tm (↑[0] e) (vbvar 0))).
        2:{ apply typed_lty_env_bind_free_notin. exact Hfresh. }
        rewrite typed_lty_env_bind_open_under by exact Hfresh.
        rewrite open_tapp_tm_shift_bvar0_under_lvar.
        reflexivity.
      }
      reflexivity.
Qed.

Lemma formula_fv_open_env_denot_ty_lvar_gas η gas Σ τ e :
  open_env_fresh_for_lvars η (dom Σ) →
  formula_fv
    (formula_open_env η (denot_ty_lvar_gas gas Σ τ e)) =
  formula_fv
    (denot_ty_lvar_gas gas
      (lty_env_open_lvars η Σ)
      (open_cty_env η τ)
      (open_tm_env η e)).
Proof.
  revert Σ τ e η.
  induction gas as [|gas IH]; intros Σ τ e η Hfresh.
  - cbn [denot_ty_lvar_gas formula_fv].
    rewrite formula_open_env_and.
    cbn [formula_fv].
    rewrite formula_fv_open_env_FDenotObligationIn.
    rewrite formula_open_env_true.
    reflexivity.
  - change (formula_fv
      (formula_open_env η (denot_ty_lvar_gas (S gas) Σ τ e))) with
      (formula_fv (formula_open_env η
        (FAnd (FDenotObligationIn Σ τ e)
          (match τ with
          | CTOver b φ =>
              FExprContIn Σ (TBase b) e (fun _ =>
                FFibVars (qual_vars φ ∖ {[LVBound 0]})
                  (FOver (FTypeQualifier φ)))
          | CTUnder b φ =>
              FExprContIn Σ (TBase b) e (fun _ =>
                FFibVars (qual_vars φ ∖ {[LVBound 0]})
                  (FUnder (FTypeQualifier φ)))
          | CTInter τ1 τ2 =>
              FAnd
                (denot_ty_lvar_gas gas Σ τ1 e)
                (denot_ty_lvar_gas gas Σ τ2 e)
          | CTUnion τ1 τ2 =>
              FOr
                (denot_ty_lvar_gas gas Σ τ1 e)
                (denot_ty_lvar_gas gas Σ τ2 e)
          | CTSum τ1 τ2 =>
              FPlus
                (denot_ty_lvar_gas gas Σ τ1 e)
                (denot_ty_lvar_gas gas Σ τ2 e)
          | CTArrow τx τ =>
              FForallTypedBind Σ (erase_ty τx) (fun Σx =>
                FImpl
                  (denot_ty_lvar_gas gas Σx
                    (↑[0] τx) (tret (vbvar 0)))
                  (denot_ty_lvar_gas gas Σx τ
                    (tapp_tm (↑[0] e) (vbvar 0))))
          | CTWand τx τ =>
              FForallTypedBind Σ (erase_ty τx) (fun Σx =>
                FWand
                  (denot_ty_lvar_gas gas Σx
                    (↑[0] τx) (tret (vbvar 0)))
                  (denot_ty_lvar_gas gas Σx τ
                    (tapp_tm (↑[0] e) (vbvar 0))))
          end)))).
    set (R := denot_ty_lvar_gas (S gas)
      (lty_env_open_lvars η Σ) (open_cty_env η τ) (open_tm_env η e)).
    change (formula_fv (formula_open_env η
      (FAnd (FDenotObligationIn Σ τ e)
        (match τ with
        | CTOver b φ =>
            FExprContIn Σ (TBase b) e (fun _ =>
              FFibVars (qual_vars φ ∖ {[LVBound 0]})
                (FOver (FTypeQualifier φ)))
        | CTUnder b φ =>
            FExprContIn Σ (TBase b) e (fun _ =>
              FFibVars (qual_vars φ ∖ {[LVBound 0]})
                (FUnder (FTypeQualifier φ)))
        | CTInter τ1 τ2 =>
            FAnd
              (denot_ty_lvar_gas gas Σ τ1 e)
              (denot_ty_lvar_gas gas Σ τ2 e)
        | CTUnion τ1 τ2 =>
            FOr
              (denot_ty_lvar_gas gas Σ τ1 e)
              (denot_ty_lvar_gas gas Σ τ2 e)
        | CTSum τ1 τ2 =>
            FPlus
              (denot_ty_lvar_gas gas Σ τ1 e)
              (denot_ty_lvar_gas gas Σ τ2 e)
        | CTArrow τx τ =>
            FForallTypedBind Σ (erase_ty τx) (fun Σx =>
              FImpl
                (denot_ty_lvar_gas gas Σx
                  (↑[0] τx) (tret (vbvar 0)))
                (denot_ty_lvar_gas gas Σx τ
                  (tapp_tm (↑[0] e) (vbvar 0))))
        | CTWand τx τ =>
            FForallTypedBind Σ (erase_ty τx) (fun Σx =>
              FWand
                (denot_ty_lvar_gas gas Σx
                  (↑[0] τx) (tret (vbvar 0)))
                (denot_ty_lvar_gas gas Σx τ
                  (tapp_tm (↑[0] e) (vbvar 0))))
        end))) = formula_fv R).
    rewrite formula_open_env_and.
    cbn [formula_fv].
    rewrite formula_fv_open_env_FDenotObligationIn.
    destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τ|τx τ].
    + rewrite (formula_fv_open_env_FExprContIn η Σ (TBase b) e
        (fun _ => FFibVars (qual_vars φ ∖ {[LVBound 0]})
          (FOver (FTypeQualifier φ)))
        (fun _ => FFibVars
          (qual_vars (qual_with_vars
            (lvars_open_env (open_env_lift η) (qual_vars φ))) ∖
            {[LVBound 0]})
          (FOver (FTypeQualifier
            (qual_with_vars
              (lvars_open_env (open_env_lift η) (qual_vars φ))))))).
      2:{
        rewrite formula_fv_open_env_FResultQualifier_over_body_vars.
        rewrite formula_fv_FResultQualifier_over_body_vars.
        reflexivity.
      }
      subst R.
      rewrite (formula_fv_denot_ty_lvar_gas_cty_vars_equiv (S gas)
        (lty_env_open_lvars η Σ)
        (open_cty_env η (CTOver b φ))
        (CTOver b (qual_with_vars
          (lvars_open_env (open_env_lift η) (qual_vars φ))))
        (open_tm_env η e)).
      2:{ apply open_cty_env_over_vars_equiv. }
      cbn [denot_ty_lvar_gas].
      reflexivity.
    + rewrite (formula_fv_open_env_FExprContIn η Σ (TBase b) e
        (fun _ => FFibVars (qual_vars φ ∖ {[LVBound 0]})
          (FUnder (FTypeQualifier φ)))
        (fun _ => FFibVars
          (qual_vars (qual_with_vars
            (lvars_open_env (open_env_lift η) (qual_vars φ))) ∖
            {[LVBound 0]})
          (FUnder (FTypeQualifier
            (qual_with_vars
              (lvars_open_env (open_env_lift η) (qual_vars φ))))))).
      2:{
        rewrite formula_fv_open_env_FResultQualifier_under_body_vars.
        rewrite formula_fv_FResultQualifier_under_body_vars.
        reflexivity.
      }
      subst R.
      rewrite (formula_fv_denot_ty_lvar_gas_cty_vars_equiv (S gas)
        (lty_env_open_lvars η Σ)
        (open_cty_env η (CTUnder b φ))
        (CTUnder b (qual_with_vars
          (lvars_open_env (open_env_lift η) (qual_vars φ))))
        (open_tm_env η e)).
      2:{ apply open_cty_env_under_vars_equiv. }
      cbn [denot_ty_lvar_gas].
      reflexivity.
    + rewrite formula_open_env_and. cbn [formula_fv].
      rewrite (IH Σ τ1 e η Hfresh).
      rewrite (IH Σ τ2 e η Hfresh).
      subst R.
      rewrite (formula_fv_denot_ty_lvar_gas_cty_vars_equiv (S gas)
        (lty_env_open_lvars η Σ) (open_cty_env η (CTInter τ1 τ2))
        (CTInter (open_cty_env η τ1) (open_cty_env η τ2))
        (open_tm_env η e)).
      2:{ apply open_cty_env_inter_vars_equiv. }
      cbn [denot_ty_lvar_gas formula_fv].
      set_solver.
    + rewrite formula_open_env_or. cbn [formula_fv].
      rewrite (IH Σ τ1 e η Hfresh).
      rewrite (IH Σ τ2 e η Hfresh).
      subst R.
      rewrite (formula_fv_denot_ty_lvar_gas_cty_vars_equiv (S gas)
        (lty_env_open_lvars η Σ) (open_cty_env η (CTUnion τ1 τ2))
        (CTUnion (open_cty_env η τ1) (open_cty_env η τ2))
        (open_tm_env η e)).
      2:{ apply open_cty_env_union_vars_equiv. }
      cbn [denot_ty_lvar_gas formula_fv].
      set_solver.
    + rewrite formula_open_env_plus. cbn [formula_fv].
      rewrite (IH Σ τ1 e η Hfresh).
      rewrite (IH Σ τ2 e η Hfresh).
      subst R.
      rewrite (formula_fv_denot_ty_lvar_gas_cty_vars_equiv (S gas)
        (lty_env_open_lvars η Σ) (open_cty_env η (CTSum τ1 τ2))
        (CTSum (open_cty_env η τ1) (open_cty_env η τ2))
        (open_tm_env η e)).
      2:{ apply open_cty_env_sum_vars_equiv. }
      cbn [denot_ty_lvar_gas formula_fv].
      set_solver.
    + rewrite (formula_fv_open_env_FForallTypedBind η Σ (erase_ty τx)
        (fun Σx => FImpl
          (denot_ty_lvar_gas gas Σx (↑[0] τx) (tret (vbvar 0)))
          (denot_ty_lvar_gas gas Σx τ
            (tapp_tm (↑[0] e) (vbvar 0))))
        (fun Σx => FImpl
          (denot_ty_lvar_gas gas Σx
            (↑[0] (open_cty_env η τx)) (tret (vbvar 0)))
          (denot_ty_lvar_gas gas Σx (open_cty_env (open_env_lift η) τ)
            (tapp_tm (↑[0] (open_tm_env η e)) (vbvar 0))))).
      2:{
        rewrite formula_open_env_impl.
        rewrite !formula_fv_FImpl.
        assert (Hargfv :
          formula_fv
            (denot_ty_lvar_gas gas
              (typed_lty_env_bind (lty_env_open_lvars η Σ) (erase_ty τx))
              (open_cty_env (open_env_lift η) (↑[0] τx))
              (tret (vbvar 0))) =
          formula_fv
            (denot_ty_lvar_gas gas
              (typed_lty_env_bind (lty_env_open_lvars η Σ) (erase_ty τx))
              (↑[0] (open_cty_env η τx))
              (tret (vbvar 0)))).
        {
          apply formula_fv_denot_ty_lvar_gas_cty_vars_equiv.
          apply open_cty_env_lift_shift0_vars_equiv.
        }
        rewrite <- Hargfv.
        rewrite (IH (typed_lty_env_bind Σ (erase_ty τx)) (↑[0] τx)
          (tret (vbvar 0)) (open_env_lift η)).
        2:{ apply open_env_fresh_for_lvars_lift_typed_bind. exact Hfresh. }
        rewrite (IH (typed_lty_env_bind Σ (erase_ty τx)) τ
          (tapp_tm (↑[0] e) (vbvar 0)) (open_env_lift η)).
        2:{ apply open_env_fresh_for_lvars_lift_typed_bind. exact Hfresh. }
        rewrite typed_lty_env_bind_open_env_lift by exact Hfresh.
        rewrite open_tm_env_lift_tapp_shift_bvar0.
        rewrite (formula_fv_denot_ty_lvar_gas_tm_irrelevant gas
          (typed_lty_env_bind (lty_env_open_lvars η Σ) (erase_ty τx))
          (open_cty_env (open_env_lift η) (↑[0] τx))
          (open_tm_env (open_env_lift η) (tret (vbvar 0)))
          (tret (vbvar 0))).
        reflexivity.
      }
      subst R.
      rewrite (formula_fv_denot_ty_lvar_gas_cty_vars_equiv (S gas)
        (lty_env_open_lvars η Σ)
        (open_cty_env η (CTArrow τx τ))
        (CTArrow (open_cty_env η τx) (open_cty_env (open_env_lift η) τ))
        (open_tm_env η e)).
      2:{ apply open_cty_env_arrow_vars_equiv. }
      cbn [denot_ty_lvar_gas].
      rewrite <- (open_cty_env_preserves_erasure η τx).
      reflexivity.
    + rewrite (formula_fv_open_env_FForallTypedBind η Σ (erase_ty τx)
        (fun Σx => FWand
          (denot_ty_lvar_gas gas Σx (↑[0] τx) (tret (vbvar 0)))
          (denot_ty_lvar_gas gas Σx τ
            (tapp_tm (↑[0] e) (vbvar 0))))
        (fun Σx => FWand
          (denot_ty_lvar_gas gas Σx
            (↑[0] (open_cty_env η τx)) (tret (vbvar 0)))
          (denot_ty_lvar_gas gas Σx (open_cty_env (open_env_lift η) τ)
            (tapp_tm (↑[0] (open_tm_env η e)) (vbvar 0))))).
      2:{
        rewrite formula_open_env_wand.
        rewrite !formula_fv_FWand.
        assert (Hargfv :
          formula_fv
            (denot_ty_lvar_gas gas
              (typed_lty_env_bind (lty_env_open_lvars η Σ) (erase_ty τx))
              (open_cty_env (open_env_lift η) (↑[0] τx))
              (tret (vbvar 0))) =
          formula_fv
            (denot_ty_lvar_gas gas
              (typed_lty_env_bind (lty_env_open_lvars η Σ) (erase_ty τx))
              (↑[0] (open_cty_env η τx))
              (tret (vbvar 0)))).
        {
          apply formula_fv_denot_ty_lvar_gas_cty_vars_equiv.
          apply open_cty_env_lift_shift0_vars_equiv.
        }
        rewrite <- Hargfv.
        rewrite (IH (typed_lty_env_bind Σ (erase_ty τx)) (↑[0] τx)
          (tret (vbvar 0)) (open_env_lift η)).
        2:{ apply open_env_fresh_for_lvars_lift_typed_bind. exact Hfresh. }
        rewrite (IH (typed_lty_env_bind Σ (erase_ty τx)) τ
          (tapp_tm (↑[0] e) (vbvar 0)) (open_env_lift η)).
        2:{ apply open_env_fresh_for_lvars_lift_typed_bind. exact Hfresh. }
        rewrite typed_lty_env_bind_open_env_lift by exact Hfresh.
        rewrite open_tm_env_lift_tapp_shift_bvar0.
        rewrite (formula_fv_denot_ty_lvar_gas_tm_irrelevant gas
          (typed_lty_env_bind (lty_env_open_lvars η Σ) (erase_ty τx))
          (open_cty_env (open_env_lift η) (↑[0] τx))
          (open_tm_env (open_env_lift η) (tret (vbvar 0)))
          (tret (vbvar 0))).
        reflexivity.
      }
      subst R.
      rewrite (formula_fv_denot_ty_lvar_gas_cty_vars_equiv (S gas)
        (lty_env_open_lvars η Σ)
        (open_cty_env η (CTWand τx τ))
        (CTWand (open_cty_env η τx) (open_cty_env (open_env_lift η) τ))
        (open_tm_env η e)).
      2:{ apply open_cty_env_wand_vars_equiv. }
      cbn [denot_ty_lvar_gas].
      rewrite <- (open_cty_env_preserves_erasure η τx).
      reflexivity.
Qed.

Lemma formula_store_equiv_open_env_denot_ty_lvar_gas η gas Σ τ e :
  open_env_fresh_for_lvars η (dom Σ) →
  formula_store_equiv
    (formula_open_env η (denot_ty_lvar_gas gas Σ τ e))
    (denot_ty_lvar_gas gas
      (lty_env_open_lvars η Σ)
      (open_cty_env η τ)
      (open_tm_env η e)).
Proof.
  (* Store-equivalence version of the general mopen theorem.  This is the
     theorem that should drive nested [FForallTypedBind] proof obligations.
     The structural proof needs a body-level FV/store lemma rather than using
     the whole [denot_ty_lvar_gas] FV theorem as if the outer [FAnd] could be
     projected automatically. *)
Admitted.

Lemma formula_store_equiv_open_denot_ty_lvar_gas_arrow_body
    k x gas Σ τx τ e :
  (∀ k x Σ τ e,
    LVFree x ∉ dom Σ →
    formula_store_equiv
      (formula_open k x (denot_ty_lvar_gas gas Σ τ e))
      (denot_ty_lvar_gas gas ({k ~> x} Σ)
        ({k ~> x} τ) ({k ~> x} e))) →
  (∀ Σ τ1 τ2 e,
    τ1 = τ2 →
    formula_store_equiv
      (denot_ty_lvar_gas gas Σ τ1 e)
      (denot_ty_lvar_gas gas Σ τ2 e)) →
  LVFree x ∉ dom Σ →
  formula_store_equiv
    (formula_open k x
      (FForallTypedBind Σ (erase_ty τx) (fun Σx =>
        FImpl
          (denot_ty_lvar_gas gas Σx (↑[0] τx) (tret (vbvar 0)))
          (denot_ty_lvar_gas gas Σx τ
            (tapp_tm (↑[0] e) (vbvar 0))))))
    (FForallTypedBind ({k ~> x} Σ) (erase_ty ({k ~> x} τx))
      (fun Σx =>
        FImpl
          (denot_ty_lvar_gas gas Σx (↑[0] ({k ~> x} τx))
            (tret (vbvar 0)))
          (denot_ty_lvar_gas gas Σx ({S k ~> x} τ)
            (tapp_tm (↑[0] ({k ~> x} e)) (vbvar 0))))).
Proof.
  (* Needs the general open-env/mopen denotation fv/equiv theorem.  A fixed
     open2 helper is not closed under nested [FForallTypedBind], because each
     recursive binder adds another fresh opening. *)
Admitted.

Lemma formula_store_equiv_open_denot_ty_lvar_gas_wand_body
    k x gas Σ τx τ e :
  (∀ k x Σ τ e,
    LVFree x ∉ dom Σ →
    formula_store_equiv
      (formula_open k x (denot_ty_lvar_gas gas Σ τ e))
      (denot_ty_lvar_gas gas ({k ~> x} Σ)
        ({k ~> x} τ) ({k ~> x} e))) →
  (∀ Σ τ1 τ2 e,
    τ1 = τ2 →
    formula_store_equiv
      (denot_ty_lvar_gas gas Σ τ1 e)
      (denot_ty_lvar_gas gas Σ τ2 e)) →
  LVFree x ∉ dom Σ →
  formula_store_equiv
    (formula_open k x
      (FForallTypedBind Σ (erase_ty τx) (fun Σx =>
        FWand
          (denot_ty_lvar_gas gas Σx (↑[0] τx) (tret (vbvar 0)))
          (denot_ty_lvar_gas gas Σx τ
            (tapp_tm (↑[0] e) (vbvar 0))))))
    (FForallTypedBind ({k ~> x} Σ) (erase_ty ({k ~> x} τx))
      (fun Σx =>
        FWand
          (denot_ty_lvar_gas gas Σx (↑[0] ({k ~> x} τx))
            (tret (vbvar 0)))
          (denot_ty_lvar_gas gas Σx ({S k ~> x} τ)
            (tapp_tm (↑[0] ({k ~> x} e)) (vbvar 0))))).
Proof.
  (* Same open-env/mopen gap as the arrow helper. *)
Admitted.

Lemma formula_store_equiv_open_denot_ty_lvar_gas k x gas Σ τ e :
  LVFree x ∉ dom Σ →
  formula_store_equiv
    (formula_open k x (denot_ty_lvar_gas gas Σ τ e))
    (denot_ty_lvar_gas gas ({k ~> x} Σ) ({k ~> x} τ) ({k ~> x} e)).
Proof.
  revert k x Σ τ e.
  induction gas as [|gas IH]; intros k x Σ τ e Hfresh;
    cbn [denot_ty_lvar_gas formula_open].
  - eapply formula_store_equiv_and.
    + apply formula_fv_open_FDenotObligationIn.
    + reflexivity.
    + apply formula_store_equiv_open_FDenotObligationIn.
    + apply formula_store_equiv_refl.
  - destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τ|τx τ];
      cbn [cty_open open_one open_cty_atom_inst denot_ty_lvar_gas
        formula_open].
    + eapply formula_store_equiv_and.
      * apply formula_fv_open_FDenotObligationIn.
      * eapply formula_fv_open_FExprContIn.
        -- exact Hfresh.
        -- apply formula_fv_open_FResultQualifier_over_body.
      * apply formula_store_equiv_open_FDenotObligationIn.
      * eapply formula_store_equiv_open_FExprContIn.
        -- exact Hfresh.
        -- apply formula_fv_open_FResultQualifier_over_body.
        -- intros y Hy. apply formula_fv_open2_FResultQualifier_over_body.
        -- intros y Hy. apply formula_store_equiv_open2_FResultQualifier_over_body.
    + eapply formula_store_equiv_and.
      * apply formula_fv_open_FDenotObligationIn.
      * eapply formula_fv_open_FExprContIn.
        -- exact Hfresh.
        -- apply formula_fv_open_FResultQualifier_under_body.
      * apply formula_store_equiv_open_FDenotObligationIn.
      * eapply formula_store_equiv_open_FExprContIn.
        -- exact Hfresh.
        -- apply formula_fv_open_FResultQualifier_under_body.
        -- intros y Hy. apply formula_fv_open2_FResultQualifier_under_body.
        -- intros y Hy. apply formula_store_equiv_open2_FResultQualifier_under_body.
    + eapply formula_store_equiv_and.
      * apply formula_fv_open_FDenotObligationIn.
      * cbn [formula_fv].
        rewrite (formula_fv_open_denot_ty_lvar_gas k x gas Σ τ1 e Hfresh).
        rewrite (formula_fv_open_denot_ty_lvar_gas k x gas Σ τ2 e Hfresh).
        reflexivity.
      * apply formula_store_equiv_open_FDenotObligationIn.
      * eapply formula_store_equiv_and.
        -- apply formula_fv_open_denot_ty_lvar_gas. exact Hfresh.
        -- apply formula_fv_open_denot_ty_lvar_gas. exact Hfresh.
        -- apply IH. exact Hfresh.
        -- apply IH. exact Hfresh.
    + eapply formula_store_equiv_and.
      * apply formula_fv_open_FDenotObligationIn.
      * cbn [formula_fv].
        rewrite (formula_fv_open_denot_ty_lvar_gas k x gas Σ τ1 e Hfresh).
        rewrite (formula_fv_open_denot_ty_lvar_gas k x gas Σ τ2 e Hfresh).
        reflexivity.
      * apply formula_store_equiv_open_FDenotObligationIn.
      * eapply formula_store_equiv_or.
        -- apply formula_fv_open_denot_ty_lvar_gas. exact Hfresh.
        -- apply formula_fv_open_denot_ty_lvar_gas. exact Hfresh.
        -- apply IH. exact Hfresh.
        -- apply IH. exact Hfresh.
    + eapply formula_store_equiv_and.
      * apply formula_fv_open_FDenotObligationIn.
      * cbn [formula_fv].
        rewrite (formula_fv_open_denot_ty_lvar_gas k x gas Σ τ1 e Hfresh).
        rewrite (formula_fv_open_denot_ty_lvar_gas k x gas Σ τ2 e Hfresh).
        reflexivity.
      * apply formula_store_equiv_open_FDenotObligationIn.
      * eapply formula_store_equiv_plus.
        -- apply formula_fv_open_denot_ty_lvar_gas. exact Hfresh.
        -- apply formula_fv_open_denot_ty_lvar_gas. exact Hfresh.
        -- apply IH. exact Hfresh.
        -- apply IH. exact Hfresh.
    + eapply formula_store_equiv_and.
      * apply formula_fv_open_FDenotObligationIn.
      * cbn [formula_fv].
        rewrite cty_open_preserves_erasure.
        rewrite (formula_fv_open_FForallTypedBind k x Σ (erase_ty τx)
          (fun Σx => FImpl
            (denot_ty_lvar_gas gas Σx (↑[0] τx) (tret (vbvar 0)))
            (denot_ty_lvar_gas gas Σx τ
              (tapp_tm (↑[0] e) (vbvar 0))))
          (fun Σx => FImpl
            (denot_ty_lvar_gas gas Σx (↑[0] ({k ~> x} τx))
              (tret (vbvar 0)))
            (denot_ty_lvar_gas gas Σx ({S k ~> x} τ)
              (tapp_tm (↑[0] ({k ~> x} e)) (vbvar 0))))).
        2:{ exact Hfresh. }
        2:{
          cbn [formula_open formula_fv].
          rewrite (formula_fv_open_denot_ty_lvar_gas (S k) x gas
            (typed_lty_env_bind Σ (erase_ty τx)) (↑[0] τx)
            (tret (vbvar 0))).
          2:{ apply typed_lty_env_bind_free_notin. exact Hfresh. }
          rewrite typed_lty_env_bind_open_under by exact Hfresh.
          change ({S k ~> x} (↑[0] τx)) with
            (cty_open (S k) x (cty_shift 0 τx)).
          rewrite cty_open_shift_under_equiv.
          rewrite (formula_fv_open_denot_ty_lvar_gas (S k) x gas
            (typed_lty_env_bind Σ (erase_ty τx)) τ
            (tapp_tm (↑[0] e) (vbvar 0))).
          2:{ apply typed_lty_env_bind_free_notin. exact Hfresh. }
          rewrite typed_lty_env_bind_open_under by exact Hfresh.
          rewrite open_tapp_tm_shift_bvar0_under_lvar.
          reflexivity.
        }
        reflexivity.
      * apply formula_store_equiv_open_FDenotObligationIn.
      * apply formula_store_equiv_open_denot_ty_lvar_gas_arrow_body.
        -- intros k' x' Σ' τ' e' Hfresh'.
           apply IH. exact Hfresh'.
        -- intros Σ' τ1 τ2 e' ->. apply formula_store_equiv_refl.
        -- exact Hfresh.
    + eapply formula_store_equiv_and.
      * apply formula_fv_open_FDenotObligationIn.
      * cbn [formula_fv].
        rewrite cty_open_preserves_erasure.
        rewrite (formula_fv_open_FForallTypedBind k x Σ (erase_ty τx)
          (fun Σx => FWand
            (denot_ty_lvar_gas gas Σx (↑[0] τx) (tret (vbvar 0)))
            (denot_ty_lvar_gas gas Σx τ
              (tapp_tm (↑[0] e) (vbvar 0))))
          (fun Σx => FWand
            (denot_ty_lvar_gas gas Σx (↑[0] ({k ~> x} τx))
              (tret (vbvar 0)))
            (denot_ty_lvar_gas gas Σx ({S k ~> x} τ)
              (tapp_tm (↑[0] ({k ~> x} e)) (vbvar 0))))).
        2:{ exact Hfresh. }
        2:{
          cbn [formula_open formula_fv].
          rewrite (formula_fv_open_denot_ty_lvar_gas (S k) x gas
            (typed_lty_env_bind Σ (erase_ty τx)) (↑[0] τx)
            (tret (vbvar 0))).
          2:{ apply typed_lty_env_bind_free_notin. exact Hfresh. }
          rewrite typed_lty_env_bind_open_under by exact Hfresh.
          change ({S k ~> x} (↑[0] τx)) with
            (cty_open (S k) x (cty_shift 0 τx)).
          rewrite cty_open_shift_under_equiv.
          rewrite (formula_fv_open_denot_ty_lvar_gas (S k) x gas
            (typed_lty_env_bind Σ (erase_ty τx)) τ
            (tapp_tm (↑[0] e) (vbvar 0))).
          2:{ apply typed_lty_env_bind_free_notin. exact Hfresh. }
          rewrite typed_lty_env_bind_open_under by exact Hfresh.
          rewrite open_tapp_tm_shift_bvar0_under_lvar.
          reflexivity.
        }
        reflexivity.
      * apply formula_store_equiv_open_FDenotObligationIn.
      * apply formula_store_equiv_open_denot_ty_lvar_gas_wand_body.
        -- intros k' x' Σ' τ' e' Hfresh'.
           apply IH. exact Hfresh'.
        -- intros Σ' τ1 τ2 e' ->. apply formula_store_equiv_refl.
        -- exact Hfresh.
Qed.

Lemma res_models_open_denot_ty_lvar_gas_fwd
    k y gas Σ τ e (m : WfWorld) :
  LVFree y ∉ dom Σ ->
  m ⊨ formula_open k y (denot_ty_lvar_gas gas Σ τ e) ->
  m ⊨ denot_ty_lvar_gas gas ({k ~> y} Σ) ({k ~> y} τ) ({k ~> y} e).
Proof.
  intros HΣ Hm.
  pose proof (formula_store_equiv_open_denot_ty_lvar_gas
    k y gas Σ τ e HΣ) as Heq.
  exact ((proj1 (res_models_of_formula_store_equiv _ _ m Heq)) Hm).
Qed.

Lemma res_models_open_denot_ty_lvar_gas_rev
    k y gas Σ τ e (m : WfWorld) :
  LVFree y ∉ dom Σ ->
  m ⊨ denot_ty_lvar_gas gas ({k ~> y} Σ) ({k ~> y} τ) ({k ~> y} e) ->
  m ⊨ formula_open k y (denot_ty_lvar_gas gas Σ τ e).
Proof.
  intros HΣ Hm.
  pose proof (formula_store_equiv_open_denot_ty_lvar_gas
    k y gas Σ τ e HΣ) as Heq.
  exact ((proj2 (res_models_of_formula_store_equiv _ _ m Heq)) Hm).
Qed.

Lemma denot_ty_lvar_gas_open_shift0_lc_cty_store_equiv
    gas Σ (τ : choice_ty) e y :
  lc_choice_ty τ ->
  cty_parametric τ ->
  formula_store_equiv
    (denot_ty_lvar_gas gas Σ ({0 ~> y} (↑[0] τ)) e)
    (denot_ty_lvar_gas gas Σ τ e).
Proof.
  intros Hlc Hparam.
  rewrite (cty_open_shift0_lc_parametric y τ Hlc Hparam).
  apply formula_store_equiv_refl.
Qed.

Lemma denot_ty_lvar_gas_opened_arrow_arg_to_atom_env
    gas (Δ : gmap atom ty) τx y (m : WfWorld) :
  y ∉ dom Δ ->
  basic_choice_ty (dom Δ) τx ->
  cty_parametric τx ->
  m ⊨ formula_open 0 y
    (denot_ty_lvar_gas gas
      (typed_lty_env_bind (atom_env_to_lty_env Δ) (erase_ty τx))
      (↑[0] τx) (tret (vbvar 0))) ->
  m ⊨ denot_ty_lvar_gas gas
    (atom_env_to_lty_env (<[y := erase_ty τx]> Δ))
    τx (tret (vfvar y)).
Proof.
  intros Hy Hbasic Hparam Hm.
  eapply res_models_open_denot_ty_lvar_gas_fwd in Hm.
  2:{
    intros Hfree.
    apply Hy.
    rewrite <- atom_env_to_lty_env_atom_dom.
    rewrite <- typed_lty_env_bind_atom_dom
      with (T := erase_ty τx) (Σ := atom_env_to_lty_env Δ).
    unfold lty_env_atom_dom.
    apply lvars_fv_elem. exact Hfree.
  }
  rewrite lty_env_open_typed_bind_atom_env in Hm by exact Hy.
  rewrite open_tret_bvar0 in Hm.
  rewrite (cty_open_shift0_lc_parametric y τx) in Hm.
  - exact Hm.
  - eapply basic_choice_ty_lc. exact Hbasic.
  - exact Hparam.
Qed.

Lemma denot_ty_lvar_gas_atom_env_to_opened_arrow_arg
    gas (Δ : gmap atom ty) τx y (m : WfWorld) :
  y ∉ dom Δ ->
  basic_choice_ty (dom Δ) τx ->
  cty_parametric τx ->
  m ⊨ denot_ty_lvar_gas gas
    (atom_env_to_lty_env (<[y := erase_ty τx]> Δ))
    τx (tret (vfvar y)) ->
  m ⊨ formula_open 0 y
    (denot_ty_lvar_gas gas
      (typed_lty_env_bind (atom_env_to_lty_env Δ) (erase_ty τx))
      (↑[0] τx) (tret (vbvar 0))).
Proof.
  intros Hy Hbasic Hparam Hm.
  eapply res_models_open_denot_ty_lvar_gas_rev.
  2:{
    rewrite lty_env_open_typed_bind_atom_env by exact Hy.
    rewrite open_tret_bvar0.
    rewrite (cty_open_shift0_lc_parametric y τx).
    - exact Hm.
    - eapply basic_choice_ty_lc. exact Hbasic.
    - exact Hparam.
  }
  intros Hfree.
  apply Hy.
  rewrite <- atom_env_to_lty_env_atom_dom.
  rewrite <- typed_lty_env_bind_atom_dom
    with (T := erase_ty τx) (Σ := atom_env_to_lty_env Δ).
  unfold lty_env_atom_dom.
  apply lvars_fv_elem. exact Hfree.
Qed.

Lemma denot_ty_lvar_gas_opened_arrow_conseq_to_atom_env
    gas (Δ : gmap atom ty) τx τ e y (m : WfWorld) :
  y ∉ dom Δ ->
  lc_tm e ->
  m ⊨ formula_open 0 y
    (denot_ty_lvar_gas gas
      (typed_lty_env_bind (atom_env_to_lty_env Δ) (erase_ty τx))
      τ (tapp_tm (↑[0] e) (vbvar 0))) ->
  m ⊨ denot_ty_lvar_gas gas
    (atom_env_to_lty_env (<[y := erase_ty τx]> Δ))
    ({0 ~> y} τ) (tapp_tm e (vfvar y)).
Proof.
  intros Hy Hlc Hm.
  eapply res_models_open_denot_ty_lvar_gas_fwd in Hm.
  2:{
    intros Hfree.
    apply Hy.
    rewrite <- atom_env_to_lty_env_atom_dom.
    rewrite <- typed_lty_env_bind_atom_dom
      with (T := erase_ty τx) (Σ := atom_env_to_lty_env Δ).
    unfold lty_env_atom_dom.
    apply lvars_fv_elem. exact Hfree.
  }
  rewrite lty_env_open_typed_bind_atom_env in Hm by exact Hy.
  rewrite open_tapp_shift_bvar0 in Hm by exact Hlc.
  exact Hm.
Qed.

Lemma denot_ty_lvar_gas_atom_env_to_opened_arrow_conseq
    gas (Δ : gmap atom ty) τx τ e y (m : WfWorld) :
  y ∉ dom Δ ->
  lc_tm e ->
  m ⊨ denot_ty_lvar_gas gas
    (atom_env_to_lty_env (<[y := erase_ty τx]> Δ))
    ({0 ~> y} τ) (tapp_tm e (vfvar y)) ->
  m ⊨ formula_open 0 y
    (denot_ty_lvar_gas gas
      (typed_lty_env_bind (atom_env_to_lty_env Δ) (erase_ty τx))
      τ (tapp_tm (↑[0] e) (vbvar 0))).
Proof.
  intros Hy Hlc Hm.
  eapply res_models_open_denot_ty_lvar_gas_rev.
  2:{
    rewrite lty_env_open_typed_bind_atom_env by exact Hy.
    rewrite open_tapp_shift_bvar0 by exact Hlc.
    exact Hm.
  }
  intros Hfree.
  apply Hy.
  rewrite <- atom_env_to_lty_env_atom_dom.
  rewrite <- typed_lty_env_bind_atom_dom
    with (T := erase_ty τx) (Σ := atom_env_to_lty_env Δ).
  unfold lty_env_atom_dom.
  apply lvars_fv_elem. exact Hfree.
Qed.

Lemma denot_ty_lvar_gas_fv_subset gas Σ τ e :
  formula_fv (denot_ty_lvar_gas gas Σ τ e) ⊆
    lvars_fv (dom Σ) ∪ fv_cty τ.
Proof.
  revert Σ τ e.
  induction gas as [|gas IH]; intros Σ τ e.
  - cbn [denot_ty_lvar_gas formula_fv].
    unfold FDenotObligationIn.
    rewrite formula_fv_FStoreResourceAtom_lvars.
    set_solver.
  - destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τ1 τ2|τ1 τ2];
      cbn [denot_ty_lvar_gas formula_fv fv_cty].
    + unfold FDenotObligationIn.
      rewrite formula_fv_FStoreResourceAtom_lvars.
      pose proof (FExprContIn_lvar_formula_fv_subset
        Σ (TBase b) e (lvars_fv (dom Σ) ∪ qual_dom φ)
        (fun _ => FFibVars (qual_vars φ ∖ {[LVBound 0]})
          (FOver (FTypeQualifier φ)))) as Hcont.
      assert (HQ : formula_fv
        (FFibVars (qual_vars φ ∖ {[LVBound 0]})
          (FOver (FTypeQualifier φ))) ⊆
        lvars_fv (dom Σ) ∪ qual_dom φ).
      {
        cbn [formula_fv].
        rewrite formula_fv_FTypeQualifier.
        destruct φ as [D p]; cbn [qual_dom qual_vars].
        pose proof (lvars_fv_difference_subset
          D ({[LVBound 0]} : lvset)).
        set_solver.
      }
      specialize (Hcont ltac:(set_solver) HQ).
      set_solver.
    + unfold FDenotObligationIn.
      rewrite formula_fv_FStoreResourceAtom_lvars.
      pose proof (FExprContIn_lvar_formula_fv_subset
        Σ (TBase b) e (lvars_fv (dom Σ) ∪ qual_dom φ)
        (fun _ => FFibVars (qual_vars φ ∖ {[LVBound 0]})
          (FUnder (FTypeQualifier φ)))) as Hcont.
      assert (HQ : formula_fv
        (FFibVars (qual_vars φ ∖ {[LVBound 0]})
          (FUnder (FTypeQualifier φ))) ⊆
        lvars_fv (dom Σ) ∪ qual_dom φ).
      {
        cbn [formula_fv].
        rewrite formula_fv_FTypeQualifier.
        destruct φ as [D p]; cbn [qual_dom qual_vars].
        pose proof (lvars_fv_difference_subset
          D ({[LVBound 0]} : lvset)).
        set_solver.
      }
      specialize (Hcont ltac:(set_solver) HQ).
      set_solver.
    + unfold FDenotObligationIn.
      rewrite formula_fv_FStoreResourceAtom_lvars.
      pose proof (IH Σ τ1 e).
      pose proof (IH Σ τ2 e).
      set_solver.
    + unfold FDenotObligationIn.
      rewrite formula_fv_FStoreResourceAtom_lvars.
      pose proof (IH Σ τ1 e).
      pose proof (IH Σ τ2 e).
      set_solver.
    + unfold FDenotObligationIn.
      rewrite formula_fv_FStoreResourceAtom_lvars.
      pose proof (IH Σ τ1 e).
      pose proof (IH Σ τ2 e).
      set_solver.
    + unfold FDenotObligationIn.
      rewrite formula_fv_FStoreResourceAtom_lvars.
      pose proof (FForallTypedBind_lvar_formula_fv_subset
        Σ (erase_ty τ1) (lvars_fv (dom Σ) ∪ fv_cty τ1 ∪ fv_cty τ2)
        (fun Σx => FImpl
          (denot_ty_lvar_gas gas Σx (↑[0] τ1) (tret (vbvar 0)))
          (denot_ty_lvar_gas gas Σx τ2
            (tapp_tm (↑[0] e) (vbvar 0))))) as Hforall.
      assert (HQ : formula_fv
        (FImpl
          (denot_ty_lvar_gas gas (typed_lty_env_bind Σ (erase_ty τ1))
            (↑[0] τ1) (tret (vbvar 0)))
          (denot_ty_lvar_gas gas (typed_lty_env_bind Σ (erase_ty τ1))
            τ2 (tapp_tm (↑[0] e) (vbvar 0)))) ⊆
        lvars_fv (dom Σ) ∪ fv_cty τ1 ∪ fv_cty τ2).
      {
        cbn [formula_fv].
        pose proof (IH (typed_lty_env_bind Σ (erase_ty τ1))
          (↑[0] τ1) (tret (vbvar 0))) as Harg.
        pose proof (IH (typed_lty_env_bind Σ (erase_ty τ1))
          τ2 (tapp_tm (↑[0] e) (vbvar 0))) as Hres.
        rewrite typed_lty_env_bind_lvars_fv_dom in Harg, Hres.
        change (↑[0] τ1) with (cty_shift 0 τ1) in Harg.
        rewrite cty_shift_fv in Harg.
        set_solver.
      }
      specialize (Hforall ltac:(set_solver) HQ).
      set_solver.
    + unfold FDenotObligationIn.
      rewrite formula_fv_FStoreResourceAtom_lvars.
      pose proof (FForallTypedBind_lvar_formula_fv_subset
        Σ (erase_ty τ1) (lvars_fv (dom Σ) ∪ fv_cty τ1 ∪ fv_cty τ2)
        (fun Σx => FWand
          (denot_ty_lvar_gas gas Σx (↑[0] τ1) (tret (vbvar 0)))
          (denot_ty_lvar_gas gas Σx τ2
            (tapp_tm (↑[0] e) (vbvar 0))))) as Hforall.
      assert (HQ : formula_fv
        (FWand
          (denot_ty_lvar_gas gas (typed_lty_env_bind Σ (erase_ty τ1))
            (↑[0] τ1) (tret (vbvar 0)))
          (denot_ty_lvar_gas gas (typed_lty_env_bind Σ (erase_ty τ1))
            τ2 (tapp_tm (↑[0] e) (vbvar 0)))) ⊆
        lvars_fv (dom Σ) ∪ fv_cty τ1 ∪ fv_cty τ2).
      {
        cbn [formula_fv].
        pose proof (IH (typed_lty_env_bind Σ (erase_ty τ1))
          (↑[0] τ1) (tret (vbvar 0))) as Harg.
        pose proof (IH (typed_lty_env_bind Σ (erase_ty τ1))
          τ2 (tapp_tm (↑[0] e) (vbvar 0))) as Hres.
        rewrite typed_lty_env_bind_lvars_fv_dom in Harg, Hres.
        change (↑[0] τ1) with (cty_shift 0 τ1) in Harg.
        rewrite cty_shift_fv in Harg.
        set_solver.
      }
      specialize (Hforall ltac:(set_solver) HQ).
      set_solver.
Qed.

Lemma tlet_arrow_inline_impl_fv_subset
    gas (Δ : gmap atom ty) τx τ e :
  basic_choice_ty (dom Δ) τx ->
  fv_cty τ ⊆ dom Δ ->
  formula_fv
    (FImpl
      (denot_ty_lvar_gas gas
        (typed_lty_env_bind (atom_env_to_lty_env Δ) (erase_ty τx))
        (↑[0] τx) (tret (vbvar 0)))
      (denot_ty_lvar_gas gas
        (typed_lty_env_bind (atom_env_to_lty_env Δ) (erase_ty τx))
        τ (tapp_tm (↑[0] e) (vbvar 0)))) ⊆ dom Δ.
Proof.
  intros Hbasicx Hfvτ.
  cbn [formula_fv].
  pose proof (denot_ty_lvar_gas_fv_subset gas
    (typed_lty_env_bind (atom_env_to_lty_env Δ) (erase_ty τx))
    (↑[0] τx) (tret (vbvar 0))) as Harg.
  pose proof (denot_ty_lvar_gas_fv_subset gas
    (typed_lty_env_bind (atom_env_to_lty_env Δ) (erase_ty τx))
    τ (tapp_tm (↑[0] e) (vbvar 0))) as Hres.
  rewrite typed_lty_env_bind_lvars_fv_dom in Harg, Hres.
  rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms in Harg, Hres.
  change (↑[0] τx) with (cty_shift 0 τx) in Harg.
  rewrite cty_shift_fv in Harg.
  pose proof (basic_choice_ty_fv_subset _ _ Hbasicx) as Hfvτx.
  set_solver.
Qed.

Lemma tlet_arrow_inline_forall_body_fv_subset
    gas (Δ : gmap atom ty) τx τ e :
  basic_choice_ty (dom Δ) τx ->
  fv_cty τ ⊆ dom Δ ->
  formula_fv
    (FForallTypedBody (atom_env_to_lty_env Δ) (erase_ty τx)
      (fun Σy =>
        FImpl
          (denot_ty_lvar_gas gas Σy (↑[0] τx) (tret (vbvar 0)))
          (denot_ty_lvar_gas gas Σy τ
            (tapp_tm (↑[0] e) (vbvar 0))))) ⊆ dom Δ.
Proof.
  intros Hbasicx Hfvτ.
  eapply FForallTypedBody_lvar_formula_fv_subset.
  - rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms. set_solver.
  - eapply tlet_arrow_inline_impl_fv_subset; eauto.
Qed.

Lemma denot_ty_on_fv_subset Σ τ e :
  formula_fv (denot_ty_on Σ τ e) ⊆ dom Σ ∪ fv_cty τ.
Proof.
  unfold denot_ty_on, denot_ty_lvar.
  pose proof (denot_ty_lvar_gas_fv_subset (cty_depth τ)
    (atom_env_to_lty_env Σ) τ e) as Hfv.
  rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms in Hfv.
  exact Hfv.
Qed.

Lemma denot_ty_under_fv_subset Σ τ e :
  formula_fv (denot_ty_under Σ τ e) ⊆ dom Σ ∪ fv_cty τ.
Proof.
  apply denot_ty_on_fv_subset.
Qed.

Lemma denot_ty_on_fv_subset_env Σ τ e :
  fv_cty τ ∪ fv_tm e ⊆ dom Σ →
  formula_fv (denot_ty_on Σ τ e) ⊆ dom Σ.
Proof.
  intros Hfv.
  pose proof (denot_ty_on_fv_subset Σ τ e) as Hφ.
  set_solver.
Qed.

Lemma denot_ty_on_env_fv_subset Σ τ e :
  dom Σ ⊆ formula_fv (denot_ty_on Σ τ e).
Proof.
  intros z Hz.
  destruct τ; unfold denot_ty_on, denot_ty_lvar;
    cbn [cty_depth denot_ty_lvar_gas formula_fv];
    apply elem_of_union; left; unfold FDenotObligationIn;
    rewrite formula_fv_FStoreResourceAtom_lvars;
    rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms;
    exact Hz.
Qed.

Lemma denot_ty_on_result_atom_fv Σ x τ :
  x ∈ dom Σ →
  x ∈ formula_fv (denot_ty_on Σ τ (tret (vfvar x))).
Proof.
  intros Hx.
  pose proof (denot_ty_on_env_fv_subset Σ τ (tret (vfvar x))) as Hfv.
  exact (Hfv x Hx).
Qed.

Lemma denot_ty_in_ctx_under_fv_subset Σ Γ τ e :
  formula_fv (denot_ty_in_ctx_under Σ Γ τ e) ⊆
    dom Σ ∪ ctx_stale Γ ∪ fv_cty τ.
Proof.
  unfold denot_ty_in_ctx_under.
  pose proof (denot_ty_on_fv_subset (erase_ctx_under Σ Γ) τ e) as Hfv.
  rewrite dom_union_L in Hfv.
  assert (Herase : dom (erase_ctx Γ) ⊆ ctx_stale Γ).
  {
    clear Σ τ e Hfv.
    induction Γ; simpl.
    - rewrite dom_empty_L. set_solver.
    - rewrite dom_singleton_L. set_solver.
    - rewrite dom_union_L. intros z Hz.
      apply elem_of_union in Hz as [Hz|Hz].
      + apply elem_of_union. left. exact (IHΓ1 z Hz).
      + apply elem_of_union. right. exact (IHΓ2 z Hz).
    - rewrite dom_union_L. intros z Hz.
      apply elem_of_union in Hz as [Hz|Hz].
      + apply elem_of_union. left. exact (IHΓ1 z Hz).
      + apply elem_of_union. right. exact (IHΓ2 z Hz).
    - intros z Hz. apply elem_of_union. left. exact (IHΓ1 z Hz).
  }
  set_solver.
Qed.
