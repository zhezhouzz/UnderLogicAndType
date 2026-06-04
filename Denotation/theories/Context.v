(** * Denotation.Context

    Denotation of type contexts, expressed directly with the new recursive
    context-type denotation. *)

From Denotation Require Export Notation ContextTypeDenotationOpen.
From Denotation Require Import ContextTypeDenotationSaturateCore.

Section ContextDenotation.

Definition erase_ctx_under (Σ : gmap atom ty) (Γ : ctx) : gmap atom ty :=
  Σ ∪ erase_ctx Γ.

Fixpoint denot_ctx_under (Σ : gmap atom ty) (Γ : ctx) : FormulaT :=
  FAnd (basic_world_formula (atom_env_to_lty_env (erase_ctx_under Σ Γ)))
    (match Γ with
    | CtxEmpty =>
        FTrue
    | CtxBind x τ =>
        denot_ty (<[x := erase_ty τ]> Σ) τ (tret (vfvar x))
    | CtxComma Γ1 Γ2 =>
        FAnd
          (denot_ctx_under Σ Γ1)
          (denot_ctx_under (Σ ∪ erase_ctx Γ1) Γ2)
    | CtxStar Γ1 Γ2 =>
        FStar (denot_ctx_under Σ Γ1) (denot_ctx_under Σ Γ2)
    | CtxSum Γ1 Γ2 =>
        FPlus (denot_ctx_under Σ Γ1) (denot_ctx_under Σ Γ2)
    end).

Definition denot_ctx (Γ : ctx) : FormulaT :=
  denot_ctx_under ∅ Γ.

Definition denot_ty_in_ctx (Γ : ctx) (τ : context_ty) (e : tm) : FormulaT :=
  denot_ty (erase_ctx Γ) τ e.

Definition denot_ty_in_ctx_under
    (Σ : gmap atom ty) (Γ : ctx) (τ : context_ty) (e : tm) : FormulaT :=
  denot_ty (erase_ctx Γ) τ e.

Definition ty_env_agree_on (X : aset) (Σ1 Σ2 : gmap atom ty) : Prop :=
  forall x, x ∈ X -> Σ1 !! x = Σ2 !! x.

Lemma atom_env_to_lty_env_restrict_lvars_agree_on
    (Δ1 Δ2 : gmap atom ty) (D : lvset) X :
  ty_env_agree_on X Δ1 Δ2 ->
  lvars_fv D ⊆ X ->
  lty_env_restrict_lvars (atom_env_to_lty_env Δ1) D =
  lty_env_restrict_lvars (atom_env_to_lty_env Δ2) D.
Proof.
  intros Hagree Hfv.
  apply storeA_map_eq. intros v.
  unfold lty_env_restrict_lvars.
  rewrite !storeA_restrict_lookup.
  destruct (decide (v ∈ D)) as [Hv|Hv]; [|reflexivity].
  destruct v as [k|x].
  - rewrite !atom_store_to_lvar_store_lookup_bound_none. reflexivity.
  - rewrite !atom_store_to_lvar_store_lookup_free.
    apply Hagree. apply Hfv. apply lvars_fv_elem. exact Hv.
Qed.

(** ** Context bridge lemmas for the Fundamental proof

    These statements are semantic context-denotation facts.  They live below
    [ContextTyping] so the Fundamental proof only instantiates induction
    hypotheses and calls the appropriate bridge. *)

Lemma denot_ctx_under_basic_world
    (Σ : gmap atom ty) (Γ : ctx) (m : WfWorldT) :
  m ⊨ denot_ctx_under Σ Γ ->
  m ⊨ basic_world_formula (atom_env_to_lty_env (erase_ctx_under Σ Γ)).
Proof.
  intros Hctx.
  destruct Γ; cbn [denot_ctx_under] in Hctx |- *;
    rewrite res_models_and_iff in Hctx; exact (proj1 Hctx).
Qed.

Lemma denot_ctx_under_bind_inv
    (Σ : gmap atom ty) x τ (m : WfWorldT) :
  m ⊨ denot_ctx_under Σ (CtxBind x τ) ->
  m ⊨ denot_ty (<[x := erase_ty τ]> Σ) τ (tret (vfvar x)).
Proof.
  intros Hctx.
  cbn [denot_ctx_under] in Hctx.
  rewrite res_models_and_iff in Hctx.
  exact (proj2 Hctx).
Qed.

Lemma denot_ty_in_ctx_under_restrict_agree_transport
    (Σ : gmap atom ty) Γsrc Γdst X τ e (m : WfWorldT) :
  lvars_fv (denot_relevant_lvars τ e) ⊆ X ->
  ty_env_agree_on X (erase_ctx Γsrc) (erase_ctx Γdst) ->
  res_restrict m X ⊨ denot_ty_in_ctx_under Σ Γdst τ e ->
  m ⊨ denot_ty_in_ctx_under Σ Γsrc τ e.
Proof.
  intros Hfv Hagree Hden.
  unfold denot_ty_in_ctx_under, denot_ty in Hden |- *.
  eapply res_models_kripke; [apply res_restrict_le |].
  eapply res_models_denot_ty_lvar_gas_env_agree_on
    with (X := denot_relevant_lvars τ e).
  - reflexivity.
  - apply atom_env_to_lty_env_restrict_lvars_agree_on with (X := X).
    + intros x Hx. symmetry. apply Hagree. exact Hx.
    + exact Hfv.
  - exact Hden.
Qed.

Lemma basic_world_formula_insert_from_arg_denotation
    (Σ : lty_env) (τ : context_ty) y T gas (m : WfWorldT) :
  LVFree y ∉ dom Σ ->
  m ⊨ basic_world_formula Σ ->
  m ⊨ denot_ty_lvar_gas gas (<[LVFree y := T]> Σ) τ (tret (vfvar y)) ->
  m ⊨ basic_world_formula (<[LVFree y := T]> Σ).
Proof.
  intros HyΣ Hworld Harg.
  pose proof (denot_ty_lvar_gas_guard gas
    (<[LVFree y := T]> Σ) τ (tret (vfvar y)) m Harg) as Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [_ [Hrel_world _]].
  assert (Hy_world : m ⊨ basic_world_formula
    (<[LVFree y := T]> (∅ : gmap logic_var ty))).
  {
    eapply basic_world_formula_subenv; [|exact Hrel_world].
    intros v U Hv.
    change (((<[LVFree y := T]> (∅ : gmap logic_var ty))
      : gmap logic_var ty) !! v = Some U) in Hv.
    destruct v as [k|z].
    - rewrite lookup_insert_ne in Hv by discriminate.
      rewrite lookup_empty in Hv. discriminate.
    - destruct (decide (z = y)) as [->|Hzy].
      + change ((<[LVFree y := T]> (∅ : gmap logic_var ty) : gmap logic_var ty)
            !! LVFree y = Some U) in Hv.
        rewrite lookup_insert_eq in Hv. inversion Hv. subst U.
        unfold denot_relevant_env, lty_env_restrict_lvars.
        apply storeA_restrict_lookup_some_2.
        * apply map_lookup_insert.
        * unfold denot_relevant_lvars.
          cbn [tm_lvars tm_lvars_at value_lvars value_lvars_at].
          set_solver.
      + rewrite lookup_insert_ne in Hv by congruence.
        rewrite lookup_empty in Hv. discriminate.
  }
  pose proof (basic_world_formula_union Σ
    (<[LVFree y := T]> (∅ : gmap logic_var ty) : lty_env)
    m Hworld Hy_world) as Hunion.
  change (m ⊨ basic_world_formula
    ((Σ : gmap logic_var ty) ∪
      (<[LVFree y := T]> (∅ : gmap logic_var ty)))) in Hunion.
  change (<[LVFree y := T]> (∅ : gmap logic_var ty))
    with ({[LVFree y := T]} : gmap logic_var ty) in Hunion.
  rewrite storeA_union_singleton_insert_fresh in Hunion.
  - exact Hunion.
  - exact HyΣ.
Qed.

Lemma erase_ctx_under_comma_bind_env_fresh Σ Γ x τ :
  x ∉ dom (erase_ctx_under Σ Γ) →
  erase_ctx_under Σ (CtxComma Γ (CtxBind x τ)) =
  <[x := erase_ty τ]> (erase_ctx_under Σ Γ).
Proof.
  intros Hfresh.
  unfold erase_ctx_under in *.
  cbn [erase_ctx] in *.
  assert (HxΣ : x ∉ dom Σ) by better_set_solver.
  assert (HxΓ : x ∉ dom (erase_ctx Γ)) by better_set_solver.
  change (Σ ∪ ((erase_ctx Γ : gmap atom ty) ∪
      ({[x := erase_ty τ]} : gmap atom ty)) =
    <[x := erase_ty τ]> (Σ ∪ erase_ctx Γ)).
  replace ((erase_ctx Γ : gmap atom ty) ∪
      ({[x := erase_ty τ]} : gmap atom ty))
    with (<[x := erase_ty τ]> (erase_ctx Γ : gmap atom ty)).
  2:{
    symmetry.
    apply (storeA_union_singleton_insert_fresh
      (V := ty) (K := atom) (erase_ctx Γ : gmap atom ty)
      x (erase_ty τ)).
    exact HxΓ.
  }
  change (Σ ∪ (<[x := erase_ty τ]> (erase_ctx Γ : gmap atom ty) :
      gmap atom ty) =
    <[x := erase_ty τ]> (Σ ∪ erase_ctx Γ)).
  apply (storeA_insert_union_r_fresh (V := ty) (K := atom)
    (Σ : gmap atom ty) (erase_ctx Γ : gmap atom ty)
    x (erase_ty τ)).
  exact HxΣ.
Qed.

Lemma denot_ty_in_ctx_under_comma_bind_to_lvar_insert
    (Σ : gmap atom ty) Γ τx τ e y (m : WfWorldT) :
  y ∉ dom (erase_ctx Γ) ->
  m ⊨ denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind y τx)) τ e ->
  m ⊨ denot_ty_lvar_gas (cty_depth τ)
    (<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ)))
    τ e.
Proof.
  intros Hy Hden.
  unfold denot_ty_in_ctx_under, denot_ty in Hden |- *.
  assert (Henv :
      erase_ctx (CtxComma Γ (CtxBind y τx)) =
      <[y := erase_ty τx]> (erase_ctx Γ)).
  {
    cbn [erase_ctx].
    apply (storeA_union_singleton_insert_fresh
      (V := ty) (K := atom) (erase_ctx Γ : gmap atom ty)
      y (erase_ty τx)).
    exact Hy.
  }
  rewrite Henv in Hden.
  replace (<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ)))
    with (atom_env_to_lty_env
      (<[y := erase_ty τx]> (erase_ctx Γ))).
  2:{ apply atom_store_to_lvar_store_insert. }
  exact Hden.
Qed.

Lemma erase_ctx_under_comma_assoc Σ Γ1 Γ2 :
  erase_ctx_under Σ (CtxComma Γ1 Γ2) =
  erase_ctx_under (Σ ∪ erase_ctx Γ1) Γ2.
Proof.
  unfold erase_ctx_under. cbn [erase_ctx].
  apply map_eq. intros x.
  unfold store_union.
  rewrite !lookup_union.
  destruct ((Σ : gmap atom ty) !! x) as [TΣ|] eqn:HΣ;
    destruct ((erase_ctx Γ1 : gmap atom ty) !! x) as [T1|] eqn:H1;
    destruct ((erase_ctx Γ2 : gmap atom ty) !! x) as [T2|] eqn:H2;
    reflexivity.
Qed.

Lemma denot_ctx_under_comma_intro
    (Σ : gmap atom ty) Γ1 Γ2 (m : WfWorldT) :
  m ⊨ denot_ctx_under Σ Γ1 ->
  m ⊨ denot_ctx_under (Σ ∪ erase_ctx Γ1) Γ2 ->
  m ⊨ denot_ctx_under Σ (CtxComma Γ1 Γ2).
Proof.
  intros HΓ1 HΓ2.
  pose proof (denot_ctx_under_basic_world (Σ ∪ erase_ctx Γ1) Γ2 m HΓ2)
    as HworldΓ2.
  cbn [denot_ctx_under].
  rewrite res_models_and_iff. split.
  - rewrite erase_ctx_under_comma_assoc. exact HworldΓ2.
  - rewrite res_models_and_iff. split; assumption.
Qed.

End ContextDenotation.

#[global] Instance denot_cty_inst :
    Denotation context_ty (tm -> Formula (V := value)) :=
  fun τ e => denot_ty ∅ τ e.
#[global] Instance denot_ctx_inst :
    Denotation ctx (Formula (V := value)) := denot_ctx.
Arguments denot_cty_inst /.
Arguments denot_ctx_inst /.
