(** * Denotation.Context

    Denotation of type contexts, expressed directly with the new recursive
    context-type denotation. *)

From Denotation Require Export Notation TypeDenoteOpen.
From Denotation Require Import TypeEquivCore.

Section ContextDenotation.

Definition ctx_erasure_under (Σ : gmap atom ty) (Γ : ctx) : gmap atom ty :=
  Σ ∪ erase_ctx Γ.

Fixpoint ctx_denote_under (Σ : gmap atom ty) (Γ : ctx) : FormulaT :=
  FAnd (basic_world_formula (atom_env_to_lty_env (ctx_erasure_under Σ Γ)))
    (match Γ with
    | CtxEmpty =>
        FTrue
    | CtxBind x τ =>
        ty_denote (<[x := erase_ty τ]> Σ) τ (tret (vfvar x))
    | CtxComma Γ1 Γ2 =>
        FAnd
          (ctx_denote_under Σ Γ1)
          (ctx_denote_under (Σ ∪ erase_ctx Γ1) Γ2)
    | CtxStar Γ1 Γ2 =>
        FStar (ctx_denote_under Σ Γ1) (ctx_denote_under Σ Γ2)
    | CtxSum Γ1 Γ2 =>
        FPlus (ctx_denote_under Σ Γ1) (ctx_denote_under Σ Γ2)
    end).

Definition ctx_denote (Γ : ctx) : FormulaT :=
  ctx_denote_under ∅ Γ.

Definition ty_denote_ctx (Γ : ctx) (τ : context_ty) (e : tm) : FormulaT :=
  ty_denote (erase_ctx Γ) τ e.

Definition ty_denote_under
    (Σ : gmap atom ty) (Γ : ctx) (τ : context_ty) (e : tm) : FormulaT :=
  ty_denote (erase_ctx Γ) τ e.

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

Lemma ctx_denote_under_basic_world
    (Σ : gmap atom ty) (Γ : ctx) (m : WfWorldT) :
  m ⊨ ctx_denote_under Σ Γ ->
  m ⊨ basic_world_formula (atom_env_to_lty_env (ctx_erasure_under Σ Γ)).
Proof.
  intros Hctx.
  destruct Γ; cbn [ctx_denote_under] in Hctx |- *;
    rewrite res_models_and_iff in Hctx; exact (proj1 Hctx).
Qed.

Lemma ctx_denote_under_bind_inv
    (Σ : gmap atom ty) x τ (m : WfWorldT) :
  m ⊨ ctx_denote_under Σ (CtxBind x τ) ->
  m ⊨ ty_denote (<[x := erase_ty τ]> Σ) τ (tret (vfvar x)).
Proof.
  intros Hctx.
  cbn [ctx_denote_under] in Hctx.
  rewrite res_models_and_iff in Hctx.
  exact (proj2 Hctx).
Qed.

Lemma basic_world_formula_insert_from_arg_denotation
    (Σ : lty_env) (τ : context_ty) y T gas (m : WfWorldT) :
  LVFree y ∉ dom Σ ->
  m ⊨ basic_world_formula Σ ->
  m ⊨ ty_denote_gas gas (<[LVFree y := T]> Σ) τ (tret (vfvar y)) ->
  m ⊨ basic_world_formula (<[LVFree y := T]> Σ).
Proof.
  intros HyΣ Hworld Harg.
  pose proof (ty_denote_gas_guard gas
    (<[LVFree y := T]> Σ) τ (tret (vfvar y)) m Harg) as Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [_ [Hrel_world _]].
  assert (Hy_world : m ⊨ basic_world_formula
    (<[LVFree y := T]> (∅ : gmap logic_var ty))).
  {
    eapply basic_world_formula_subenv; [|exact Hrel_world].
    intros v U Hv.
    eapply lty_env_singleton_subenv_denot_relevant_env_ret_fvar.
    exact Hv.
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

Lemma ctx_denote_bind_from_arg_denotation
    (Σ : gmap atom ty) x τ (m : WfWorldT) :
  basic_context_ty ∅ τ ->
  Σ !! x = Some (erase_ty τ) ->
  m ⊨ ty_denote_gas (cty_depth τ) (atom_env_to_lty_env Σ)
    τ (tret (vfvar x)) ->
  m ⊨ ctx_denote (CtxBind x τ).
Proof.
  intros Hbasic Hlookup Harg.
  pose proof (res_models_ty_denote_gas_env_agree_on
    (cty_depth τ)
    (atom_env_to_lty_env Σ)
    (atom_env_to_lty_env (<[x := erase_ty τ]> (∅ : gmap atom ty)))
    τ (tret (vfvar x)) ({[LVFree x]}) m
    (denot_relevant_lvars_basic_ret_fvar_subset x τ Hbasic)
    (atom_env_to_lty_env_restrict_singleton_lookup
      Σ x (erase_ty τ) Hlookup)
    Harg) as Harg_single.
  unfold ctx_denote.
  cbn [ctx_denote_under].
  rewrite res_models_and_iff. split.
  - replace (ctx_erasure_under ∅ (CtxBind x τ))
      with (<[x := erase_ty τ]> (∅ : gmap atom ty)).
    2:{
      unfold ctx_erasure_under. cbn [erase_ctx].
      unfold store_union, store_singleton, store_empty.
      rewrite map_empty_union. reflexivity.
    }
    replace (atom_env_to_lty_env (<[x := erase_ty τ]> (∅ : gmap atom ty)))
      with (<[LVFree x := erase_ty τ]> (∅ : lty_env)).
    2:{
      unfold store_insert, store_empty.
      rewrite atom_store_to_lvar_store_insert.
      unfold atom_store_to_lvar_store.
      rewrite kmap_empty.
      reflexivity.
    }
    eapply basic_world_formula_insert_from_arg_denotation
      with (τ := τ) (gas := cty_depth τ)
        (y := x) (T := erase_ty τ) (Σ := ∅).
    + rewrite dom_empty_L. set_solver.
    + apply basic_world_formula_empty.
    + replace (<[LVFree x := erase_ty τ]> (∅ : lty_env))
        with (atom_env_to_lty_env (<[x := erase_ty τ]> (∅ : gmap atom ty))).
      * exact Harg_single.
      * symmetry.
        unfold store_insert, store_empty.
        rewrite atom_store_to_lvar_store_insert.
        unfold atom_store_to_lvar_store.
        rewrite kmap_empty.
        reflexivity.
  - unfold ty_denote.
    exact Harg_single.
Qed.

Lemma ty_denote_under_comma_bind_to_lvar_insert
    (Σ : gmap atom ty) Γ τx τ e y (m : WfWorldT) :
  y ∉ dom (erase_ctx Γ) ->
  m ⊨ ty_denote_under Σ (CtxComma Γ (CtxBind y τx)) τ e ->
  m ⊨ ty_denote_gas (cty_depth τ)
    (<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ)))
    τ e.
Proof.
  intros Hy Hden.
  unfold ty_denote_under, ty_denote in Hden |- *.
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

Lemma ctx_erasure_under_comma_assoc Σ Γ1 Γ2 :
  ctx_erasure_under Σ (CtxComma Γ1 Γ2) =
  ctx_erasure_under (Σ ∪ erase_ctx Γ1) Γ2.
Proof.
  unfold ctx_erasure_under. cbn [erase_ctx].
  apply map_eq. intros x.
  unfold store_union.
  rewrite !lookup_union.
  destruct ((Σ : gmap atom ty) !! x) as [TΣ|] eqn:HΣ;
    destruct ((erase_ctx Γ1 : gmap atom ty) !! x) as [T1|] eqn:H1;
    destruct ((erase_ctx Γ2 : gmap atom ty) !! x) as [T2|] eqn:H2;
    reflexivity.
Qed.

Lemma ctx_denote_under_comma_intro
    (Σ : gmap atom ty) Γ1 Γ2 (m : WfWorldT) :
  m ⊨ ctx_denote_under Σ Γ1 ->
  m ⊨ ctx_denote_under (Σ ∪ erase_ctx Γ1) Γ2 ->
  m ⊨ ctx_denote_under Σ (CtxComma Γ1 Γ2).
Proof.
  intros HΓ1 HΓ2.
  pose proof (ctx_denote_under_basic_world (Σ ∪ erase_ctx Γ1) Γ2 m HΓ2)
    as HworldΓ2.
  cbn [ctx_denote_under].
  rewrite res_models_and_iff. split.
  - rewrite ctx_erasure_under_comma_assoc. exact HworldΓ2.
  - rewrite res_models_and_iff. split; assumption.
Qed.

End ContextDenotation.

#[global] Instance denot_cty_inst :
    Denotation context_ty (tm -> Formula (V := value)) :=
  fun τ e => ty_denote ∅ τ e.
#[global] Instance ctx_denote_inst :
    Denotation ctx (Formula (V := value)) := ctx_denote.
Arguments denot_cty_inst /.
Arguments ctx_denote_inst /.
