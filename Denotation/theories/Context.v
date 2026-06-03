(** * Denotation.Context

    Denotation of type contexts, expressed directly with the new recursive
    context-type denotation. *)

From Denotation Require Export Notation ContextTypeDenotationOpen.
From Denotation Require Import ContextTypeDenotationMsubst
  ContextTypeDenotationSaturate.

Section ContextDenotation.

Definition erase_ctx_under (Σ : gmap atom ty) (Γ : ctx) : gmap atom ty :=
  Σ ∪ erase_ctx Γ.

Definition ctx_base_vars (Σ : gmap atom ty) : lvset :=
  lvars_of_atoms (dom Σ).

Lemma ctx_base_vars_fv (Σ : gmap atom ty) :
  lvars_fv (ctx_base_vars Σ) = dom Σ.
Proof. unfold ctx_base_vars. apply lvars_fv_of_atoms. Qed.

Lemma ctx_base_vars_lc (Σ : gmap atom ty) :
  lc_lvars (ctx_base_vars Σ).
Proof.
  intros [k|x] Hx; cbn [lc_logic_var_key]; [|exact I].
  unfold ctx_base_vars, lvars_of_atoms in Hx.
  apply elem_of_map in Hx as [a [Hbad _]]. discriminate.
Qed.

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

Definition denot_ctx_under_body (Σ : gmap atom ty) (Γ : ctx) : FormulaT :=
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

Lemma denot_ctx_under_unfold_body Σ Γ :
  denot_ctx_under Σ Γ = denot_ctx_under_body Σ Γ.
Proof. destruct Γ; reflexivity. Qed.

Definition denot_ctx (Γ : ctx) : FormulaT :=
  denot_ctx_under ∅ Γ.

Definition denot_ty_under
    (Σ : gmap atom ty) (τ : context_ty) (e : tm) : FormulaT :=
  denot_ty Σ τ e.

Definition denot_ty_in_ctx (Γ : ctx) (τ : context_ty) (e : tm) : FormulaT :=
  denot_ty (erase_ctx Γ) τ e.

Definition denot_ty_in_ctx_under
    (Σ : gmap atom ty) (Γ : ctx) (τ : context_ty) (e : tm) : FormulaT :=
  denot_ty (erase_ctx Γ) τ e.

Definition denot_ty_in_ctx_under_fiber
    (Σ : gmap atom ty) (Γ : ctx) (τ : context_ty) (e : tm) : FormulaT :=
  denot_ty_in_ctx_under Σ Γ τ e.

Lemma denot_ty_in_ctx_under_fiber_intro
    (Σ : gmap atom ty) Γ τ e (m : WfWorldT) :
  formula_scoped_in_world m (denot_ty_in_ctx_under_fiber Σ Γ τ e) ->
  (forall σΣ mfib,
    res_fiber_from_projection m (dom Σ) σΣ mfib ->
    mfib ⊨ formula_msubst_store σΣ (denot_ty_in_ctx_under Σ Γ τ e)) ->
  m ⊨ denot_ty_in_ctx_under_fiber Σ Γ τ e.
Proof.
  (* Compatibility obligation for the old fiberwise Soundness route.
     The new definition-level route uses [denot_ty_in_ctx_under] directly. *)
Admitted.

Lemma denot_ty_in_ctx_under_fiber_elim_projection
    (Σ : gmap atom ty) Γ τ e (m mfib : WfWorldT) (σΣ : StoreT) :
  res_fiber_from_projection m (dom Σ) σΣ mfib ->
  m ⊨ denot_ty_in_ctx_under_fiber Σ Γ τ e ->
  mfib ⊨ formula_msubst_store σΣ (denot_ty_in_ctx_under Σ Γ τ e).
Proof.
  (* Compatibility obligation for callers that still expect base-fiber
     elimination. This is no longer part of the new public target. *)
Admitted.

Lemma denot_ctx_under_projection_store_has_type
    (Σ : gmap atom ty) Γ (m mfib : WfWorldT) (σΣ : StoreT) :
  m ⊨ denot_ctx_under Σ Γ ->
  res_fiber_from_projection m (dom Σ) σΣ mfib ->
  storeA_has_type Σ σΣ.
Proof.
  (* TODO(new context denotation): prove directly from the leading
     [basic_world_formula (erase_ctx_under Σ Γ)]. The previous proof used the
     removed outer [FFibVars (ctx_base_vars Σ)]. *)
Admitted.

Lemma denot_ty_in_ctx_under_fiber_elim_projection_instantiated
    (Σ : gmap atom ty) Γ τ e (m mfib : WfWorldT) (σΣ : StoreT) :
  context_typing_wf_erased Σ (erase_ctx_under Σ Γ) e τ ->
  storeA_has_type Σ σΣ ->
  res_fiber_from_projection m (dom Σ) σΣ mfib ->
  m ⊨ denot_ty_in_ctx_under_fiber Σ Γ τ e ->
  mfib ⊨ denot_ty_lvar_gas (cty_depth τ)
    (atom_env_to_lty_env (erase_ctx_under Σ Γ)) τ
    (lstore_instantiate_tm (lstore_lift_free σΣ) e).
Proof.
  (* Old msubst/fiber bridge. New Soundness should call the local target
     [denot_ty (erase_ctx Γ) τ e] directly. *)
Admitted.

Lemma denot_ty_in_ctx_under_fiber_elim_singleton_instantiated
    (Σ : gmap atom ty) Γ τ e (m : WfWorldT) (σΣ : StoreT) :
  context_typing_wf_erased Σ (erase_ctx_under Σ Γ) e τ ->
  storeA_has_type Σ σΣ ->
  base_store_projection Σ σΣ m ->
  m ⊨ denot_ty_in_ctx_under_fiber Σ Γ τ e ->
  m ⊨ denot_ty_lvar_gas (cty_depth τ)
    (atom_env_to_lty_env (erase_ctx_under Σ Γ)) τ
    (lstore_instantiate_tm (lstore_lift_free σΣ) e).
Proof.
  (* Old singleton-instantiated bridge retained as a precise compatibility
     obligation while Soundness is retargeted to local denotation. *)
Admitted.

Lemma base_store_projection_from_superset_fiber
    (Σ : gmap atom ty) (σΣ σX : StoreT)
    (m mfib : WfWorldT) X :
  base_store_projection Σ σΣ m ->
  dom Σ ⊆ X ->
  res_fiber_from_projection m X σX mfib ->
  base_store_projection Σ σΣ mfib.
Proof.
  intros [Hdomσ Hsingle] HΣX Hfib.
  split; [exact Hdomσ|].
  pose proof (res_fiber_from_projection_subset_source
    m mfib X σX Hfib) as Hsub.
  assert (HΣmfib : dom Σ ⊆ world_dom (mfib : WorldT)).
  {
    rewrite (res_fiber_from_projection_world_dom m mfib X σX Hfib).
    pose proof (f_equal world_dom Hsingle) as Hdom_single.
    cbn [res_restrict resA_restrict rawA_restrict worldA_dom
      singleton_world] in Hdom_single.
    change (dom (σΣ : StoreT)) with (dom (σΣ : gmap atom value))
      in Hdom_single.
    set_solver.
  }
  eapply res_subset_singleton_restrict; eauto.
Qed.

Definition denot_ty_total_in_ctx_under
    (Σ : gmap atom ty) (Γ : ctx) (τ : context_ty) (e : tm)
    (m : WfWorldT) : Prop :=
  m ⊨ denot_ty_in_ctx_under Σ Γ τ e ∧
  m ⊨ expr_total_formula e.

Definition entails_total (φ : FormulaT) (P : WfWorldT -> Prop) : Prop :=
  forall m, m ⊨ φ -> P m.

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

Lemma denot_ctx_under_comma_inv
    (Σ : gmap atom ty) Γ1 Γ2 (m : WfWorldT) :
  m ⊨ denot_ctx_under Σ (CtxComma Γ1 Γ2) ->
  m ⊨ denot_ctx_under Σ Γ1 /\
  m ⊨ denot_ctx_under (Σ ∪ erase_ctx Γ1) Γ2.
Proof.
  intros Hctx.
  cbn [denot_ctx_under] in Hctx.
  rewrite res_models_and_iff in Hctx.
  rewrite res_models_and_iff in Hctx.
  exact (proj2 Hctx).
Qed.

Lemma denot_ctx_under_projected_body
    (Σ : gmap atom ty) Γ (m mfib : WfWorldT) (σΣ : StoreT) :
  res_fiber_from_projection m (dom Σ) σΣ mfib ->
  m ⊨ denot_ctx_under Σ Γ ->
  mfib ⊨ formula_msubst_store σΣ (denot_ctx_under_body Σ Γ).
Proof.
  (* Compatibility obligation for the removed outer base-fiber wrapper. *)
Admitted.

Lemma denot_ctx_under_fiber_from_projection
    (Σ : gmap atom ty) Γ (m mfib : WfWorldT) (σΣ : StoreT) :
  res_fiber_from_projection m (dom Σ) σΣ mfib ->
  m ⊨ denot_ctx_under Σ Γ ->
  mfib ⊨ denot_ctx_under Σ Γ.
Proof.
  (* Compatibility obligation for old fiberwise context lemmas. The new
     context denotation no longer asserts arbitrary base-fiber preservation. *)
Admitted.

Lemma denot_ctx_under_relevant_basic_world
    (Σ : gmap atom ty) (Γ : ctx) τ e (m : WfWorldT) :
  m ⊨ denot_ctx_under Σ Γ ->
  m ⊨ basic_world_formula
    (denot_relevant_env (atom_env_to_lty_env (erase_ctx_under Σ Γ)) τ e).
Proof.
  intros Hctx.
  pose proof (denot_ctx_under_basic_world Σ Γ m Hctx) as Hworld.
  eapply basic_world_formula_subenv.
  - intros v T Hv.
    eapply storeA_restrict_lookup_some in Hv as [_ Hv].
    exact Hv.
  - exact Hworld.
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

Ltac destruct_basic_world_formula_hyps :=
  repeat match goal with
  | H : res_models _ (FAnd _ _) |- _ =>
      rewrite res_models_and_iff in H; destruct H
  | H : _ /\ _ |- _ =>
      destruct H
  end.

Ltac solve_basic_world_formula :=
  destruct_basic_world_formula_hyps;
  first
    [ assumption
    | eassumption
    | match goal with
      | Hctx : ?m ⊨ denot_ctx_under ?Σ ?Γ
        |- ?m ⊨ basic_world_formula
             (atom_env_to_lty_env (erase_ctx_under ?Σ ?Γ)) =>
          exact (denot_ctx_under_basic_world Σ Γ m Hctx)
      | Hctx : ?m ⊨ denot_ctx_under ?Σ ?Γ
        |- ?m ⊨ basic_world_formula
             (denot_relevant_env
                (atom_env_to_lty_env (erase_ctx_under ?Σ ?Γ)) ?τ ?e) =>
          exact (denot_ctx_under_relevant_basic_world Σ Γ τ e m Hctx)
      end
    | eauto ].

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

Lemma erase_ctx_under_star_bind_env_fresh Σ Γ x τ :
  x ∉ dom (erase_ctx_under Σ Γ) →
  erase_ctx_under Σ (CtxStar Γ (CtxBind x τ)) =
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

Lemma denot_ctx_under_comma_bind_from_fibered_arg_denotation
    (Σ : gmap atom ty) (Γ : ctx) (τx : context_ty) y
    (my : WfWorldT) :
  y ∉ dom (erase_ctx_under Σ Γ) ->
  my ⊨ denot_ctx_under Σ Γ ->
  my ⊨ denot_ctx_under (erase_ctx_under Σ Γ) (CtxBind y τx) ->
  my ⊨ denot_ctx_under Σ (CtxComma Γ (CtxBind y τx)).
Proof.
  intros _ Hctx Harg.
  eapply denot_ctx_under_comma_intro; [exact Hctx|].
  unfold erase_ctx_under in Harg. exact Harg.
Qed.

Lemma denot_ctx_under_bind_projection_intro
    (Σ : gmap atom ty) x τ (m : WfWorldT) :
  formula_scoped_in_world m (denot_ctx_under Σ (CtxBind x τ)) ->
  (forall σΣ mfib,
    res_fiber_from_projection m (dom Σ) σΣ mfib ->
    mfib ⊨ formula_msubst_store σΣ
      (FAnd
        (basic_world_formula
          (atom_env_to_lty_env (erase_ctx_under Σ (CtxBind x τ))))
        (denot_ty (<[x := erase_ty τ]> Σ) τ (tret (vfvar x))))) ->
  m ⊨ denot_ctx_under Σ (CtxBind x τ).
Proof.
  (* Compatibility obligation for the removed outer base-fiber wrapper. *)
Admitted.

Lemma denot_ctx_under_bind_scope_from_result_denotation
    (Σ : gmap atom ty) (τ1 : context_ty) e1
    (m mx : WfWorldT) (Fx : FiberExtensionT) (x : atom) :
  x ∉ dom Σ ->
  expr_result_extension_witness e1 x Fx ->
  res_extend_by m Fx mx ->
  m ⊨ basic_world_formula (atom_env_to_lty_env Σ) ->
  basic_context_ty (dom Σ) τ1 ->
  formula_scoped_in_world mx (denot_ctx_under Σ (CtxBind x τ1)).
Proof.
  intros Hfresh HFx Hext Hworld Hτbasic.
  pose proof (proj1 (basic_world_formula_models_iff
    (atom_env_to_lty_env Σ) m) Hworld) as [_ [HΣm_lvar _]].
  assert (HΣm : dom Σ ⊆ world_dom (m : WorldT)).
  {
    intros a Ha.
    apply HΣm_lvar.
    rewrite atom_store_to_lvar_store_dom.
    rewrite lvars_fv_of_atoms. exact Ha.
  }
  pose proof (res_extend_by_dom_base_subset m Fx mx Hext) as Hm_mx.
  assert (HΣmx : dom Σ ⊆ world_dom (mx : WorldT)) by set_solver.
  destruct HFx as [_ [_ Hout] _].
  pose proof (res_extend_by_dom_output_subset m Fx mx Hext) as Hout_mx.
  assert (Hxmx : x ∈ world_dom (mx : WorldT)).
  {
    apply Hout_mx.
    change (x ∈ ext_out Fx).
    rewrite Hout. set_solver.
  }
  assert (HτΣ : fv_cty τ1 ⊆ dom Σ).
  {
    pose proof (basic_context_ty_to_lvars _ _ Hτbasic) as [Hτvars _].
    rewrite <- context_ty_lvars_fv.
    intros a Ha.
    apply lvars_fv_elem in Ha.
    apply Hτvars in Ha.
    unfold lvars_of_atoms in Ha.
    apply elem_of_map in Ha as [b [Heq Hb]].
    inversion Heq. subst b. exact Hb.
  }
  rewrite denot_ctx_under_unfold_body.
  unfold denot_ctx_under_body.
  cbn [erase_ctx].
  apply (proj2 (formula_scoped_and_iff _ _ _)).
  split.
  - unfold formula_scoped_in_world.
    rewrite formula_fv_basic_world_formula.
    intros a Ha.
    rewrite atom_store_to_lvar_store_dom in Ha.
    apply lvars_fv_elem in Ha.
    unfold lvars_of_atoms in Ha.
    apply elem_of_map in Ha as [a' [Heq Ha]].
    inversion Heq. subst a'.
    unfold erase_ctx_under in Ha.
    cbn [erase_ctx] in Ha.
    apply elem_of_dom in Ha as [T Hlook].
    change ((Σ ∪ ({[x := erase_ty τ1]} : gmap atom ty)) !! a = Some T)
      in Hlook.
    apply map_lookup_union_Some_raw in Hlook as [HΣa|[_ Hxa]].
    + apply HΣmx. apply elem_of_dom. exists T. exact HΣa.
    + destruct (decide (a = x)) as [->|Hneq]; [exact Hxmx|].
      change ((({[x := erase_ty τ1]} : gmap atom ty) !! a) = Some T) in Hxa.
      pose proof (lookup_singleton_Some
        (M := gmap atom) x a (erase_ty τ1) T) as Hsingle.
      apply Hsingle in Hxa as [Hxa _].
      symmetry in Hxa. contradiction.
  - unfold denot_ty, formula_scoped_in_world.
    transitivity (fv_tm (tret (vfvar x)) ∪ fv_cty τ1).
    + apply formula_fv_denot_ty_lvar_gas_subset_relevant.
    + cbn [fv_tm fv_value]. set_solver.
Qed.

Lemma denot_ctx_under_bind_projected_body_basic_world
    (Σ : gmap atom ty) (τ1 : context_ty) e1
    (m mx mfib : WfWorldT) (Fx : FiberExtensionT)
    (x : atom) (σΣ : StoreT) :
  x ∉ dom Σ ->
  expr_result_extension_witness e1 x Fx ->
  res_extend_by m Fx mx ->
  m ⊨ basic_world_formula (atom_env_to_lty_env Σ) ->
  m ⊨ denot_ty_lvar_gas (cty_depth τ1)
    (atom_env_to_lty_env Σ) τ1 e1 ->
  res_fiber_from_projection mx (dom Σ) σΣ mfib ->
  mfib ⊨ formula_msubst_store σΣ
    (basic_world_formula
      (atom_env_to_lty_env (erase_ctx_under Σ (CtxBind x τ1)))).
Proof.
  intros Hfresh HFx Hext Hworld Hden Hproj.
  pose proof (denot_ty_lvar_gas_guard (cty_depth τ1)
    (atom_env_to_lty_env Σ) τ1 e1 m Hden) as Hguard.
  assert (HFx_ltype :
      extension_has_ltype (<[LVFree x := erase_ty τ1]> ∅)
        (res_restrict m (ext_in Fx)) Fx).
  {
    eapply expr_result_extension_has_ltype_from_source_guard.
    - apply atom_store_to_lvar_store_closed.
    - rewrite atom_store_to_lvar_store_dom.
      intros Hbad.
      apply Hfresh.
      apply lvars_fv_elem in Hbad.
      rewrite lvars_fv_of_atoms in Hbad. exact Hbad.
    - exact HFx.
    - exact Hext.
    - exact Hguard.
  }
  assert (Hmx_world :
      mx ⊨ basic_world_formula
        (<[LVFree x := erase_ty τ1]> (atom_env_to_lty_env Σ))).
  {
    eapply basic_world_formula_insert_typed_extension.
    - rewrite atom_store_to_lvar_store_dom.
      intros Hbad.
      apply Hfresh.
      apply lvars_fv_elem in Hbad.
      rewrite lvars_fv_of_atoms in Hbad. exact Hbad.
    - exact Hworld.
    - exact HFx_ltype.
    - exact Hext.
  }
  assert (Hmx_fib :
      mx ⊨ FFibVars (ctx_base_vars Σ)
        (basic_world_formula
          (atom_env_to_lty_env (erase_ctx_under Σ (CtxBind x τ1))))).
  {
    replace (atom_env_to_lty_env (erase_ctx_under Σ (CtxBind x τ1)))
      with (<[LVFree x := erase_ty τ1]> (atom_env_to_lty_env Σ)).
    2:{
      rewrite <- atom_store_to_lvar_store_insert.
      f_equal.
      unfold erase_ctx_under, store_union, store_singleton, store_insert.
      cbn [erase_ctx].
      symmetry.
      apply storeA_union_singleton_insert_fresh. exact Hfresh.
    }
    eapply basic_world_formula_fibvars_intro.
    - apply ctx_base_vars_lc.
    - rewrite ctx_base_vars_fv.
      rewrite dom_insert_L, atom_store_to_lvar_store_dom.
      rewrite lvars_fv_union, lvars_fv_singleton_free, lvars_fv_of_atoms.
      set_solver.
    - exact Hmx_world.
  }
  pose proof (res_models_scoped _ _ Hmx_fib) as Hscope.
  pose proof (proj1 (res_models_FFibVars_iff _ _ _ Hscope) Hmx_fib)
    as [_ Hfib].
  apply Hfib.
  rewrite ctx_base_vars_fv. exact Hproj.
Qed.

Lemma basic_world_formula_projection_store_has_type
    (Σ : gmap atom ty) (m mfib : WfWorldT) (σΣ : StoreT) :
  m ⊨ basic_world_formula (atom_env_to_lty_env Σ) ->
  res_fiber_from_projection m (dom Σ) σΣ mfib ->
  storeA_has_type Σ σΣ.
Proof.
  intros Hworld Hproj a T v HΣa Hσa.
  assert (HΣm : dom Σ ⊆ world_dom (m : WorldT)).
  {
    pose proof (proj1 (basic_world_formula_models_iff
      (atom_env_to_lty_env Σ) m) Hworld) as [_ [Hscope _]].
    intros x Hx.
    apply Hscope.
    rewrite atom_store_to_lvar_store_dom.
    rewrite lvars_fv_of_atoms. exact Hx.
  }
  assert (Hdomσ : dom (σΣ : StoreT) = dom Σ).
  { eapply res_fiber_from_projection_store_dom; eauto. }
  assert (Hfib_world :
      mfib ⊨ formula_msubst_store σΣ
        (basic_world_formula (atom_env_to_lty_env Σ))).
  {
    assert (Hfib :
        m ⊨ FFibVars (ctx_base_vars Σ)
          (basic_world_formula (atom_env_to_lty_env Σ))).
    {
      eapply basic_world_formula_fibvars_intro.
      - apply ctx_base_vars_lc.
      - rewrite ctx_base_vars_fv.
        rewrite atom_store_to_lvar_store_dom.
        rewrite lvars_fv_of_atoms. set_solver.
      - exact Hworld.
    }
    pose proof (res_models_scoped _ _ Hfib) as Hscope.
    pose proof (proj1 (res_models_FFibVars_iff _ _ _ Hscope) Hfib)
      as [_ Hfib_elim].
    apply Hfib_elim. rewrite ctx_base_vars_fv. exact Hproj.
  }
  pose proof (basic_world_formula_msubst_store_extract_atom_store_has_ltype
    σΣ (atom_env_to_lty_env Σ) mfib) as Hextract.
  assert (HσΣ :
      lvars_of_atoms (dom (σΣ : gmap atom value)) ⊆
      dom (atom_env_to_lty_env Σ)).
  {
    change (lvars_of_atoms (dom (σΣ : StoreT)) ⊆
      dom (atom_env_to_lty_env Σ)).
    rewrite Hdomσ.
    rewrite atom_store_to_lvar_store_dom.
    unfold lvars_of_atoms.
    intros lv Hlv.
    apply elem_of_map in Hlv as [x [-> Hx]].
    apply elem_of_map. exists x. split; [reflexivity|exact Hx].
  }
  destruct (Hextract HσΣ Hfib_world a v Hσa) as [T' [Hlookup Hv]].
  rewrite atom_store_to_lvar_store_lookup_free in Hlookup.
  rewrite HΣa in Hlookup. inversion Hlookup. subst T'. exact Hv.
Qed.

Lemma storeA_has_type_from_basic_world_extension_projection
    (Σ : gmap atom ty) (τ1 : context_ty) e1
    (m mx mfib : WfWorldT) (Fx : FiberExtensionT)
    (x : atom) (σΣ : StoreT) :
  x ∉ dom Σ ->
  expr_result_extension_witness e1 x Fx ->
  res_extend_by m Fx mx ->
  m ⊨ basic_world_formula (atom_env_to_lty_env Σ) ->
  m ⊨ denot_ty_lvar_gas (cty_depth τ1)
    (atom_env_to_lty_env Σ) τ1 e1 ->
  res_fiber_from_projection mx (dom Σ) σΣ mfib ->
  storeA_has_type Σ σΣ.
Proof.
  intros Hfresh HFx Hext Hworld Hden Hproj.
  pose proof (denot_ty_lvar_gas_guard (cty_depth τ1)
    (atom_env_to_lty_env Σ) τ1 e1 m Hden) as Hguard.
  assert (HFx_ltype :
      extension_has_ltype (<[LVFree x := erase_ty τ1]> ∅)
        (res_restrict m (ext_in Fx)) Fx).
  {
    eapply expr_result_extension_has_ltype_from_source_guard.
    - apply atom_store_to_lvar_store_closed.
    - rewrite atom_store_to_lvar_store_dom.
      intros Hbad.
      apply Hfresh.
      apply lvars_fv_elem in Hbad.
      rewrite lvars_fv_of_atoms in Hbad. exact Hbad.
    - exact HFx.
    - exact Hext.
    - exact Hguard.
  }
  assert (Hmx_world :
      mx ⊨ basic_world_formula
        (<[LVFree x := erase_ty τ1]> (atom_env_to_lty_env Σ))).
  {
    eapply basic_world_formula_insert_typed_extension.
    - rewrite atom_store_to_lvar_store_dom.
      intros Hbad.
      apply Hfresh.
      apply lvars_fv_elem in Hbad.
      rewrite lvars_fv_of_atoms in Hbad. exact Hbad.
    - exact Hworld.
    - exact HFx_ltype.
    - exact Hext.
  }
  assert (HΣmx : dom Σ ⊆ world_dom (mx : WorldT)).
  {
    pose proof (proj1 (basic_world_formula_models_iff
      (atom_env_to_lty_env Σ) m) Hworld) as [_ [HΣm_lvar _]].
    pose proof (res_extend_by_dom_base_subset m Fx mx Hext) as Hm_mx.
    intros a Ha.
    apply Hm_mx. apply HΣm_lvar.
    rewrite atom_store_to_lvar_store_dom.
    rewrite lvars_fv_of_atoms. exact Ha.
  }
  assert (Hdomσ : dom (σΣ : StoreT) = dom Σ).
  {
    eapply res_fiber_from_projection_store_dom; eauto.
  }
  assert (Hmx_fib :
      mx ⊨ FFibVars (ctx_base_vars Σ)
        (basic_world_formula
          (<[LVFree x := erase_ty τ1]> (atom_env_to_lty_env Σ)))).
  {
    eapply basic_world_formula_fibvars_intro.
    - apply ctx_base_vars_lc.
    - rewrite ctx_base_vars_fv.
      rewrite dom_insert_L, atom_store_to_lvar_store_dom.
      rewrite lvars_fv_union, lvars_fv_singleton_free, lvars_fv_of_atoms.
      set_solver.
    - exact Hmx_world.
  }
  pose proof (res_models_scoped _ _ Hmx_fib) as Hscope.
  pose proof (proj1 (res_models_FFibVars_iff _ _ _ Hscope) Hmx_fib)
    as [_ Hfib].
  specialize (Hfib σΣ mfib ltac:(rewrite ctx_base_vars_fv; exact Hproj)).
  assert (Hσ_ltype :
      atom_store_has_ltype
        (<[LVFree x := erase_ty τ1]> (atom_env_to_lty_env Σ)) σΣ).
  {
    eapply basic_world_formula_msubst_store_extract_atom_store_has_ltype.
    - change (lvars_of_atoms (dom (σΣ : StoreT)) ⊆
        dom (<[LVFree x := erase_ty τ1]> (atom_env_to_lty_env Σ))).
      rewrite Hdomσ.
      intros v Hv.
      unfold lvars_of_atoms in Hv.
      apply elem_of_map in Hv as [a [-> Ha]].
      apply elem_of_dom in Ha as [T HΣa].
      apply elem_of_dom. exists T.
      rewrite lookup_insert_ne.
      + rewrite atom_store_to_lvar_store_lookup_free. exact HΣa.
      + intros Heq. inversion Heq. subst a.
        apply Hfresh. apply elem_of_dom. eauto.
    - exact Hfib.
  }
  intros a T v HΣa Hσa.
  destruct (Hσ_ltype a v Hσa) as [T' [Hlookup Hv]].
  rewrite lookup_insert_ne in Hlookup.
  2:{
    intros Heq. inversion Heq. subst a.
    apply Hfresh. apply elem_of_dom. eauto.
  }
  rewrite atom_store_to_lvar_store_lookup_free in Hlookup.
  rewrite HΣa in Hlookup. inversion Hlookup. subst T'. exact Hv.
Qed.

Lemma denot_ctx_under_bind_projected_body_arg_instantiated_from_source
    (Σ : gmap atom ty) (τ1 : context_ty) e1
    (msrc mfib : WfWorldT) (Fx : FiberExtensionT) (x : atom) :
  x ∉ dom Σ ->
  expr_result_extension_witness e1 x Fx ->
  res_extend_by msrc Fx mfib ->
  msrc ⊨ denot_ty_lvar_gas (cty_depth τ1)
    (atom_env_to_lty_env Σ) τ1 e1 ->
  mfib ⊨ denot_ty_lvar_gas (cty_depth τ1)
    (atom_env_to_lty_env (<[x := erase_ty τ1]> Σ)) τ1
    (tret (vfvar x)).
Proof.
  intros Hfresh HFx Hext Hden.
  replace (atom_env_to_lty_env (<[x := erase_ty τ1]> Σ))
    with (<[LVFree x := erase_ty τ1]> (atom_env_to_lty_env Σ)).
  2:{ symmetry. apply atom_store_to_lvar_store_insert. }
  eapply denot_ty_lvar_gas_result_extension_to_var; eauto.
  - apply atom_store_to_lvar_store_closed.
  - rewrite atom_store_to_lvar_store_dom.
    intros Hbad.
    apply lvars_fv_elem in Hbad.
    rewrite lvars_fv_of_atoms in Hbad.
    exact (Hfresh Hbad).
Qed.

Lemma denot_ctx_under_bind_projected_body_arg_denotation
    (Σbase Σ : gmap atom ty) (τ1 : context_ty) e1
    (m mx mfib : WfWorldT) (Fx : FiberExtensionT)
    (x : atom) (σΣ : StoreT) :
  context_typing_wf_erased Σbase Σ e1 τ1 ->
  x ∉ dom Σ ->
  expr_result_extension_witness e1 x Fx ->
  res_extend_by m Fx mx ->
  m ⊨ basic_world_formula (atom_env_to_lty_env Σ) ->
  (forall σsrc msrc,
    res_fiber_from_projection m (dom Σ) σsrc msrc ->
    msrc ⊨ denot_ty_lvar_gas (cty_depth τ1)
      (atom_env_to_lty_env Σ) τ1 e1) ->
  res_fiber_from_projection mx (dom Σ) σΣ mfib ->
  mfib ⊨ formula_msubst_store σΣ
    (denot_ty (<[x := erase_ty τ1]> Σ) τ1 (tret (vfvar x))).
Proof.
  intros Hwf Hfresh HFx Hext Hworld Hsource Hproj.
  assert (HΣmx : dom Σ ⊆ world_dom (mx : WorldT)).
  {
    pose proof (proj1 (basic_world_formula_models_iff
      (atom_env_to_lty_env Σ) m) Hworld) as [_ [HΣm_lvar _]].
    pose proof (res_extend_by_dom_base_subset m Fx mx Hext) as Hm_mx.
    intros a Ha.
    apply Hm_mx. apply HΣm_lvar.
    rewrite atom_store_to_lvar_store_dom.
    rewrite lvars_fv_of_atoms. exact Ha.
  }
  pose proof (base_store_projection_from_fiber Σ mx mfib σΣ
    HΣmx Hproj) as Hbase.
  assert (HΣm : dom Σ ⊆ world_dom (m : WorldT)).
  {
    pose proof (proj1 (basic_world_formula_models_iff
      (atom_env_to_lty_env Σ) m) Hworld) as [_ [HΣm_lvar _]].
    intros a Ha.
    apply HΣm_lvar.
    rewrite atom_store_to_lvar_store_dom.
    rewrite lvars_fv_of_atoms. exact Ha.
  }
  assert (Hin : ext_in Fx ⊆ dom Σ).
  {
    destruct HFx as [_ [Hin _] _].
    unfold ext_in in *.
    rewrite Hin.
    pose proof (context_typing_wf_erased_basic_typing
      Σbase Σ e1 τ1 Hwf) as Hbasic.
    exact (basic_typing_contains_fv_tm _ _ _ Hbasic).
  }
  assert (Hout : ext_out Fx ## dom Σ).
  {
    destruct HFx as [_ [_ Hout] _].
    unfold ext_out in *.
    rewrite Hout. set_solver.
  }
  destruct (res_extend_by_fiber_from_projection
    m mx mfib Fx (dom Σ) σΣ
    Hin Hout HΣm Hext Hproj) as [msrc [Hsrc_proj Hsrc_ext]].
  pose proof (basic_world_formula_projection_store_has_type
    Σ m msrc σΣ Hworld Hsrc_proj) as Hσty.
  pose proof (context_typing_wf_erased_bind_ret_fvar
    Σbase Σ e1 τ1 x Hwf Hfresh) as Hwf_ret.
  pose proof (Hsource σΣ msrc Hsrc_proj) as Hsource_den.
  pose proof (denot_ctx_under_bind_projected_body_arg_instantiated_from_source
    Σ τ1 e1 msrc mfib Fx x
    Hfresh HFx Hsrc_ext Hsource_den) as Htarget_raw.
  assert (Hxσ : x ∉ dom (σΣ : StoreT)).
  {
    rewrite (proj1 Hbase). exact Hfresh.
  }
  rewrite <- (lstore_instantiate_tm_lift_free_tret_fvar_fresh σΣ x Hxσ)
    in Htarget_raw.
  unfold denot_ty.
  eapply denot_ty_lvar_gas_msubst_store_to_typing_wf; eauto.
Qed.

Lemma denot_ctx_under_bind_projected_body_basic_world_source_fiber
    (Σbase Σ : gmap atom ty) (τ1 : context_ty) e1
    (m mx mfib : WfWorldT) (Fx : FiberExtensionT)
    (x : atom) (σΣ : StoreT) :
  context_typing_wf_erased Σbase Σ e1 τ1 ->
  x ∉ dom Σ ->
  expr_result_extension_witness e1 x Fx ->
  res_extend_by m Fx mx ->
  m ⊨ basic_world_formula (atom_env_to_lty_env Σ) ->
  (forall σsrc msrc,
    res_fiber_from_projection m (dom Σ) σsrc msrc ->
    msrc ⊨ denot_ty_lvar_gas (cty_depth τ1)
      (atom_env_to_lty_env Σ) τ1 e1) ->
  res_fiber_from_projection mx (dom Σ) σΣ mfib ->
  mfib ⊨ formula_msubst_store σΣ
    (basic_world_formula
      (atom_env_to_lty_env (erase_ctx_under Σ (CtxBind x τ1)))).
Proof.
  intros Hwf Hfresh HFx Hext Hworld Hsource Hproj.
  assert (HΣm : dom Σ ⊆ world_dom (m : WorldT)).
  {
    pose proof (proj1 (basic_world_formula_models_iff
      (atom_env_to_lty_env Σ) m) Hworld) as [_ [HΣm_lvar _]].
    intros a Ha.
    apply HΣm_lvar.
    rewrite atom_store_to_lvar_store_dom.
    rewrite lvars_fv_of_atoms. exact Ha.
  }
  assert (HΣmx : dom Σ ⊆ world_dom (mx : WorldT)).
  {
    pose proof (res_extend_by_dom_base_subset m Fx mx Hext) as Hm_mx.
    set_solver.
  }
  assert (Hin : ext_in Fx ⊆ dom Σ).
  {
    destruct HFx as [_ [Hin _] _].
    unfold ext_in in *.
    rewrite Hin.
    pose proof (context_typing_wf_erased_basic_typing
      Σbase Σ e1 τ1 Hwf) as Hbasic.
    exact (basic_typing_contains_fv_tm _ _ _ Hbasic).
  }
  assert (Hout : ext_out Fx ## dom Σ).
  {
    destruct HFx as [_ [_ Hout] _].
    unfold ext_out in *.
    rewrite Hout. set_solver.
  }
  destruct (res_extend_by_fiber_from_projection
    m mx mfib Fx (dom Σ) σΣ
    Hin Hout HΣm Hext Hproj) as [msrc [Hsrc_proj Hsrc_ext]].
  pose proof (Hsource σΣ msrc Hsrc_proj) as Hsource_den.
  assert (Hsource_world :
      msrc ⊨ basic_world_formula (atom_env_to_lty_env Σ)).
  {
    eapply basic_world_formula_res_subset.
    - eapply res_fiber_from_projection_subset_source. exact Hsrc_proj.
    - exact Hworld.
  }
  pose proof (denot_ty_lvar_gas_guard (cty_depth τ1)
    (atom_env_to_lty_env Σ) τ1 e1 msrc Hsource_den) as Hguard.
  assert (HFx_ltype :
      extension_has_ltype (<[LVFree x := erase_ty τ1]> ∅)
        (res_restrict msrc (ext_in Fx)) Fx).
  {
    eapply expr_result_extension_has_ltype_from_source_guard.
    - apply atom_store_to_lvar_store_closed.
    - rewrite atom_store_to_lvar_store_dom.
      intros Hbad.
      apply Hfresh.
      apply lvars_fv_elem in Hbad.
      rewrite lvars_fv_of_atoms in Hbad. exact Hbad.
    - exact HFx.
    - exact Hsrc_ext.
    - exact Hguard.
  }
  assert (Hmfib_world :
      mfib ⊨ basic_world_formula
        (<[LVFree x := erase_ty τ1]> (atom_env_to_lty_env Σ))).
  {
    eapply basic_world_formula_insert_typed_extension.
    - rewrite atom_store_to_lvar_store_dom.
      intros Hbad.
      apply Hfresh.
      apply lvars_fv_elem in Hbad.
      rewrite lvars_fv_of_atoms in Hbad. exact Hbad.
    - exact Hsource_world.
    - exact HFx_ltype.
    - exact Hsrc_ext.
  }
  assert (Hmfib_fib :
      mfib ⊨ FFibVars (ctx_base_vars Σ)
        (basic_world_formula
          (atom_env_to_lty_env (erase_ctx_under Σ (CtxBind x τ1))))).
  {
    replace (atom_env_to_lty_env (erase_ctx_under Σ (CtxBind x τ1)))
      with (<[LVFree x := erase_ty τ1]> (atom_env_to_lty_env Σ)).
    2:{
      rewrite <- atom_store_to_lvar_store_insert.
      f_equal.
      unfold erase_ctx_under, store_union, store_singleton, store_insert.
      cbn [erase_ctx].
      symmetry.
      apply storeA_union_singleton_insert_fresh. exact Hfresh.
    }
    eapply basic_world_formula_fibvars_intro.
    - apply ctx_base_vars_lc.
    - rewrite ctx_base_vars_fv.
      rewrite dom_insert_L, atom_store_to_lvar_store_dom.
      rewrite lvars_fv_union, lvars_fv_singleton_free, lvars_fv_of_atoms.
      set_solver.
    - exact Hmfib_world.
  }
  assert (Hdomσ : dom (σΣ : StoreT) = dom Σ).
  {
    eapply res_fiber_from_projection_store_dom_of_subset; eauto.
  }
  assert (Hsingleton :
      (res_restrict mfib (dom Σ) : WorldT) = singleton_world σΣ).
  {
    eapply res_restrict_fiber_from_projection_eq_singleton; eauto.
  }
  eapply res_models_FFibVars_singleton_elim; [| |exact Hmfib_fib].
  - rewrite ctx_base_vars_fv. exact Hdomσ.
  - rewrite ctx_base_vars_fv. exact Hsingleton.
Qed.

Lemma denot_ctx_under_bind_projected_body_from_result_denotation
    (Σbase Σ : gmap atom ty) (τ1 : context_ty) e1
    (m mx mfib : WfWorldT) (Fx : FiberExtensionT)
    (x : atom) (σΣ : StoreT) :
  context_typing_wf_erased Σbase Σ e1 τ1 ->
  x ∉ dom Σ ->
  expr_result_extension_witness e1 x Fx ->
  res_extend_by m Fx mx ->
  m ⊨ basic_world_formula (atom_env_to_lty_env Σ) ->
  (forall σsrc msrc,
    res_fiber_from_projection m (dom Σ) σsrc msrc ->
    msrc ⊨ denot_ty_lvar_gas (cty_depth τ1)
      (atom_env_to_lty_env Σ) τ1 e1) ->
  res_fiber_from_projection mx (dom Σ) σΣ mfib ->
  mfib ⊨ formula_msubst_store σΣ
    (FAnd
      (basic_world_formula
          (atom_env_to_lty_env (erase_ctx_under Σ (CtxBind x τ1))))
      (denot_ty (<[x := erase_ty τ1]> Σ) τ1 (tret (vfvar x)))).
Proof.
  intros Hwf Hfresh HFx Hext Hworld Hsource Hproj.
  change (mfib ⊨
    FAnd
      (formula_msubst_store σΣ
        (basic_world_formula
          (atom_env_to_lty_env (erase_ctx_under Σ (CtxBind x τ1)))))
      (formula_msubst_store σΣ
        (denot_ty (<[x := erase_ty τ1]> Σ) τ1 (tret (vfvar x))))).
  rewrite res_models_and_iff. split.
  - eapply denot_ctx_under_bind_projected_body_basic_world_source_fiber; eauto.
  - eapply denot_ctx_under_bind_projected_body_arg_denotation; eauto.
Qed.

Lemma denot_ctx_under_bind_from_result_denotation
    (Σbase Σ : gmap atom ty) (τ1 : context_ty) e1
    (m mx : WfWorldT) (Fx : FiberExtensionT) (x : atom) :
  context_typing_wf_erased Σbase Σ e1 τ1 ->
  x ∉ dom Σ ->
  expr_result_extension_witness e1 x Fx ->
  res_extend_by m Fx mx ->
  m ⊨ basic_world_formula (atom_env_to_lty_env Σ) ->
  (forall σsrc msrc,
    res_fiber_from_projection m (dom Σ) σsrc msrc ->
    msrc ⊨ denot_ty_lvar_gas (cty_depth τ1)
      (atom_env_to_lty_env Σ) τ1 e1) ->
  mx ⊨ denot_ctx_under Σ (CtxBind x τ1).
Proof.
  intros Hwf Hfresh HFx Hext Hworld Hsource.
  eapply denot_ctx_under_bind_projection_intro.
  - eapply denot_ctx_under_bind_scope_from_result_denotation; eauto.
    eapply context_typing_wf_erased_context_ty_wf. exact Hwf.
  - intros σΣ mfib Hproj.
    eapply denot_ctx_under_bind_projected_body_from_result_denotation; eauto.
Qed.

Lemma denot_ctx_under_erased_fiber_from_basic_ctx
    (Σ : gmap atom ty) Γ
    (m mfib : WfWorldT) (σΔ : StoreT) :
  basic_ctx (dom Σ) Γ ->
  m ⊨ denot_ctx_under Σ Γ ->
  res_fiber_from_projection m (dom (erase_ctx_under Σ Γ)) σΔ mfib ->
  mfib ⊨ denot_ctx_under Σ Γ.
Proof.
Admitted.

Lemma denot_ctx_under_comma_bind_from_result_denotation
    (Σ : gmap atom ty) (Γ : ctx) (τ1 : context_ty) e1
    (m mx : WfWorldT) (Fx : FiberExtensionT) (x : atom) :
  context_typing_wf_erased Σ (erase_ctx_under Σ Γ) e1 τ1 ->
  m ⊨ denot_ctx_under Σ Γ ->
  (forall σΔ msrc,
    res_fiber_from_projection m (dom (erase_ctx_under Σ Γ)) σΔ msrc ->
    msrc ⊨ denot_ty_lvar_gas (cty_depth τ1)
      (atom_env_to_lty_env (erase_ctx_under Σ Γ)) τ1 e1) ->
  expr_result_extension_witness e1 x Fx ->
  x ∉ dom (erase_ctx_under Σ Γ) ->
  res_extend_by m Fx mx ->
  mx ⊨ denot_ctx_under Σ (CtxComma Γ (CtxBind x τ1)).
Proof.
  intros Hwf Hctx Hsource HFx Hfresh Hext.
  pose proof (denot_ctx_under_bind_from_result_denotation
    Σ (erase_ctx_under Σ Γ) τ1 e1 m mx Fx x Hwf Hfresh HFx Hext
    (denot_ctx_under_basic_world Σ Γ m Hctx) Hsource)
    as Hbind.
  eapply denot_ctx_under_comma_bind_from_fibered_arg_denotation; eauto.
  eapply res_models_extend_mono; [exact Hext | exact Hctx].
Qed.

Lemma denot_ty_in_ctx_under_star_bind_to_lvar_insert
    (Σ : gmap atom ty) Γ τx τ e y (m : WfWorldT) :
  y ∉ dom (erase_ctx Γ) ->
  m ⊨ denot_ty_in_ctx_under Σ (CtxStar Γ (CtxBind y τx)) τ e ->
  m ⊨ denot_ty_lvar_gas (cty_depth τ)
    (<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ)))
    τ e.
Proof.
  intros Hy Hden.
  unfold denot_ty_in_ctx_under, denot_ty in Hden |- *.
  assert (Henv :
      erase_ctx (CtxStar Γ (CtxBind y τx)) =
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

Lemma denot_ctx_under_star_elim_singleton
    (Σ : gmap atom ty) Γ1 Γ2 (m : WfWorldT) (σΣ : StoreT) :
  dom σΣ = dom Σ ->
  (res_restrict m (dom Σ) : WorldT) = singleton_world σΣ ->
  m ⊨ denot_ctx_under Σ (CtxStar Γ1 Γ2) ->
  exists (m1 m2 : WfWorldT) (Hc : world_compat m1 m2),
    res_product m1 m2 Hc ⊑ m /\
    m1 ⊨ denot_ctx_under Σ Γ1 /\
    m2 ⊨ denot_ctx_under Σ Γ2.
Proof.
  intros _ _ Hctx.
  cbn [denot_ctx_under] in Hctx.
  rewrite res_models_and_iff in Hctx.
  apply res_models_star_iff.
  exact (proj2 Hctx).
Qed.

Lemma denot_ctx_under_sum_elim_singleton
    (Σ : gmap atom ty) Γ1 Γ2 (m : WfWorldT) (σΣ : StoreT) :
  dom σΣ = dom Σ ->
  (res_restrict m (dom Σ) : WorldT) = singleton_world σΣ ->
  m ⊨ denot_ctx_under Σ (CtxSum Γ1 Γ2) ->
  exists (m1 m2 : WfWorldT) (Hdef : raw_sum_defined m1 m2),
    res_sum m1 m2 Hdef ⊑ m /\
    m1 ⊨ denot_ctx_under Σ Γ1 /\
    m2 ⊨ denot_ctx_under Σ Γ2.
Proof.
  intros _ _ Hctx.
  cbn [denot_ctx_under] in Hctx.
  rewrite res_models_and_iff in Hctx.
  apply res_models_plus_iff.
  exact (proj2 Hctx).
Qed.

Lemma denot_ctx_under_star_elim_in_fiber
    (Σ : gmap atom ty) Γ1 Γ2 (m mfib : WfWorldT) (σΣ : StoreT) :
  res_fiber_from_projection m (dom Σ) σΣ mfib ->
  m ⊨ denot_ctx_under Σ (CtxStar Γ1 Γ2) ->
  exists (m1 m2 : WfWorldT) (Hc : world_compat m1 m2),
    res_product m1 m2 Hc ⊑ mfib /\
    m1 ⊨ denot_ctx_under Σ Γ1 /\
    m2 ⊨ denot_ctx_under Σ Γ2.
Proof.
  (* Compatibility obligation for old fiberwise star decomposition. *)
Admitted.

Lemma denot_ctx_under_sum_elim_in_fiber
    (Σ : gmap atom ty) Γ1 Γ2 (m mfib : WfWorldT) (σΣ : StoreT) :
  res_fiber_from_projection m (dom Σ) σΣ mfib ->
  m ⊨ denot_ctx_under Σ (CtxSum Γ1 Γ2) ->
  exists (m1 m2 : WfWorldT) (Hdef : raw_sum_defined m1 m2),
    res_sum m1 m2 Hdef ⊑ mfib /\
    m1 ⊨ denot_ctx_under Σ Γ1 /\
    m2 ⊨ denot_ctx_under Σ Γ2.
Proof.
  (* Compatibility obligation for old fiberwise sum decomposition. *)
Admitted.

Lemma denot_ty_lvar_gas_star_union_to_ctx
    (Σ : gmap atom ty) Γ1 Γ2 τ e (m : WfWorldT) :
  m ⊨ denot_ty_lvar_gas (cty_depth τ)
    (atom_env_to_lty_env (erase_ctx Γ1) ∪
     atom_env_to_lty_env (erase_ctx Γ2)) τ e ->
  m ⊨ denot_ty_in_ctx_under Σ (CtxStar Γ1 Γ2) τ e.
Proof.
  intros Hden.
  unfold denot_ty_in_ctx_under, denot_ty in *.
  cbn [erase_ctx].
  rewrite <- atom_store_to_lvar_store_union in Hden.
  exact Hden.
Qed.

Lemma atom_env_to_lty_env_erase_ctx_under_star
    (Σ : gmap atom ty) Γ1 Γ2 :
  atom_env_to_lty_env (erase_ctx_under Σ (CtxStar Γ1 Γ2)) =
  atom_env_to_lty_env (erase_ctx_under Σ Γ1) ∪
  atom_env_to_lty_env (erase_ctx_under Σ Γ2).
Proof.
  unfold erase_ctx_under.
  cbn [erase_ctx].
  rewrite <- atom_store_to_lvar_store_union.
  f_equal.
  apply map_eq. intros x.
  unfold store_union.
  rewrite !lookup_union.
  destruct ((Σ : gmap atom ty) !! x) as [TΣ|] eqn:HΣ;
    destruct ((erase_ctx Γ1 : gmap atom ty) !! x) as [T1|] eqn:H1;
    destruct ((erase_ctx Γ2 : gmap atom ty) !! x) as [T2|] eqn:H2;
    reflexivity.
Qed.

Lemma denot_ty_lvar_gas_sum_left_to_ctx
    (Σ : gmap atom ty) Γ1 Γ2 τ e (m : WfWorldT) :
  m ⊨ denot_ty_lvar_gas (cty_depth τ)
    (atom_env_to_lty_env (erase_ctx_under Σ Γ1)) τ e ->
  m ⊨ denot_ty_lvar_gas (cty_depth τ)
    (atom_env_to_lty_env (erase_ctx_under Σ (CtxSum Γ1 Γ2))) τ e.
Proof.
  unfold erase_ctx_under. cbn [erase_ctx]. auto.
Qed.

Lemma denot_ty_lvar_gas_sum_right_to_ctx
    (Σ : gmap atom ty) Γ1 Γ2 τ e (m : WfWorldT) :
  erase_ctx Γ1 = erase_ctx Γ2 ->
  m ⊨ denot_ty_lvar_gas (cty_depth τ)
    (atom_env_to_lty_env (erase_ctx_under Σ Γ2)) τ e ->
  m ⊨ denot_ty_lvar_gas (cty_depth τ)
    (atom_env_to_lty_env (erase_ctx_under Σ (CtxSum Γ1 Γ2))) τ e.
Proof.
  intros Herase Hden.
  unfold erase_ctx_under. cbn [erase_ctx].
  rewrite Herase.
  exact Hden.
Qed.

Lemma basic_typing_star_union_lty_env
    (Σ : gmap atom ty) Γ1 Γ2 e T :
  erase_ctx_under Σ (CtxStar Γ1 Γ2) ⊢ₑ e ⋮ T ->
  lty_env_to_atom_env
    (atom_env_to_lty_env (erase_ctx_under Σ Γ1) ∪
     atom_env_to_lty_env (erase_ctx_under Σ Γ2)) ⊢ₑ e ⋮ T.
Proof.
  intros Hbasic.
  unfold erase_ctx_under in *.
  cbn [erase_ctx] in *.
  rewrite <- atom_store_to_lvar_store_union.
  rewrite lvar_store_to_atom_store_atom_store.
  replace ((Σ ∪ erase_ctx Γ1) ∪ (Σ ∪ erase_ctx Γ2) : gmap atom ty)
    with (Σ ∪ (erase_ctx Γ1 ∪ erase_ctx Γ2) : gmap atom ty).
  - exact Hbasic.
  - apply map_eq. intros x.
    unfold store_union.
    rewrite !lookup_union.
    destruct ((Σ : gmap atom ty) !! x) as [TΣ|] eqn:HΣ;
      destruct ((erase_ctx Γ1 : gmap atom ty) !! x) as [T1|] eqn:H1;
      destruct ((erase_ctx Γ2 : gmap atom ty) !! x) as [T2|] eqn:H2;
      reflexivity.
Qed.

Lemma letd_body_world_compat
    e1 x (m1 m2 mx1 : WfWorldT) (Hc : world_compat m1 m2)
    (Fx : FiberExtensionT) :
  expr_result_extension_witness e1 x Fx ->
  x ∉ world_dom (m2 : WorldT) ->
  res_extend_by m1 Fx mx1 ->
  world_compat m2 mx1.
Proof.
  intros HFx Hx Hext.
  assert (Hout : ext_out Fx ## world_dom (m2 : WorldT)).
  {
    destruct HFx as [_ [_ Hout] _].
    unfold ext_out in *. rewrite Hout. set_solver.
  }
  assert (Hc_sym : world_compat m2 m1).
  {
    intros σ2 σ1 Hσ2 Hσ1.
    apply storeA_compat_sym. exact (Hc σ1 σ2 Hσ1 Hσ2).
  }
  pose proof (world_compat_restrict_l_extend_by_fresh
    m2 m1 mx1 Fx (world_dom (m2 : WorldT)) Hout Hext Hc_sym) as Hcompat.
  rewrite (res_restrict_eq_of_le m2 m2 ltac:(reflexivity)) in Hcompat.
  exact Hcompat.
Qed.

End ContextDenotation.

#[global] Instance denot_cty_inst :
    Denotation context_ty (tm -> Formula (V := value)) :=
  fun τ e => denot_ty ∅ τ e.
#[global] Instance denot_ctx_inst :
    Denotation ctx (Formula (V := value)) := denot_ctx.
Arguments denot_cty_inst /.
Arguments denot_ctx_inst /.
