(** * Denotation.Context

    Denotation of type contexts, expressed directly with the new recursive
    context-type denotation. *)

From Denotation Require Export Notation.
From Denotation Require Import ContextTypeDenotationSaturate.

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
  FFibVars (ctx_base_vars Σ)
    (FAnd (basic_world_formula (atom_env_to_lty_env (erase_ctx_under Σ Γ)))
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
      end)).

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
  denot_ctx_under Σ Γ =
  FFibVars (ctx_base_vars Σ) (denot_ctx_under_body Σ Γ).
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
  denot_ty (erase_ctx_under Σ Γ) τ e.

Definition denot_ty_in_ctx_under_fiber
    (Σ : gmap atom ty) (Γ : ctx) (τ : context_ty) (e : tm) : FormulaT :=
  FFibVars (ctx_base_vars Σ) (denot_ty_in_ctx_under Σ Γ τ e).

Lemma denot_ty_in_ctx_under_fiber_intro
    (Σ : gmap atom ty) Γ τ e (m : WfWorldT) :
  formula_scoped_in_world m (denot_ty_in_ctx_under_fiber Σ Γ τ e) ->
  (forall σΣ mfib,
    res_fiber_from_projection m (dom Σ) σΣ mfib ->
    mfib ⊨ formula_msubst_store σΣ (denot_ty_in_ctx_under Σ Γ τ e)) ->
  m ⊨ denot_ty_in_ctx_under_fiber Σ Γ τ e.
Proof.
  intros Hscope Hfib.
  unfold denot_ty_in_ctx_under_fiber.
  eapply res_models_FFibVars_intro.
  - exact Hscope.
  - apply ctx_base_vars_lc.
  - intros σΣ mfib Hproj.
    apply Hfib. rewrite <- ctx_base_vars_fv. exact Hproj.
Qed.

Lemma denot_ty_in_ctx_under_fiber_elim_projection
    (Σ : gmap atom ty) Γ τ e (m mfib : WfWorldT) (σΣ : StoreT) :
  res_fiber_from_projection m (dom Σ) σΣ mfib ->
  m ⊨ denot_ty_in_ctx_under_fiber Σ Γ τ e ->
  mfib ⊨ formula_msubst_store σΣ (denot_ty_in_ctx_under Σ Γ τ e).
Proof.
  intros Hproj Hden.
  unfold denot_ty_in_ctx_under_fiber in Hden.
  pose proof (res_models_scoped _ _ Hden) as Hscope.
  pose proof (proj1 (res_models_FFibVars_iff _ _ _ Hscope) Hden)
    as [_ Hfib].
  apply Hfib. rewrite ctx_base_vars_fv. exact Hproj.
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
  eapply basic_world_formula_fibvars_elim.
  all: eapply res_models_FFibVars_and_l; exact Hctx.
Qed.

Lemma denot_ctx_under_comma_inv
    (Σ : gmap atom ty) Γ1 Γ2 (m : WfWorldT) :
  m ⊨ denot_ctx_under Σ (CtxComma Γ1 Γ2) ->
  m ⊨ denot_ctx_under Σ Γ1 /\
  m ⊨ denot_ctx_under (Σ ∪ erase_ctx Γ1) Γ2.
Proof.
  intros Hctx.
  cbn [denot_ctx_under] in Hctx.
  pose proof (res_models_FFibVars_and_r _ _ _ _ Hctx) as Hcomma.
  split.
  - pose proof (res_models_FFibVars_and_l _ _ _ _ Hcomma) as Hleft.
    destruct Γ1; cbn [denot_ctx_under] in Hleft |- *.
    all:
      eapply res_models_FFibVars_nested_elim;
      [unfold ctx_base_vars; rewrite !lvars_fv_of_atoms; set_solver
      | exact Hleft].
  - pose proof (res_models_FFibVars_and_r _ _ _ _ Hcomma) as Hright.
    destruct Γ2; cbn [denot_ctx_under] in Hright |- *.
    all:
      eapply res_models_FFibVars_nested_elim; [| exact Hright].
    all: unfold ctx_base_vars; rewrite !lvars_fv_of_atoms; set_solver.
Qed.

Lemma denot_ctx_under_projected_body
    (Σ : gmap atom ty) Γ (m mfib : WfWorldT) (σΣ : StoreT) :
  res_fiber_from_projection m (dom Σ) σΣ mfib ->
  m ⊨ denot_ctx_under Σ Γ ->
  mfib ⊨ formula_msubst_store σΣ (denot_ctx_under_body Σ Γ).
Proof.
  intros Hproj Hctx.
  rewrite denot_ctx_under_unfold_body in Hctx.
  pose proof (res_models_scoped _ _ Hctx) as Hscope.
  pose proof (proj1 (res_models_FFibVars_iff _ _ _ Hscope) Hctx)
    as [_ Hfib].
  apply Hfib.
  rewrite ctx_base_vars_fv. exact Hproj.
Qed.

Lemma denot_ctx_under_fiber_from_projection
    (Σ : gmap atom ty) Γ (m mfib : WfWorldT) (σΣ : StoreT) :
  res_fiber_from_projection m (dom Σ) σΣ mfib ->
  m ⊨ denot_ctx_under Σ Γ ->
  mfib ⊨ denot_ctx_under Σ Γ.
Proof.
  intros Hproj Hctx.
  destruct Γ; cbn [denot_ctx_under] in Hctx |- *.
  all: (
    pose proof (res_models_scoped _ _ Hctx) as Hscope;
    pose proof (proj1 (res_models_FFibVars_iff _ _ _ Hscope) Hctx)
      as [Hlc Hfib];
    assert (HprojD :
        res_fiber_from_projection m (lvars_fv (ctx_base_vars Σ)) σΣ mfib)
      by (rewrite ctx_base_vars_fv; exact Hproj);
    pose proof (Hfib σΣ mfib HprojD) as Hbody;
    assert (Hdomσ : dom σΣ = lvars_fv (ctx_base_vars Σ)) by (
      rewrite ctx_base_vars_fv;
      destruct Hproj as [HσΣ _];
      pose proof (wfworld_store_dom (res_restrict m (dom Σ)) σΣ HσΣ)
        as Hdom;
      simpl in Hdom;
      change (dom (σΣ : StoreT) = world_dom (m : WorldT) ∩ dom Σ) in Hdom;
      apply formula_scoped_fibvars_l in Hscope;
      rewrite ctx_base_vars_fv in Hscope;
      rewrite Hdom; set_solver);
    assert (Hsingleton :
        (res_restrict mfib (lvars_fv (ctx_base_vars Σ)) : WorldT) =
        singleton_world σΣ) by (
      rewrite ctx_base_vars_fv;
      eapply res_restrict_fiber_from_projection_eq_singleton; eauto;
      rewrite <- ctx_base_vars_fv; exact Hdomσ);
    eapply res_models_FFibVars_singleton_intro;
    [ eapply formula_scoped_FFibVars_from_singleton_msubst; eauto;
      eapply res_models_scoped; exact Hbody
    | exact Hlc
    | exact Hdomσ
    | exact Hsingleton
    | exact Hbody ]).
Qed.

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
  ty_env_agree_on X (erase_ctx_under Σ Γsrc) (erase_ctx_under Σ Γdst) ->
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
  y ∉ dom (erase_ctx_under Σ Γ) ->
  m ⊨ denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind y τx)) τ e ->
  m ⊨ denot_ty_lvar_gas (cty_depth τ)
    (<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx_under Σ Γ)))
    τ e.
Proof.
  intros Hy Hden.
  unfold denot_ty_in_ctx_under, denot_ty in Hden |- *.
  rewrite (erase_ctx_under_comma_bind_env_fresh Σ Γ y τx Hy) in Hden.
  replace (<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx_under Σ Γ)))
    with (atom_env_to_lty_env
      (<[y := erase_ty τx]> (erase_ctx_under Σ Γ))).
  2:{ apply atom_store_to_lvar_store_insert. }
  exact Hden.
Qed.

Lemma denot_ty_in_ctx_under_star_bind_to_lvar_insert
    (Σ : gmap atom ty) Γ τx τ e y (m : WfWorldT) :
  y ∉ dom (erase_ctx_under Σ Γ) ->
  m ⊨ denot_ty_in_ctx_under Σ (CtxStar Γ (CtxBind y τx)) τ e ->
  m ⊨ denot_ty_lvar_gas (cty_depth τ)
    (<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx_under Σ Γ)))
    τ e.
Proof.
  intros Hy Hden.
  unfold denot_ty_in_ctx_under, denot_ty in Hden |- *.
  rewrite (erase_ctx_under_star_bind_env_fresh Σ Γ y τx Hy) in Hden.
  replace (<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx_under Σ Γ)))
    with (atom_env_to_lty_env
      (<[y := erase_ty τx]> (erase_ctx_under Σ Γ))).
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
  intros HdomσΣ Hsingleton Hctx.
  cbn [denot_ctx_under] in Hctx.
  pose proof (res_models_FFibVars_and_r _ _ _ _ Hctx) as Hstar.
  assert (HdomD : dom σΣ = lvars_fv (ctx_base_vars Σ)).
  { rewrite ctx_base_vars_fv. exact HdomσΣ. }
  assert (HsingletonD :
      (res_restrict m (lvars_fv (ctx_base_vars Σ)) : WorldT) =
      singleton_world σΣ).
  { rewrite ctx_base_vars_fv. exact Hsingleton. }
  destruct Γ1; destruct Γ2; cbn [denot_ctx_under] in Hstar |- *.
  all: destruct (res_models_FFibVars_star_elim_shared_singleton
      m (ctx_base_vars Σ) _ _ σΣ HdomD HsingletonD Hstar)
      as [m1 [m2 [Hc [Hle [HΓ1 HΓ2]]]]];
    exists m1, m2, Hc;
    split; [exact Hle | split; [exact HΓ1 | exact HΓ2]].
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
  intros HdomσΣ Hsingleton Hctx.
  cbn [denot_ctx_under] in Hctx.
  pose proof (res_models_FFibVars_and_r _ _ _ _ Hctx) as Hplus.
  assert (HdomD : dom σΣ = lvars_fv (ctx_base_vars Σ)).
  { rewrite ctx_base_vars_fv. exact HdomσΣ. }
  assert (HsingletonD :
      (res_restrict m (lvars_fv (ctx_base_vars Σ)) : WorldT) =
      singleton_world σΣ).
  { rewrite ctx_base_vars_fv. exact Hsingleton. }
  destruct Γ1; destruct Γ2; cbn [denot_ctx_under] in Hplus |- *.
  all: destruct (res_models_FFibVars_plus_elim_shared_singleton
      m (ctx_base_vars Σ) _ _ σΣ HdomD HsingletonD Hplus)
      as [m1 [m2 [Hdef [Hle [HΓ1 HΓ2]]]]];
    exists m1, m2, Hdef;
    split; [exact Hle | split; [exact HΓ1 | exact HΓ2]].
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
  intros Hproj Hctx.
  pose proof (denot_ctx_under_fiber_from_projection
    Σ (CtxStar Γ1 Γ2) m mfib σΣ Hproj Hctx) as Hfib_ctx.
  assert (Hdomσ : dom σΣ = dom Σ).
  {
    destruct Hproj as [HσΣ _].
    pose proof (wfworld_store_dom (res_restrict m (dom Σ)) σΣ HσΣ)
      as Hdom.
    simpl in Hdom.
    change (dom (σΣ : StoreT) = world_dom (m : WorldT) ∩ dom Σ) in Hdom.
    pose proof (res_models_scoped _ _ Hctx) as Hscope.
    cbn [denot_ctx_under] in Hscope.
    apply formula_scoped_fibvars_l in Hscope.
    rewrite ctx_base_vars_fv in Hscope.
    rewrite Hdom. set_solver.
  }
  assert (Hsingleton :
      (res_restrict mfib (dom Σ) : WorldT) = singleton_world σΣ).
  {
    eapply res_restrict_fiber_from_projection_eq_singleton; eauto.
  }
  eapply denot_ctx_under_star_elim_singleton; eauto.
Qed.

Lemma denot_ctx_under_sum_elim_in_fiber
    (Σ : gmap atom ty) Γ1 Γ2 (m mfib : WfWorldT) (σΣ : StoreT) :
  res_fiber_from_projection m (dom Σ) σΣ mfib ->
  m ⊨ denot_ctx_under Σ (CtxSum Γ1 Γ2) ->
  exists (m1 m2 : WfWorldT) (Hdef : raw_sum_defined m1 m2),
    res_sum m1 m2 Hdef ⊑ mfib /\
    m1 ⊨ denot_ctx_under Σ Γ1 /\
    m2 ⊨ denot_ctx_under Σ Γ2.
Proof.
  intros Hproj Hctx.
  pose proof (denot_ctx_under_fiber_from_projection
    Σ (CtxSum Γ1 Γ2) m mfib σΣ Hproj Hctx) as Hfib_ctx.
  assert (Hdomσ : dom σΣ = dom Σ).
  {
    destruct Hproj as [HσΣ _].
    pose proof (wfworld_store_dom (res_restrict m (dom Σ)) σΣ HσΣ)
      as Hdom.
    simpl in Hdom.
    change (dom (σΣ : StoreT) = world_dom (m : WorldT) ∩ dom Σ) in Hdom.
    pose proof (res_models_scoped _ _ Hctx) as Hscope.
    cbn [denot_ctx_under] in Hscope.
    apply formula_scoped_fibvars_l in Hscope.
    rewrite ctx_base_vars_fv in Hscope.
    rewrite Hdom. set_solver.
  }
  assert (Hsingleton :
      (res_restrict mfib (dom Σ) : WorldT) = singleton_world σΣ).
  {
    eapply res_restrict_fiber_from_projection_eq_singleton; eauto.
  }
  eapply denot_ctx_under_sum_elim_singleton; eauto.
Qed.

Lemma denot_ty_lvar_gas_star_union_to_ctx
    (Σ : gmap atom ty) Γ1 Γ2 τ e (m : WfWorldT) :
  m ⊨ denot_ty_lvar_gas (cty_depth τ)
    (atom_env_to_lty_env (erase_ctx_under Σ Γ1) ∪
     atom_env_to_lty_env (erase_ctx_under Σ Γ2)) τ e ->
  m ⊨ denot_ty_in_ctx_under Σ (CtxStar Γ1 Γ2) τ e.
Proof.
  intros Hden.
  unfold denot_ty_in_ctx_under, denot_ty, erase_ctx_under in *.
  cbn [erase_ctx].
  rewrite <- atom_store_to_lvar_store_union in Hden.
  replace ((Σ ∪ erase_ctx Γ1) ∪ (Σ ∪ erase_ctx Γ2) : gmap atom ty)
    with (Σ ∪ (erase_ctx Γ1 ∪ erase_ctx Γ2) : gmap atom ty) in Hden.
  - exact Hden.
  - apply map_eq. intros x.
    unfold store_union.
    rewrite !lookup_union.
    destruct ((Σ : gmap atom ty) !! x) as [TΣ|] eqn:HΣ;
      destruct ((erase_ctx Γ1 : gmap atom ty) !! x) as [T1|] eqn:H1;
      destruct ((erase_ctx Γ2 : gmap atom ty) !! x) as [T2|] eqn:H2;
	      reflexivity.
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
