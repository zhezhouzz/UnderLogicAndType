(** * Denotation.Context

    Denotation of type contexts, expressed directly with the new recursive
    context-type denotation. *)

From Denotation Require Export Notation.
From Denotation Require Import ContextTypeDenotationSaturate.

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
  denot_ctx_under (erase_ctx Γ) Γ.

Definition denot_ty_under
    (Σ : gmap atom ty) (τ : context_ty) (e : tm) : FormulaT :=
  denot_ty Σ τ e.

Definition denot_ty_in_ctx (Γ : ctx) (τ : context_ty) (e : tm) : FormulaT :=
  denot_ty (erase_ctx Γ) τ e.

Definition denot_ty_in_ctx_under
    (Σ : gmap atom ty) (Γ : ctx) (τ : context_ty) (e : tm) : FormulaT :=
  denot_ty (erase_ctx_under Σ Γ) τ e.

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
  destruct Γ; cbn [denot_ctx_under]; rewrite res_models_and_iff; tauto.
Qed.

Lemma denot_ctx_under_bind_inv
    (Σ : gmap atom ty) x τ (m : WfWorldT) :
  m ⊨ denot_ctx_under Σ (CtxBind x τ) ->
  m ⊨ denot_ty (<[x := erase_ty τ]> Σ) τ (tret (vfvar x)).
Proof.
  cbn [denot_ctx_under].
  rewrite res_models_and_iff. tauto.
Qed.

Lemma denot_ctx_under_comma_inv
    (Σ : gmap atom ty) Γ1 Γ2 (m : WfWorldT) :
  m ⊨ denot_ctx_under Σ (CtxComma Γ1 Γ2) ->
  m ⊨ denot_ctx_under Σ Γ1 /\
  m ⊨ denot_ctx_under (Σ ∪ erase_ctx Γ1) Γ2.
Proof.
  cbn [denot_ctx_under].
  rewrite res_models_and_iff.
  intros [_ Hcomma].
  rewrite res_models_and_iff in Hcomma.
  exact Hcomma.
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

Lemma denot_ctx_under_comma_bind_from_arg_denotation
    (Σ : gmap atom ty) (Γ : ctx) (τx : context_ty) y
    (m my : WfWorldT) (F : FiberExtensionT) :
  y ∉ dom (erase_ctx_under Σ Γ) ->
  m ⊨ denot_ctx_under Σ Γ ->
  res_extend_by m F my ->
  my ⊨ denot_ty_lvar_gas (cty_depth τx)
    (<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx_under Σ Γ)))
    τx (tret (vfvar y)) ->
  my ⊨ denot_ctx_under Σ (CtxComma Γ (CtxBind y τx)).
Proof.
  intros Hy Hctx Hext Harg.
  set (ΣΓ := atom_env_to_lty_env (erase_ctx_under Σ Γ)).
  assert (HyΣΓ : LVFree y ∉ dom (ΣΓ : gmap logic_var ty)).
  {
    subst ΣΓ.
    rewrite atom_store_to_lvar_store_dom.
    unfold lvars_of_atoms.
    intros HyD. apply elem_of_map in HyD as [z [Hz HzD]].
    inversion Hz. subst z. exact (Hy HzD).
  }
  pose proof (res_models_extend_mono m F my
    (denot_ctx_under Σ Γ) Hext Hctx) as Hctx_my.
  pose proof (denot_ctx_under_basic_world Σ Γ my Hctx_my) as Hworld_old.
  assert (Hworld_insert :
    my ⊨ basic_world_formula (<[LVFree y := erase_ty τx]> ΣΓ)).
  {
    eapply basic_world_formula_insert_from_arg_denotation; eauto.
  }
  cbn [denot_ctx_under].
  rewrite res_models_and_iff. split.
  - subst ΣΓ.
    rewrite (erase_ctx_under_comma_bind_env_fresh Σ Γ y τx Hy).
    replace (atom_env_to_lty_env (<[y := erase_ty τx]> (erase_ctx_under Σ Γ)))
      with (<[LVFree y := erase_ty τx]>
        (atom_env_to_lty_env (erase_ctx_under Σ Γ))).
    {
      change (my ⊨ basic_world_formula
        (<[LVFree y := erase_ty τx]>
          (atom_env_to_lty_env (erase_ctx_under Σ Γ)))) in Hworld_insert.
      exact Hworld_insert.
    }
    { symmetry. apply atom_store_to_lvar_store_insert. }
  - rewrite res_models_and_iff. split.
    + exact Hctx_my.
    + cbn [denot_ctx_under].
      rewrite res_models_and_iff. split.
      * subst ΣΓ.
        unfold erase_ctx_under.
        cbn [erase_ctx].
        replace ((Σ ∪ erase_ctx Γ) ∪ {[y := erase_ty τx]} : gmap atom ty)
          with (<[y := erase_ty τx]> (Σ ∪ erase_ctx Γ : gmap atom ty)).
        2:{
          symmetry.
          apply (storeA_union_singleton_insert_fresh
            (V := ty) (K := atom)
            (Σ ∪ erase_ctx Γ : gmap atom ty) y (erase_ty τx)).
          exact Hy.
        }
        replace (atom_env_to_lty_env
            (<[y := erase_ty τx]> (Σ ∪ erase_ctx Γ : gmap atom ty)))
          with (<[LVFree y := erase_ty τx]>
            (atom_env_to_lty_env (erase_ctx_under Σ Γ))).
        -- exact Hworld_insert.
        -- unfold erase_ctx_under. symmetry. apply atom_store_to_lvar_store_insert.
      * subst ΣΓ.
        unfold denot_ty.
        replace (atom_env_to_lty_env (<[y := erase_ty τx]>
            (Σ ∪ erase_ctx Γ : gmap atom ty)))
          with (<[LVFree y := erase_ty τx]>
            (atom_env_to_lty_env (erase_ctx_under Σ Γ))).
        2:{
          unfold erase_ctx_under.
          symmetry. apply atom_store_to_lvar_store_insert.
        }
        exact Harg.
Qed.

Lemma denot_ctx_under_star_bind_from_arg_denotation
    (Σ : gmap atom ty) (Γ : ctx) (τx : context_ty) y
    (m marg : WfWorldT) (Hc : world_compat marg m) :
  y ∉ dom (erase_ctx_under Σ Γ) ->
  m ⊨ denot_ctx_under Σ Γ ->
  marg ⊨ denot_ty_lvar_gas (cty_depth τx)
    (<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx_under Σ Γ)))
    τx (tret (vfvar y)) ->
  res_product marg m Hc ⊨ denot_ctx_under Σ (CtxStar Γ (CtxBind y τx)).
Proof.
Admitted.

Lemma denot_ctx_under_star_bind_from_result_extension
    (Σ : gmap atom ty) Γ1 Γ τ1 e1 x
    (m2 m1 mx1 mbody : WfWorldT)
    (Hcbody : world_compat m2 mx1) (Fx : FiberExtensionT) :
  x ∉ dom (erase_ctx_under Σ Γ) ->
  m2 ⊨ denot_ctx_under Σ Γ ->
  m1 ⊨ denot_ty_in_ctx_under Σ Γ1 τ1 e1 ->
  expr_result_extension_witness e1 x Fx ->
  res_extend_by m1 Fx mx1 ->
  res_product m2 mx1 Hcbody ⊑ mbody ->
  mbody ⊨ denot_ctx_under Σ (CtxStar Γ (CtxBind x τ1)).
Proof.
Admitted.

Lemma denot_ctx_under_comma_bind_from_result_denotation
    (Σ : gmap atom ty) (Γ : ctx) (τ1 : context_ty) e1
    (m mx : WfWorldT) (Fx : FiberExtensionT) (x : atom) :
  m ⊨ denot_ctx_under Σ Γ ->
  m ⊨ denot_ty_in_ctx_under Σ Γ τ1 e1 ->
  expr_result_extension_witness e1 x Fx ->
  x ∉ dom (erase_ctx_under Σ Γ) ->
  res_extend_by m Fx mx ->
  mx ⊨ denot_ctx_under Σ (CtxComma Γ (CtxBind x τ1)).
Proof.
  intros Hctx Hden HFx Hfresh Hext.
  set (ΣΓ := atom_env_to_lty_env (erase_ctx_under Σ Γ)).
  assert (HxΣΓ : LVFree x ∉ dom (ΣΓ : gmap logic_var ty)).
  {
    subst ΣΓ.
    rewrite atom_store_to_lvar_store_dom.
    unfold lvars_of_atoms.
    intros HxD. apply elem_of_map in HxD as [z [Hz HzD]].
    inversion Hz. subst z. exact (Hfresh HzD).
  }
  unfold denot_ty_in_ctx_under, denot_ty in Hden.
  pose proof (denot_ty_lvar_gas_result_extension_to_var
    (cty_depth τ1) ΣΓ τ1 e1 x m mx Fx
    ltac:(subst ΣΓ; apply atom_store_to_lvar_store_closed)
    HxΣΓ HFx Hext Hden) as Harg.
  subst ΣΓ.
  eapply denot_ctx_under_comma_bind_from_arg_denotation; eauto.
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

Lemma denot_ctx_under_star_elim
    (Σ : gmap atom ty) Γ1 Γ2 (m : WfWorldT) :
  m ⊨ denot_ctx_under Σ (CtxStar Γ1 Γ2) ->
  exists (m1 m2 : WfWorldT) (Hc : world_compat m1 m2),
    res_product m1 m2 Hc ⊑ m /\
    m1 ⊨ denot_ctx_under Σ Γ1 /\
    m2 ⊨ denot_ctx_under Σ Γ2.
Proof.
  intros Hctx.
  cbn [denot_ctx_under] in Hctx.
  rewrite res_models_and_iff in Hctx.
  destruct Hctx as [_ Hstar].
  apply res_models_star_iff in Hstar as
    [m1 [m2 [Hc [Hle [HΓ1 HΓ2]]]]].
  exists m1, m2, Hc. repeat split; assumption.
Qed.

Lemma denot_ctx_under_sum_elim
    (Σ : gmap atom ty) Γ1 Γ2 (m : WfWorldT) :
  m ⊨ denot_ctx_under Σ (CtxSum Γ1 Γ2) ->
  exists (m1 m2 : WfWorldT) (Hdef : raw_sum_defined m1 m2),
    res_sum m1 m2 Hdef ⊑ m /\
    m1 ⊨ denot_ctx_under Σ Γ1 /\
    m2 ⊨ denot_ctx_under Σ Γ2.
Proof.
  intros Hctx.
  cbn [denot_ctx_under] in Hctx.
  rewrite res_models_and_iff in Hctx.
  destruct Hctx as [_ Hplus].
  apply res_models_plus_iff in Hplus as
    [m1 [m2 [Hdef [Hle [HΓ1 HΓ2]]]]].
  exists m1, m2, Hdef. repeat split; assumption.
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
