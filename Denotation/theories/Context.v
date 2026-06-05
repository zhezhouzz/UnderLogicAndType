(** * Denotation.Context

    Denotation of type contexts, expressed directly with the new recursive
    context-type denotation. *)

From Denotation Require Export Notation TypeDenoteOpen.
From Denotation Require Import TypeEquivCore.

Section ContextDenotation.

Definition ctx_erasure_under (Σ : gmap atom ty) (Γ : ctx) : gmap atom ty :=
  store_restrict Σ (ctx_fv Γ) ∪ erase_ctx Γ.

Fixpoint ctx_denote_under (Σ : gmap atom ty) (Γ : ctx) : FormulaT :=
  let Σ' := store_restrict Σ (ctx_fv Γ) in
  FAnd (basic_world_formula (atom_env_to_lty_env (Σ' ∪ erase_ctx Γ)))
    (match Γ with
    | CtxEmpty =>
        FTrue
    | CtxBind x τ =>
        ty_denote (<[x := erase_ty τ]> Σ') τ (tret (vfvar x))
    | CtxComma Γ1 Γ2 =>
        FAnd
          (ctx_denote_under Σ' Γ1)
          (ctx_denote_under (Σ' ∪ erase_ctx Γ1) Γ2)
    | CtxStar Γ1 Γ2 =>
        FStar (ctx_denote_under Σ' Γ1) (ctx_denote_under Σ' Γ2)
    | CtxSum Γ1 Γ2 =>
        FPlus (ctx_denote_under Σ' Γ1) (ctx_denote_under Σ' Γ2)
    end).

Definition ctx_denote (Γ : ctx) : FormulaT :=
  ctx_denote_under ∅ Γ.

Definition ty_denote_under
    (Σ : gmap atom ty) (Γ : ctx) (τ : context_ty) (e : tm) : FormulaT :=
  ty_denote (erase_ctx Γ) τ e.

Definition ty_env_agree_on (X : aset) (Σ1 Σ2 : gmap atom ty) : Prop :=
  forall x, x ∈ X -> Σ1 !! x = Σ2 !! x.

Lemma ctx_erasure_under_minimal Σ Γ :
  ctx_erasure_under Σ Γ =
  ctx_erasure_under (store_restrict Σ (ctx_fv Γ)) Γ.
Proof.
  unfold ctx_erasure_under.
  rewrite storeA_restrict_twice_same.
  reflexivity.
Qed.

Lemma ctx_denote_under_minimal Σ Γ :
  ctx_denote_under Σ Γ =
  ctx_denote_under (store_restrict Σ (ctx_fv Γ)) Γ.
Proof.
  destruct Γ; cbn [ctx_denote_under ctx_fv].
  all: rewrite storeA_restrict_twice_same; reflexivity.
Qed.

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
  m ⊨ ty_denote
    (<[x := erase_ty τ]> (store_restrict Σ (ctx_fv (CtxBind x τ))))
    τ (tret (vfvar x)).
Proof.
  intros Hctx.
  cbn [ctx_denote_under] in Hctx.
  rewrite res_models_and_iff in Hctx.
  exact (proj2 Hctx).
Qed.

Lemma relevant_env_ctx_erasure_under_subenv
    (Σ : gmap atom ty) Γ τ e v T :
  basic_ctx (dom Σ) Γ ->
  relevant_env (atom_env_to_lty_env (erase_ctx Γ)) τ e !! v = Some T ->
  atom_env_to_lty_env (ctx_erasure_under Σ Γ) !! v = Some T.
Proof.
  intros Hbasic Hlook.
  unfold relevant_env, lty_env_restrict_lvars in Hlook.
  apply storeA_restrict_lookup_some in Hlook as [_ Hlook].
  destruct v as [k|x].
  - rewrite atom_store_to_lvar_store_lookup_bound_none in Hlook.
    discriminate.
  - rewrite atom_store_to_lvar_store_lookup_free in Hlook.
    rewrite atom_store_to_lvar_store_lookup_free.
    unfold ctx_erasure_under.
    apply map_lookup_union_Some_raw. right. split.
    + apply storeA_restrict_lookup_none_l.
      apply not_elem_of_dom. intros HΣx.
      pose proof (basic_ctx_erase_dom (dom Σ) Γ Hbasic) as HdomΓ.
      pose proof (basic_ctx_dom_fresh (dom Σ) Γ Hbasic) as HfreshΓ.
      apply elem_of_dom_2 in Hlook.
      rewrite HdomΓ in Hlook.
      set_solver.
    + exact Hlook.
Qed.

Lemma erase_ctx_lookup_ctx_erasure_under_of_basic_ctx
    (Σ : gmap atom ty) Γ x :
  basic_ctx (dom Σ) Γ ->
  x ∈ dom (erase_ctx Γ) ->
  (erase_ctx Γ : gmap atom ty) !! x =
  (ctx_erasure_under Σ Γ : gmap atom ty) !! x.
Proof.
  intros Hbasic HxΓ.
  unfold ctx_erasure_under.
  symmetry.
  apply lookup_union_r.
  apply storeA_restrict_lookup_none_l.
  apply not_elem_of_dom. intros HΣx.
  pose proof (basic_ctx_erase_dom (dom Σ) Γ Hbasic) as HdomΓ.
  pose proof (basic_ctx_dom_fresh (dom Σ) Γ Hbasic) as HfreshΓ.
  rewrite HdomΓ in HxΓ.
  set_solver.
Qed.

Lemma basic_world_insert_of_arg
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
    eapply lty_singleton_subenv_relevant_ret.
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
    (relevant_lvars_basic_ret_fvar_subset x τ Hbasic)
    (atom_env_restrict_singleton_lookup
      Σ x (erase_ty τ) Hlookup)
    Harg) as Harg_single.
  unfold ctx_denote.
  change (m ⊨ ctx_denote_under (∅ : gmap atom ty) (CtxBind x τ)).
  cbn [ctx_denote_under].
  rewrite res_models_and_iff. split.
  - replace (store_restrict (∅ : gmap atom ty) (ctx_fv (CtxBind x τ)) ∪
        erase_ctx (CtxBind x τ))
      with (<[x := erase_ty τ]> (∅ : gmap atom ty)).
    2:{
      cbn [ctx_fv erase_ctx].
      unfold storeA_restrict, map_restrict.
      unfold store_union, store_singleton, store_empty.
      rewrite map_filter_empty.
      rewrite map_empty_union.
      reflexivity.
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
    eapply basic_world_insert_of_arg
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

Lemma ctx_denote_under_comma_right_minimal
    (Σ : gmap atom ty) Γ1 Γ2 (m : WfWorldT) :
  basic_ctx (dom Σ) Γ1 ->
  m ⊨ ctx_denote_under (Σ ∪ erase_ctx Γ1) Γ2 ->
  m ⊨ ctx_denote_under
    (store_restrict Σ (ctx_fv (CtxComma Γ1 Γ2)) ∪ erase_ctx Γ1) Γ2.
Proof.
  intros Hbasic Hctx.
  pose proof (basic_ctx_erase_dom (dom Σ) Γ1 Hbasic) as Hdom1.
  pose proof (basic_ctx_dom_fresh (dom Σ) Γ1 Hbasic) as Hfresh1.
  rewrite ctx_denote_under_minimal.
  rewrite ctx_denote_under_minimal in Hctx.
  replace (store_restrict
      (store_restrict Σ (ctx_fv (CtxComma Γ1 Γ2)) ∪ erase_ctx Γ1)
      (ctx_fv Γ2))
    with (store_restrict (Σ ∪ erase_ctx Γ1) (ctx_fv Γ2)).
  - exact Hctx.
  - apply storeA_map_eq. intros x.
    rewrite !storeA_restrict_lookup.
    destruct (decide (x ∈ ctx_fv Γ2)) as [HxΓ2|HxΓ2];
      [|reflexivity].
    destruct ((erase_ctx Γ1 : gmap atom ty) !! x) as [T1|] eqn:Hx1.
    + assert (Hxdom1 : x ∈ ctx_dom Γ1).
      {
        rewrite <- Hdom1.
        apply elem_of_dom. eauto.
      }
      assert (HΣnone : Σ !! x = None).
      {
        apply not_elem_of_dom. intros HxΣ.
        set_solver.
      }
      assert (Hrestrict_none :
          (store_restrict Σ (ctx_fv (CtxComma Γ1 Γ2)) : gmap atom ty)
            !! x = None).
      { apply storeA_restrict_lookup_none_l. exact HΣnone. }
      transitivity (Some T1).
      * apply map_lookup_union_Some_raw. right. split; [exact HΣnone|exact Hx1].
      * symmetry. apply map_lookup_union_Some_raw. right. split; [exact Hrestrict_none|exact Hx1].
    + assert (Hxnotdom1 : x ∉ ctx_dom Γ1).
      {
        rewrite <- Hdom1.
        intros Hxdom.
        apply elem_of_dom in Hxdom as [T HT].
        rewrite HT in Hx1. discriminate.
      }
      assert (Hxcomma : x ∈ ctx_fv (CtxComma Γ1 Γ2)).
      { cbn [ctx_fv]. set_solver. }
      assert (Hleft :
          (store_restrict Σ (ctx_fv (CtxComma Γ1 Γ2)) : gmap atom ty)
            !! x = Σ !! x).
      {
        destruct (Σ !! x) as [TΣ|] eqn:HΣx.
        - apply storeA_restrict_lookup_some_2; assumption.
        - apply storeA_restrict_lookup_none_l. exact HΣx.
      }
      destruct (Σ !! x) as [TΣ|] eqn:HΣx.
      * transitivity (Some TΣ).
        -- apply map_lookup_union_Some_raw. left. exact HΣx.
        -- symmetry. apply map_lookup_union_Some_raw. left.
           exact Hleft.
      * transitivity (@None ty).
        -- apply map_lookup_union_None. split; assumption.
        -- symmetry. apply map_lookup_union_None. split.
           ++ exact Hleft.
           ++ exact Hx1.
Qed.

Lemma ctx_denote_under_comma_left_minimal
    (Σ : gmap atom ty) Γ1 Γ2 (m : WfWorldT) :
  m ⊨ ctx_denote_under Σ Γ1 ->
  m ⊨ ctx_denote_under
    (store_restrict Σ (ctx_fv (CtxComma Γ1 Γ2))) Γ1.
Proof.
  intros Hctx.
  rewrite ctx_denote_under_minimal.
  rewrite ctx_denote_under_minimal in Hctx.
  rewrite storeA_restrict_twice_subset
    by (cbn [ctx_fv]; set_solver).
  exact Hctx.
Qed.

Lemma ctx_erasure_under_comma_basic_world
    (Σ : gmap atom ty) Γ1 Γ2 (m : WfWorldT) :
  basic_ctx (dom Σ) Γ1 ->
  m ⊨ basic_world_formula
    (atom_env_to_lty_env
      (ctx_erasure_under
        (store_restrict Σ (ctx_fv (CtxComma Γ1 Γ2)))
        Γ1)) ->
  m ⊨ basic_world_formula
    (atom_env_to_lty_env
      (ctx_erasure_under
        (store_restrict Σ (ctx_fv (CtxComma Γ1 Γ2)) ∪ erase_ctx Γ1)
        Γ2)) ->
  m ⊨ basic_world_formula
    (atom_env_to_lty_env (ctx_erasure_under Σ (CtxComma Γ1 Γ2))).
Proof.
  intros Hbasic HΓ1 HΓ2.
  pose proof (basic_ctx_erase_dom (dom Σ) Γ1 Hbasic) as Hdom1.
  pose proof (basic_ctx_dom_fresh (dom Σ) Γ1 Hbasic) as Hfresh1.
  pose proof (basic_world_formula_union
    (atom_env_to_lty_env
      (ctx_erasure_under
        (store_restrict Σ (ctx_fv (CtxComma Γ1 Γ2)))
        Γ1))
    (atom_env_to_lty_env
      (ctx_erasure_under
        (store_restrict Σ (ctx_fv (CtxComma Γ1 Γ2)) ∪ erase_ctx Γ1)
        Γ2))
    m HΓ1 HΓ2) as Hunion.
  replace (atom_env_to_lty_env (ctx_erasure_under Σ (CtxComma Γ1 Γ2)))
    with
      (atom_env_to_lty_env
        (ctx_erasure_under
          (store_restrict Σ (ctx_fv (CtxComma Γ1 Γ2)))
          Γ1) ∪
       atom_env_to_lty_env
        (ctx_erasure_under
          (store_restrict Σ (ctx_fv (CtxComma Γ1 Γ2)) ∪ erase_ctx Γ1)
          Γ2)).
  - exact Hunion.
  - unfold ctx_erasure_under.
    cbn [ctx_fv erase_ctx].
    rewrite <- atom_store_to_lvar_store_union.
    f_equal.
    set (A := store_restrict Σ (ctx_fv Γ1 ∪ ctx_fv Γ2 ∖ ctx_dom Γ1)).
    set (E1 := erase_ctx Γ1).
    set (E2 := erase_ctx Γ2).
    change ((store_restrict A (ctx_fv Γ1) ∪ E1) ∪
      (store_restrict (A ∪ E1) (ctx_fv Γ2) ∪ E2) =
      A ∪ (E1 ∪ E2)).
    apply storeA_map_eq. intros x.
    destruct ((A : gmap atom ty) !! x) as [TA|] eqn:HA.
    + assert (HxC : x ∈ ctx_fv Γ1 ∪ ctx_fv Γ2 ∖ ctx_dom Γ1).
      { unfold A in HA. apply storeA_restrict_lookup_some in HA as [HxC _]. exact HxC. }
      destruct (decide (x ∈ ctx_fv Γ1)) as [HxF1|HxF1].
      * transitivity (Some TA).
        -- apply map_lookup_union_Some_raw. left.
           apply map_lookup_union_Some_raw. left.
           apply storeA_restrict_lookup_some_2; [exact HA|exact HxF1].
        -- symmetry. apply map_lookup_union_Some_raw. left. exact HA.
      * assert (HxF2 : x ∈ ctx_fv Γ2) by better_set_solver.
        assert (HxD1 : x ∉ ctx_dom Γ1) by better_set_solver.
        assert (HE1 : (E1 : gmap atom ty) !! x = None).
        {
          unfold E1.
          apply not_elem_of_dom. rewrite Hdom1. exact HxD1.
        }
        transitivity (Some TA).
        -- apply map_lookup_union_Some_raw. right. split.
           ++ apply map_lookup_union_None. split.
              ** apply storeA_restrict_lookup_none_r. exact HxF1.
              ** exact HE1.
           ++ apply map_lookup_union_Some_raw. left.
              apply storeA_restrict_lookup_some_2; [|exact HxF2].
              apply map_lookup_union_Some_raw. left. exact HA.
        -- symmetry. apply map_lookup_union_Some_raw. left. exact HA.
    + destruct ((E1 : gmap atom ty) !! x) as [T1|] eqn:HE1.
      * transitivity (Some T1).
        -- apply map_lookup_union_Some_raw. left.
           apply map_lookup_union_Some_raw. right. split.
           ++ apply storeA_restrict_lookup_none_l. exact HA.
           ++ exact HE1.
        -- symmetry. apply map_lookup_union_Some_raw. right. split; [exact HA|].
           apply map_lookup_union_Some_raw. left. exact HE1.
      * destruct ((E2 : gmap atom ty) !! x) as [T2|] eqn:HE2.
        -- transitivity (Some T2).
           ++ apply map_lookup_union_Some_raw. right. split.
              ** apply map_lookup_union_None. split.
                 --- apply storeA_restrict_lookup_none_l. exact HA.
                 --- exact HE1.
              ** apply map_lookup_union_Some_raw. right. split.
                 --- apply storeA_restrict_lookup_none_l.
                     apply map_lookup_union_None. split; assumption.
                 --- exact HE2.
           ++ symmetry. apply map_lookup_union_Some_raw. right. split; [exact HA|].
              apply map_lookup_union_Some_raw. right. split; [exact HE1|exact HE2].
        -- transitivity (@None ty).
           ++ apply map_lookup_union_None. split.
              ** apply map_lookup_union_None. split.
                 --- apply storeA_restrict_lookup_none_l. exact HA.
                 --- exact HE1.
              ** apply map_lookup_union_None. split.
                 --- apply storeA_restrict_lookup_none_l.
                     apply map_lookup_union_None. split; assumption.
                 --- exact HE2.
           ++ symmetry. apply map_lookup_union_None. split; [exact HA|].
              apply map_lookup_union_None. split; assumption.
Qed.

Lemma ctx_erasure_under_star_basic_world
    (Σ : gmap atom ty) Γ1 Γ2 (m : WfWorldT) :
  basic_ctx (dom Σ) Γ1 ->
  m ⊨ basic_world_formula
    (atom_env_to_lty_env
      (ctx_erasure_under
        (store_restrict Σ (ctx_fv (CtxStar Γ1 Γ2)))
        Γ1)) ->
  m ⊨ basic_world_formula
    (atom_env_to_lty_env
      (ctx_erasure_under
        (store_restrict Σ (ctx_fv (CtxStar Γ1 Γ2)))
        Γ2)) ->
  m ⊨ basic_world_formula
    (atom_env_to_lty_env (ctx_erasure_under Σ (CtxStar Γ1 Γ2))).
Proof.
  intros Hbasic HΓ1 HΓ2.
  pose proof (basic_ctx_erase_dom (dom Σ) Γ1 Hbasic) as Hdom1.
  pose proof (basic_ctx_dom_fresh (dom Σ) Γ1 Hbasic) as Hfresh1.
  pose proof (basic_world_formula_union
    (atom_env_to_lty_env
      (ctx_erasure_under
        (store_restrict Σ (ctx_fv (CtxStar Γ1 Γ2)))
        Γ1))
    (atom_env_to_lty_env
      (ctx_erasure_under
        (store_restrict Σ (ctx_fv (CtxStar Γ1 Γ2)))
        Γ2))
    m HΓ1 HΓ2) as Hunion.
  replace (atom_env_to_lty_env (ctx_erasure_under Σ (CtxStar Γ1 Γ2)))
    with
      (atom_env_to_lty_env
        (ctx_erasure_under
          (store_restrict Σ (ctx_fv (CtxStar Γ1 Γ2)))
          Γ1) ∪
       atom_env_to_lty_env
        (ctx_erasure_under
          (store_restrict Σ (ctx_fv (CtxStar Γ1 Γ2)))
          Γ2)).
  - exact Hunion.
  - unfold ctx_erasure_under.
    cbn [ctx_fv erase_ctx].
    rewrite <- atom_store_to_lvar_store_union.
    f_equal.
    set (A := store_restrict Σ (ctx_fv Γ1 ∪ ctx_fv Γ2)).
    set (E1 := erase_ctx Γ1).
    set (E2 := erase_ctx Γ2).
    change ((store_restrict A (ctx_fv Γ1) ∪ E1) ∪
      (store_restrict A (ctx_fv Γ2) ∪ E2) =
      A ∪ (E1 ∪ E2)).
    apply storeA_map_eq. intros x.
    destruct ((A : gmap atom ty) !! x) as [TA|] eqn:HA.
    + assert (HxC : x ∈ ctx_fv Γ1 ∪ ctx_fv Γ2).
      { unfold A in HA. apply storeA_restrict_lookup_some in HA as [HxC _]. exact HxC. }
      destruct (decide (x ∈ ctx_fv Γ1)) as [HxF1|HxF1].
      * transitivity (Some TA).
        -- apply map_lookup_union_Some_raw. left.
           apply map_lookup_union_Some_raw. left.
           apply storeA_restrict_lookup_some_2; [exact HA|exact HxF1].
        -- symmetry. apply map_lookup_union_Some_raw. left. exact HA.
      * assert (HxF2 : x ∈ ctx_fv Γ2) by better_set_solver.
        assert (HxΣ : x ∈ dom Σ).
        {
          unfold A in HA.
          apply storeA_restrict_lookup_some in HA as [_ HΣx].
          by apply elem_of_dom_2 in HΣx.
        }
        assert (HE1 : (E1 : gmap atom ty) !! x = None).
        {
          unfold E1.
          apply not_elem_of_dom. rewrite Hdom1.
          intros HxD1. better_set_solver.
        }
        transitivity (Some TA).
        -- apply map_lookup_union_Some_raw. right. split.
           ++ apply map_lookup_union_None. split.
              ** apply storeA_restrict_lookup_none_r. exact HxF1.
              ** exact HE1.
           ++ apply map_lookup_union_Some_raw. left.
              apply storeA_restrict_lookup_some_2; [exact HA|exact HxF2].
        -- symmetry. apply map_lookup_union_Some_raw. left. exact HA.
    + destruct ((E1 : gmap atom ty) !! x) as [T1|] eqn:HE1.
      * transitivity (Some T1).
        -- apply map_lookup_union_Some_raw. left.
           apply map_lookup_union_Some_raw. right. split.
           ++ apply storeA_restrict_lookup_none_l. exact HA.
           ++ exact HE1.
        -- symmetry. apply map_lookup_union_Some_raw. right. split; [exact HA|].
           apply map_lookup_union_Some_raw. left. exact HE1.
      * destruct ((E2 : gmap atom ty) !! x) as [T2|] eqn:HE2.
        -- transitivity (Some T2).
           ++ apply map_lookup_union_Some_raw. right. split.
              ** apply map_lookup_union_None. split.
                 --- apply storeA_restrict_lookup_none_l. exact HA.
                 --- exact HE1.
              ** apply map_lookup_union_Some_raw. right. split.
                 --- apply storeA_restrict_lookup_none_l. exact HA.
                 --- exact HE2.
           ++ symmetry. apply map_lookup_union_Some_raw. right. split; [exact HA|].
              apply map_lookup_union_Some_raw. right. split; [exact HE1|exact HE2].
        -- transitivity (@None ty).
           ++ apply map_lookup_union_None. split.
              ** apply map_lookup_union_None. split.
                 --- apply storeA_restrict_lookup_none_l. exact HA.
                 --- exact HE1.
              ** apply map_lookup_union_None. split.
                 --- apply storeA_restrict_lookup_none_l. exact HA.
                 --- exact HE2.
           ++ symmetry. apply map_lookup_union_None. split; [exact HA|].
              apply map_lookup_union_None. split; assumption.
Qed.

Lemma ctx_denote_under_comma_intro
    (Σ : gmap atom ty) Γ1 Γ2 (m : WfWorldT) :
  basic_ctx (dom Σ) Γ1 ->
  m ⊨ ctx_denote_under Σ Γ1 ->
  m ⊨ ctx_denote_under (Σ ∪ erase_ctx Γ1) Γ2 ->
  m ⊨ ctx_denote_under Σ (CtxComma Γ1 Γ2).
Proof.
  intros Hbasic HΓ1 HΓ2.
  pose proof (ctx_denote_under_comma_left_minimal
    Σ Γ1 Γ2 m HΓ1) as HΓ1'.
  pose proof (ctx_denote_under_comma_right_minimal
    Σ Γ1 Γ2 m Hbasic HΓ2) as HΓ2'.
  pose proof (ctx_denote_under_basic_world
    (store_restrict Σ (ctx_fv (CtxComma Γ1 Γ2))) Γ1 m HΓ1')
    as HworldΓ1.
  pose proof (ctx_denote_under_basic_world
    (store_restrict Σ (ctx_fv (CtxComma Γ1 Γ2)) ∪ erase_ctx Γ1)
    Γ2 m HΓ2')
    as HworldΓ2.
  cbn [ctx_denote_under].
  rewrite res_models_and_iff. split.
  - eapply ctx_erasure_under_comma_basic_world; eauto.
  - rewrite res_models_and_iff. split; assumption.
Qed.

Lemma ctx_denote_under_star_elim
    (Σ : gmap atom ty) Γ1 Γ2 (m : WfWorldT) :
  m ⊨ ctx_denote_under Σ (CtxStar Γ1 Γ2) ->
  exists (m1 m2 : WfWorldT) (Hc : world_compat m1 m2),
    res_product m1 m2 Hc ⊑ m /\
    m1 ⊨ ctx_denote_under Σ Γ1 /\
    m2 ⊨ ctx_denote_under Σ Γ2.
Proof.
  intros Hctx.
  cbn [ctx_denote_under] in Hctx.
  rewrite res_models_and_iff in Hctx.
  destruct Hctx as [_ Hstar].
  rewrite res_models_star_iff in Hstar.
  destruct Hstar as (m1 & m2 & Hc & Hle & HΓ1 & HΓ2).
  exists m1, m2, Hc. split; [exact Hle|].
  split.
  - rewrite ctx_denote_under_minimal.
    rewrite ctx_denote_under_minimal in HΓ1.
    rewrite storeA_restrict_twice_subset in HΓ1
      by (cbn [ctx_fv]; set_solver).
    exact HΓ1.
  - rewrite ctx_denote_under_minimal.
    rewrite ctx_denote_under_minimal in HΓ2.
    rewrite storeA_restrict_twice_subset in HΓ2
      by (cbn [ctx_fv]; set_solver).
    exact HΓ2.
Qed.

Lemma ctx_denote_under_star_intro_product
    (Σ : gmap atom ty) Γ1 Γ2 (m1 m2 : WfWorldT)
    (Hc : world_compat m1 m2) :
  basic_ctx (dom Σ) Γ1 ->
  m1 ⊨ ctx_denote_under Σ Γ1 ->
  m2 ⊨ ctx_denote_under Σ Γ2 ->
  res_product m1 m2 Hc ⊨ ctx_denote_under Σ (CtxStar Γ1 Γ2).
Proof.
  intros Hbasic HΓ1 HΓ2.
  assert (HΓ1' :
      m1 ⊨ ctx_denote_under
        (store_restrict Σ (ctx_fv (CtxStar Γ1 Γ2))) Γ1).
  {
    rewrite ctx_denote_under_minimal.
    rewrite ctx_denote_under_minimal in HΓ1.
    rewrite storeA_restrict_twice_subset
      by (cbn [ctx_fv]; set_solver).
    exact HΓ1.
  }
  assert (HΓ2' :
      m2 ⊨ ctx_denote_under
        (store_restrict Σ (ctx_fv (CtxStar Γ1 Γ2))) Γ2).
  {
    rewrite ctx_denote_under_minimal.
    rewrite ctx_denote_under_minimal in HΓ2.
    rewrite storeA_restrict_twice_subset
      by (cbn [ctx_fv]; set_solver).
    exact HΓ2.
  }
  pose proof (ctx_denote_under_basic_world
    (store_restrict Σ (ctx_fv (CtxStar Γ1 Γ2))) Γ1 m1 HΓ1')
    as Hworld1.
  pose proof (ctx_denote_under_basic_world
    (store_restrict Σ (ctx_fv (CtxStar Γ1 Γ2))) Γ2 m2 HΓ2')
    as Hworld2.
  pose proof (res_models_kripke
    m1 (res_product m1 m2 Hc)
    (basic_world_formula
      (atom_env_to_lty_env
        (ctx_erasure_under
          (store_restrict Σ (ctx_fv (CtxStar Γ1 Γ2))) Γ1)))
    (res_product_le_l m1 m2 Hc) Hworld1) as Hworld1_prod.
  pose proof (res_models_kripke
    m2 (res_product m1 m2 Hc)
    (basic_world_formula
      (atom_env_to_lty_env
        (ctx_erasure_under
          (store_restrict Σ (ctx_fv (CtxStar Γ1 Γ2))) Γ2)))
    (res_product_le_r m1 m2 Hc) Hworld2) as Hworld2_prod.
  cbn [ctx_denote_under].
  rewrite res_models_and_iff. split.
  - eapply ctx_erasure_under_star_basic_world; eauto.
  - eapply res_models_star_intro; [apply raw_le_refl|exact HΓ1'|exact HΓ2'].
Qed.

Theorem ctx_denote_under_star_comm_iff
    (Σ : gmap atom ty) Γ1 Γ2 (m : WfWorldT) :
  basic_ctx (dom Σ) Γ1 ->
  basic_ctx (dom Σ) Γ2 ->
  m ⊨ ctx_denote_under Σ (CtxStar Γ1 Γ2) <->
  m ⊨ ctx_denote_under Σ (CtxStar Γ2 Γ1).
Proof.
  intros Hbasic1 Hbasic2.
  split; intros Hctx.
  - pose proof (ctx_denote_under_star_elim Σ Γ1 Γ2 m Hctx)
      as (m1 & m2 & Hc & Hle & HΓ1 & HΓ2).
    destruct (res_product_comm_eq m1 m2 Hc) as [Hc' Heq].
    eapply res_models_kripke; [exact Hle|].
    rewrite Heq.
    eapply ctx_denote_under_star_intro_product; eauto.
  - pose proof (ctx_denote_under_star_elim Σ Γ2 Γ1 m Hctx)
      as (m1 & m2 & Hc & Hle & HΓ2 & HΓ1).
    destruct (res_product_comm_eq m1 m2 Hc) as [Hc' Heq].
    eapply res_models_kripke; [exact Hle|].
    rewrite Heq.
    eapply ctx_denote_under_star_intro_product; eauto.
Qed.

End ContextDenotation.

#[global] Instance denot_cty_inst :
    Denotation context_ty (tm -> Formula (V := value)) :=
  fun τ e => ty_denote ∅ τ e.
#[global] Instance ctx_denote_inst :
    Denotation ctx (Formula (V := value)) := ctx_denote.
Arguments denot_cty_inst /.
Arguments ctx_denote_inst /.
