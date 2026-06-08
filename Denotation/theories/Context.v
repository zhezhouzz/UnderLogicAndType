(** * Denotation.Context

    Denotation of type contexts, expressed directly with the new recursive
    context-type denotation. *)

From Denotation Require Export Notation TypeDenote.
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

Lemma erase_ctx_star_bind_insert_agree_on
    (Σ : gmap atom ty) Γ1 Γ2 τx x X :
  basic_ctx (dom Σ) (CtxStar Γ1 Γ2) ->
  X ⊆ dom (erase_ctx (CtxStar Γ2 (CtxBind x τx))) ->
  x ∉ dom (erase_ctx (CtxStar Γ1 Γ2)) ->
  ty_env_agree_on X
    (erase_ctx (CtxStar Γ2 (CtxBind x τx)))
    (<[x := erase_ty τx]> (erase_ctx (CtxStar Γ1 Γ2))).
Proof.
  intros Hbasic_top HX Hxctx y Hy.
  cbn [basic_ctx] in Hbasic_top.
  destruct Hbasic_top as [Hbasic1 [Hbasic2 Hdisj12]].
  pose proof (basic_ctx_erase_dom (dom Σ) Γ1 Hbasic1) as Hdom1.
  pose proof (basic_ctx_erase_dom (dom Σ) Γ2 Hbasic2) as Hdom2.
  destruct (decide (y = x)) as [->|Hyx].
  - cbn [erase_ctx].
    transitivity (Some (erase_ty τx)).
    + apply map_lookup_union_Some_raw. right. split.
      * apply not_elem_of_dom. intros HxΓ2.
        apply Hxctx. cbn [erase_ctx].
        apply elem_of_dom in HxΓ2 as [Tx HTx].
        apply elem_of_dom.
        destruct ((erase_ctx Γ1 : gmap atom ty) !! x) as [T1|] eqn:HT1.
        -- exists T1. apply map_lookup_union_Some_raw. left. exact HT1.
        -- exists Tx. apply map_lookup_union_Some_raw. right. split; assumption.
      * apply map_lookup_singleton.
    + symmetry. apply map_lookup_insert.
  - assert (HyΓ2 : y ∈ dom (erase_ctx Γ2)).
    {
      assert (HySrc : y ∈ dom (erase_ctx (CtxStar Γ2 (CtxBind x τx)))).
      { apply HX. exact Hy. }
      cbn [erase_ctx] in HySrc.
      apply elem_of_dom in HySrc as [Ty HTy].
      apply map_lookup_union_Some_raw in HTy as [HTy|[_ HTy]].
      - apply elem_of_dom. eauto.
      - change (({[x := erase_ty τx]} : gmap atom ty) !! y = Some Ty) in HTy.
        apply (proj1 (lookup_singleton_Some x y (erase_ty τx) Ty)) in HTy
          as [Hy_eq _].
        congruence.
    }
    pose proof HyΓ2 as HyΓ2_dom.
    apply elem_of_dom in HyΓ2 as [T HT].
    transitivity (Some T).
    + cbn [erase_ctx].
      apply map_lookup_union_Some_raw. left. exact HT.
    + symmetry.
      transitivity ((erase_ctx (CtxStar Γ1 Γ2) : gmap atom ty) !! y).
      * apply map_lookup_insert_ne. congruence.
      * cbn [erase_ctx].
        apply map_lookup_union_Some_raw. right. split.
        -- apply not_elem_of_dom. intros HyΓ1.
           rewrite Hdom1 in HyΓ1.
           rewrite Hdom2 in HyΓ2_dom.
           better_set_solver.
        -- exact HT.
Qed.

Lemma ctx_erasure_under_minimal Σ Γ :
  ctx_erasure_under Σ Γ =
  ctx_erasure_under (store_restrict Σ (ctx_fv Γ)) Γ.
Proof.
  unfold ctx_erasure_under.
  rewrite storeA_restrict_twice_same.
  reflexivity.
Qed.

Lemma ctx_erasure_under_bind Σ x τ :
  ctx_erasure_under Σ (CtxBind x τ) =
  store_restrict Σ (fv_cty τ) ∪ {[x := erase_ty τ]}.
Proof.
  unfold ctx_erasure_under.
  cbn [ctx_fv erase_ctx].
  reflexivity.
Qed.

Lemma ctx_erasure_under_comma Σ Γ1 Γ2 :
  ctx_erasure_under Σ (CtxComma Γ1 Γ2) =
  store_restrict Σ (ctx_fv Γ1 ∪ (ctx_fv Γ2 ∖ ctx_dom Γ1)) ∪
    (erase_ctx Γ1 ∪ erase_ctx Γ2).
Proof.
  unfold ctx_erasure_under.
  cbn [ctx_fv erase_ctx].
  reflexivity.
Qed.

Lemma ctx_erasure_under_star Σ Γ1 Γ2 :
  ctx_erasure_under Σ (CtxStar Γ1 Γ2) =
  store_restrict Σ (ctx_fv Γ1 ∪ ctx_fv Γ2) ∪
    (erase_ctx Γ1 ∪ erase_ctx Γ2).
Proof.
  unfold ctx_erasure_under.
  cbn [ctx_fv erase_ctx].
  reflexivity.
Qed.

Lemma erase_ctx_star_lookup_r_of_basic (Σ : gmap atom ty) Γ1 Γ2 x T :
  basic_ctx (dom Σ) Γ1 ->
  basic_ctx (dom Σ) Γ2 ->
  ctx_dom Γ1 ## ctx_dom Γ2 ->
  (erase_ctx Γ2 : gmap atom ty) !! x = Some T ->
  (erase_ctx (CtxStar Γ1 Γ2) : gmap atom ty) !! x = Some T.
Proof.
  intros Hbasic1 Hbasic2 Hdisj Hx2.
  change ((erase_ctx (CtxStar Γ1 Γ2) : gmap atom ty) !! x)
    with (((erase_ctx Γ1 ∪ erase_ctx Γ2) : gmap atom ty) !! x).
  apply map_lookup_union_Some_raw. right.
  split; [|exact Hx2].
  apply not_elem_of_dom. intros Hx1dom.
  pose proof (basic_ctx_erase_dom (dom Σ) Γ1 Hbasic1) as Hdom1.
  pose proof (basic_ctx_erase_dom (dom Σ) Γ2 Hbasic2) as Hdom2.
  assert (Hx2dom : x ∈ dom (erase_ctx Γ2 : gmap atom ty)).
  { apply elem_of_dom. eexists. exact Hx2. }
  rewrite Hdom1 in Hx1dom.
  rewrite Hdom2 in Hx2dom.
  better_set_solver.
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

Lemma ty_denote_gas_ret_fvar_insert_atom_env_agree_on
    gas (Δ1 Δ2 : gmap atom ty) τ y (m : WfWorldT) :
  ty_env_agree_on (fv_cty τ ∪ {[y]})
    (<[y := erase_ty τ]> Δ1)
    (<[y := erase_ty τ]> Δ2) ->
  m ⊨ ty_denote_gas gas
    (atom_env_to_lty_env (<[y := erase_ty τ]> Δ1))
    τ (tret (vfvar y)) ->
  m ⊨ ty_denote_gas gas
    (atom_env_to_lty_env (<[y := erase_ty τ]> Δ2))
    τ (tret (vfvar y)).
Proof.
  intros Hagree Hden.
  eapply res_models_ty_denote_gas_env_agree_on
    with (X := relevant_lvars τ (tret (vfvar y)));
    [reflexivity| |exact Hden].
  apply atom_env_to_lty_env_restrict_lvars_agree_on
    with (X := fv_cty τ ∪ {[y]}).
  - exact Hagree.
  - relevant_lvars_norm. better_set_solver.
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

Lemma ty_env_agree_ctx_erasure_under_of_basic_ctx
    (Σ : gmap atom ty) Γ X :
  basic_ctx (dom Σ) Γ ->
  X ⊆ dom (erase_ctx Γ) ->
  ty_env_agree_on X (Σ ∪ erase_ctx Γ) (ctx_erasure_under Σ Γ).
Proof.
  intros Hbasic HX x Hx.
  assert (HxΓ : x ∈ dom (erase_ctx Γ)).
  { exact (HX x Hx). }
  pose proof (erase_ctx_lookup_ctx_erasure_under_of_basic_ctx
    Σ Γ x Hbasic HxΓ) as Herase.
  assert (HΣnone : Σ !! x = None).
  {
    apply not_elem_of_dom. intros HΣx.
    pose proof (basic_ctx_erase_dom (dom Σ) Γ Hbasic) as HdomΓ.
    pose proof (basic_ctx_dom_fresh (dom Σ) Γ Hbasic) as HfreshΓ.
    apply elem_of_disjoint in HfreshΓ.
    eapply HfreshΓ; [|exact HΣx].
    rewrite <- HdomΓ. exact HxΓ.
  }
  transitivity ((erase_ctx Γ : gmap atom ty) !! x).
  - apply lookup_union_r. exact HΣnone.
  - exact Herase.
Qed.

Lemma ctx_erasure_under_erase_ctx_dom_subset
    (Σ : gmap atom ty) Γ :
  dom (erase_ctx Γ) ⊆ dom (ctx_erasure_under Σ Γ).
Proof.
  intros x Hx.
  unfold ctx_erasure_under.
  apply elem_of_dom in Hx as [T HT].
  apply elem_of_dom.
  destruct ((store_restrict Σ (ctx_fv Γ) : gmap atom ty) !! x)
    as [Tleft|] eqn:Hleft.
  - exists Tleft. apply map_lookup_union_Some_raw. left. exact Hleft.
  - exists T. apply map_lookup_union_Some_raw. right. split; assumption.
Qed.

Lemma ctx_erasure_under_notin_erase_ctx
    (Σ : gmap atom ty) Γ x :
  x ∉ dom (ctx_erasure_under Σ Γ) ->
  x ∉ dom (erase_ctx Γ).
Proof.
  intros Hnot Hx.
  apply Hnot.
  eapply ctx_erasure_under_erase_ctx_dom_subset.
  exact Hx.
Qed.

Lemma ty_denote_gas_ret_fvar_insert_ctx_erasure_under
    gas (Σ : gmap atom ty) Γ τ y (m : WfWorldT) :
  basic_ctx (dom Σ) Γ ->
  fv_cty τ ⊆ dom (erase_ctx Γ) ->
  m ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τ]> (atom_env_to_lty_env (erase_ctx Γ)))
    τ (tret (vfvar y)) ->
  m ⊨ ty_denote_gas gas
    (atom_env_to_lty_env (<[y:=erase_ty τ]> (ctx_erasure_under Σ Γ)))
    τ (tret (vfvar y)).
Proof.
  intros Hbasic Hτfv Hden.
  rewrite <- atom_store_to_lvar_store_insert in Hden.
  eapply (ty_denote_gas_ret_fvar_insert_atom_env_agree_on
    gas (erase_ctx Γ) (ctx_erasure_under Σ Γ) τ y m);
    [|exact Hden].
  unfold ty_env_agree_on. intros z Hz.
  destruct (decide (z = y)) as [->|Hzy].
  - setoid_rewrite lookup_insert.
    repeat case_decide; congruence.
  - assert (HzΓ : z ∈ dom (erase_ctx Γ)).
    { better_set_solver. }
    transitivity ((erase_ctx Γ : gmap atom ty) !! z).
    + apply map_lookup_insert_ne. congruence.
    + transitivity ((ctx_erasure_under Σ Γ : gmap atom ty) !! z).
      * apply erase_ctx_lookup_ctx_erasure_under_of_basic_ctx; assumption.
      * symmetry. apply map_lookup_insert_ne. congruence.
Qed.

Lemma ty_denote_gas_ret_fvar_insert_closed_atom_env
    gas (Δ1 Δ2 : gmap atom ty) τ y (m : WfWorldT) :
  basic_context_ty ∅ τ ->
  m ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τ]> (atom_env_to_lty_env Δ1))
    τ (tret (vfvar y)) ->
  m ⊨ ty_denote_gas gas
    (atom_env_to_lty_env (<[y:=erase_ty τ]> Δ2))
    τ (tret (vfvar y)).
Proof.
  intros Hτ Hden.
  rewrite <- atom_store_to_lvar_store_insert in Hden.
  eapply (ty_denote_gas_ret_fvar_insert_atom_env_agree_on
    gas Δ1 Δ2 τ y m); [|exact Hden].
  unfold ty_env_agree_on. intros z Hz.
  destruct (decide (z = y)) as [->|Hzy].
  - setoid_rewrite lookup_insert.
    repeat case_decide; congruence.
  - exfalso.
    pose proof (basic_context_ty_fv_subset ∅ τ Hτ) as Hτfv.
    assert (Hzτ : z ∈ fv_cty τ) by better_set_solver.
    pose proof (Hτfv z Hzτ). better_set_solver.
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

Lemma ty_denote_under_star_bind_to_lvar_insert_direct
    (Σ : gmap atom ty) Γ τx τ e y (m : WfWorldT) :
  y ∉ dom (erase_ctx Γ) ->
  m ⊨ ty_denote_under Σ (CtxStar Γ (CtxBind y τx)) τ e ->
  m ⊨ ty_denote_gas (cty_depth τ)
    (<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ)))
    τ e.
Proof.
  intros Hy Hden.
  unfold ty_denote_under, ty_denote in Hden |- *.
  assert (Henv :
      erase_ctx (CtxStar Γ (CtxBind y τx)) =
      <[y := erase_ty τx]> (erase_ctx Γ)).
  {
    cbn [erase_ctx].
    apply storeA_union_singleton_insert_fresh.
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

Lemma ty_denote_under_star_bind_to_comma_bind_fresh
    (Σ : gmap atom ty) Γ τx τ e y (m : WfWorldT) :
  y ∉ dom (erase_ctx Γ) ->
  m ⊨ ty_denote_under Σ (CtxStar Γ (CtxBind y τx)) τ e ->
  m ⊨ ty_denote_under Σ (CtxComma Γ (CtxBind y τx)) τ e.
Proof.
  intros Hy Hden.
  unfold ty_denote_under, ty_denote in Hden |- *.
  rewrite erase_ctx_star_bind_fresh in Hden by exact Hy.
  rewrite erase_ctx_comma_bind_fresh by exact Hy.
  exact Hden.
Qed.

Lemma ctx_bind_from_base_denotation
    (Σ : gmap atom ty) x τ (m : WfWorldT) :
  basic_context_ty (dom Σ) τ ->
  x ∉ dom Σ ->
  m ⊨ ty_denote_gas (cty_depth τ)
    (atom_env_to_lty_env (<[x := erase_ty τ]> Σ))
    τ (tret (vfvar x)) ->
  m ⊨ ctx_denote_under Σ (CtxBind x τ).
Proof.
  intros Hτ HxΣ Harg.
  pose proof (ty_denote_gas_guard _ _ _ _ _ Harg) as Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [_ [Hrel_world _]].
  assert (Hworld_bind :
      m ⊨ basic_world_formula
        (atom_env_to_lty_env (ctx_erasure_under Σ (CtxBind x τ)))).
  {
    eapply basic_world_formula_subenv; [|exact Hrel_world].
    intros v T Hv.
    destruct v as [k|y].
    - rewrite atom_store_to_lvar_store_lookup_bound_none in Hv.
      discriminate.
    - rewrite atom_store_to_lvar_store_lookup_free in Hv.
      unfold ctx_erasure_under in Hv.
      cbn [ctx_fv erase_ctx] in Hv.
      apply map_lookup_union_Some_raw in Hv as [HΣ | [_ Hx]].
      + apply storeA_restrict_lookup_some in HΣ as [Hyτ HΣ].
        unfold relevant_env, lty_env_restrict_lvars.
        apply storeA_restrict_lookup_some_2.
        * rewrite atom_store_to_lvar_store_lookup_free.
          change ((<[x := erase_ty τ]> (Σ : gmap atom ty)) !! y = Some T).
          unfold store_insert.
          rewrite (lookup_insert_ne (Σ : gmap atom ty) x y (erase_ty τ)).
          -- exact HΣ.
          -- intros ->. apply HxΣ.
             apply elem_of_dom_2 in HΣ. exact HΣ.
        * unfold relevant_lvars.
          apply elem_of_union_l.
          apply (proj1 (lvars_fv_elem (context_ty_lvars τ) y)).
          rewrite context_ty_lvars_fv. exact Hyτ.
      + apply (proj1 (lookup_singleton_Some x y (erase_ty τ) T)) in Hx
          as [-> ->].
        unfold relevant_env, lty_env_restrict_lvars.
        apply storeA_restrict_lookup_some_2.
        * rewrite atom_store_to_lvar_store_lookup_free.
          apply map_lookup_insert.
        * unfold relevant_lvars.
          apply elem_of_union_r.
          cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys].
          set_solver.
  }
  assert (Harg_bind :
      m ⊨ ty_denote_gas (cty_depth τ)
        (atom_env_to_lty_env (ctx_erasure_under Σ (CtxBind x τ)))
        τ (tret (vfvar x))).
  {
    eapply res_models_ty_denote_gas_env_agree_on
      with (X := relevant_lvars τ (tret (vfvar x)));
      [reflexivity| |exact Harg].
    apply storeA_map_eq. intros v.
    unfold lty_env_restrict_lvars.
    rewrite !storeA_restrict_lookup.
    destruct (decide (v ∈ relevant_lvars τ (tret (vfvar x))))
      as [Hv|Hv]; [|reflexivity].
    destruct v as [k|y].
    - rewrite !atom_store_to_lvar_store_lookup_bound_none. reflexivity.
    - rewrite !atom_store_to_lvar_store_lookup_free.
      unfold ctx_erasure_under. cbn [ctx_fv erase_ctx].
      destruct (decide (y = x)) as [->|Hyx].
      + assert (HL :
            (store_restrict Σ (fv_cty τ) ∪ {[x := erase_ty τ]})
              !! x = Some (erase_ty τ)).
        {
          apply map_lookup_union_Some_raw. right.
          split.
          - apply storeA_restrict_lookup_none_r.
            intros Hxτ.
            pose proof (basic_context_ty_fv_subset (dom Σ) τ Hτ) as Hτfv.
            apply HxΣ. apply Hτfv. exact Hxτ.
          - apply map_lookup_singleton.
        }
        assert (HR :
            (<[x := erase_ty τ]> Σ) !! x = Some (erase_ty τ))
          by apply map_lookup_insert.
        transitivity (Some (erase_ty τ)).
        * exact HR.
        * symmetry. exact HL.
      + unfold relevant_lvars in Hv.
        cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys] in Hv.
        assert (Hyτ : y ∈ fv_cty τ).
        {
          rewrite <- context_ty_lvars_fv.
          apply lvars_fv_elem.
          better_set_solver.
        }
        pose proof (basic_context_ty_fv_subset (dom Σ) τ Hτ) as Hτfv.
        apply Hτfv in Hyτ.
        apply elem_of_dom in Hyτ as [T HT].
        assert (Hinsert :
            (<[x := erase_ty τ]> Σ) !! y = Σ !! y).
        { apply map_lookup_insert_ne. congruence. }
        transitivity (Some T).
        * exact (eq_trans Hinsert HT).
        * symmetry.
          apply map_lookup_union_Some_raw. left.
          apply storeA_restrict_lookup_some_2; [exact HT|].
          rewrite <- context_ty_lvars_fv.
          apply lvars_fv_elem. better_set_solver.
  }
  cbn [ctx_denote_under].
  rewrite res_models_and_iff.
  split; [exact Hworld_bind|].
  unfold ty_denote.
  replace (<[x := erase_ty τ]> (store_restrict Σ (ctx_fv (CtxBind x τ))))
    with (ctx_erasure_under Σ (CtxBind x τ)).
  2:{
    unfold ctx_erasure_under. cbn [ctx_fv erase_ctx].
    assert (Hfresh : x ∉ dom (store_restrict Σ (fv_cty τ) : gmap atom ty)).
    {
      intros Hxdom.
      apply elem_of_dom in Hxdom as [T HT].
      apply storeA_restrict_lookup_some in HT as [_ HT].
      apply HxΣ. apply elem_of_dom_2 in HT. exact HT.
    }
    exact (storeA_union_singleton_insert_fresh
      (store_restrict Σ (fv_cty τ)) x (erase_ty τ) Hfresh).
  }
  exact Harg_bind.
Qed.

Lemma ctx_bind_from_inserted_erasure_denotation
    (Σ : gmap atom ty) Γ x τ (m : WfWorldT) :
  x ∉ dom (ctx_erasure_under Σ Γ) ->
  ty_env_agree_on (fv_cty τ) (Σ ∪ erase_ctx Γ) (ctx_erasure_under Σ Γ) ->
  m ⊨ basic_world_formula
    (atom_env_to_lty_env (<[x := erase_ty τ]> (ctx_erasure_under Σ Γ))) ->
  m ⊨ ty_denote_gas (cty_depth τ)
    (atom_env_to_lty_env (<[x := erase_ty τ]> (ctx_erasure_under Σ Γ)))
    τ (tret (vfvar x)) ->
  m ⊨ ctx_denote_under (Σ ∪ erase_ctx Γ) (CtxBind x τ).
Proof.
  intros HxΔ Hagree Hworld Harg.
  set (Δ := ctx_erasure_under Σ Γ).
  set (Σtarget := store_restrict (Σ ∪ erase_ctx Γ) (fv_cty τ)).
  assert (Hlookup :
      forall y T,
        (Σtarget ∪ {[x := erase_ty τ]}) !! y = Some T ->
        (<[x := erase_ty τ]> Δ) !! y = Some T).
  {
    intros y T HyT.
    apply map_lookup_union_Some_raw in HyT as [HyT | [Hnone HyT]].
    - apply storeA_restrict_lookup_some in HyT as [Hyτ HyT].
      pose proof (Hagree y Hyτ) as Hag.
      assert (HΔy : Δ !! y = Some T).
      { exact (eq_trans (eq_sym Hag) HyT). }
      destruct (decide (y = x)) as [->|Hyx].
      + exfalso.
        apply HxΔ. apply elem_of_dom. eauto.
      + exact (eq_trans
          (map_lookup_insert_ne Δ x y (erase_ty τ) ltac:(congruence))
          HΔy).
    - apply (proj1 (lookup_singleton_Some x y (erase_ty τ) T)) in HyT
        as [-> ->].
      apply map_lookup_insert.
  }
  assert (Hworld_target :
      m ⊨ basic_world_formula
        (atom_env_to_lty_env (ctx_erasure_under (Σ ∪ erase_ctx Γ)
          (CtxBind x τ)))).
  {
    unfold ctx_erasure_under. cbn [ctx_fv erase_ctx].
    fold Σtarget.
    eapply basic_world_formula_subenv; [|exact Hworld].
    intros v T Hv.
    destruct v as [k|y].
    - rewrite atom_store_to_lvar_store_lookup_bound_none in Hv.
      discriminate.
    - rewrite atom_store_to_lvar_store_lookup_free in Hv |- *.
      exact (Hlookup y T Hv).
  }
  assert (Harg_target :
      m ⊨ ty_denote_gas (cty_depth τ)
        (atom_env_to_lty_env (ctx_erasure_under (Σ ∪ erase_ctx Γ)
          (CtxBind x τ))) τ (tret (vfvar x))).
  {
    unfold ctx_erasure_under. cbn [ctx_fv erase_ctx].
    fold Σtarget.
    eapply res_models_ty_denote_gas_env_agree_on
      with (X := relevant_lvars τ (tret (vfvar x)));
      [reflexivity| |exact Harg].
    apply storeA_map_eq. intros v.
    unfold lty_env_restrict_lvars.
    rewrite !storeA_restrict_lookup.
    destruct (decide (v ∈ relevant_lvars τ (tret (vfvar x))))
      as [Hv|Hv]; [|reflexivity].
    destruct v as [k|y].
    - rewrite !atom_store_to_lvar_store_lookup_bound_none. reflexivity.
    - rewrite !atom_store_to_lvar_store_lookup_free.
      unfold relevant_lvars in Hv.
      cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys] in Hv.
      destruct (decide (y = x)) as [->|Hyx].
      + assert (HL :
            (Σtarget ∪ {[x := erase_ty τ]})
              !! x = Some (erase_ty τ)).
        {
          apply map_lookup_union_Some_raw. right.
          split.
          - unfold Σtarget.
            rewrite storeA_restrict_lookup.
            destruct (decide (x ∈ fv_cty τ)) as [Hxτ|Hxτ].
            + pose proof (Hagree x Hxτ) as Hag.
              destruct (Δ !! x) as [Tx|] eqn:Hxlookup.
              * exfalso. apply HxΔ. apply elem_of_dom. eauto.
              * exact (eq_trans Hag Hxlookup).
            + reflexivity.
          - apply map_lookup_singleton.
        }
        assert (HR :
            (<[x := erase_ty τ]> Δ) !! x = Some (erase_ty τ))
          by apply map_lookup_insert.
        transitivity (Some (erase_ty τ)); [exact HR|symmetry; exact HL].
      + assert (Hyτ : y ∈ fv_cty τ).
        {
          rewrite <- context_ty_lvars_fv.
          apply lvars_fv_elem. better_set_solver.
        }
        pose proof (Hagree y Hyτ) as Hag.
        destruct ((Σ ∪ erase_ctx Γ) !! y) as [T|] eqn:Hylookup.
        * assert (Hsource :
              (<[x := erase_ty τ]> Δ) !! y = Some T).
          {
            exact (eq_trans
              (map_lookup_insert_ne Δ x y (erase_ty τ) ltac:(congruence))
              (eq_sym Hag)).
          }
          assert (Htarget :
              (Σtarget ∪ {[x := erase_ty τ]}) !! y = Some T).
          {
            apply map_lookup_union_Some_raw. left.
            unfold Σtarget.
            apply storeA_restrict_lookup_some_2; [exact Hylookup|exact Hyτ].
          }
          transitivity (Some T); [exact Hsource|symmetry; exact Htarget].
        * assert (Hsource :
              (<[x := erase_ty τ]> Δ) !! y = None).
          {
            exact (eq_trans
              (map_lookup_insert_ne Δ x y (erase_ty τ) ltac:(congruence))
              (eq_sym Hag)).
          }
          assert (Htarget :
              (Σtarget ∪ {[x := erase_ty τ]}) !! y = None).
          {
            apply map_lookup_union_None. split.
            - unfold Σtarget. apply storeA_restrict_lookup_none_l. exact Hylookup.
            - apply lookup_singleton_ne. congruence.
          }
          transitivity (@None ty); [exact Hsource|symmetry; exact Htarget].
  }
  cbn [ctx_denote_under].
  rewrite res_models_and_iff.
  split; [exact Hworld_target|].
  unfold ty_denote.
  replace (<[x := erase_ty τ]>
      (store_restrict (Σ ∪ erase_ctx Γ) (ctx_fv (CtxBind x τ))))
    with (ctx_erasure_under (Σ ∪ erase_ctx Γ) (CtxBind x τ)).
  2:{
    unfold ctx_erasure_under. cbn [ctx_fv erase_ctx].
    assert (Hfresh :
        x ∉ dom (store_restrict (Σ ∪ erase_ctx Γ) (fv_cty τ) : gmap atom ty)).
    {
      intros Hxdom.
      apply elem_of_dom in Hxdom as [T HT].
      apply storeA_restrict_lookup_some in HT as [Hxτ HT].
      pose proof (Hagree x Hxτ) as Hag.
      destruct (Δ !! x) as [Tx|] eqn:Hxlookup.
      - exfalso. apply HxΔ. apply elem_of_dom. eauto.
      - pose proof (eq_trans (eq_sym HT) (eq_trans Hag Hxlookup)) as Hbad.
        discriminate Hbad.
    }
    exact (storeA_union_singleton_insert_fresh
      (store_restrict (Σ ∪ erase_ctx Γ) (fv_cty τ))
      x (erase_ty τ) Hfresh).
  }
  exact Harg_target.
Qed.

Lemma ty_denote_gas_result_ext_base_env_transport
    (Σ : gmap atom ty) Γ τ x (mx : WfWorldT) :
  basic_context_ty (dom Σ) τ ->
  mx ⊨ ty_denote_gas (cty_depth τ)
    (atom_env_to_lty_env
      (<[x := erase_ty τ]>
        (store_restrict (Σ ∪ erase_ctx Γ) (ctx_fv (CtxBind x τ)))))
    τ (tret (vfvar x)) ->
  mx ⊨ ty_denote_gas (cty_depth τ)
    (atom_env_to_lty_env (<[x := erase_ty τ]> Σ))
    τ (tret (vfvar x)).
Proof.
  intros Hτ Harg.
  replace (atom_env_to_lty_env
      (<[x := erase_ty τ]>
        (store_restrict (Σ ∪ erase_ctx Γ) (ctx_fv (CtxBind x τ)))))
    with (<[LVFree x := erase_ty τ]>
      (atom_env_to_lty_env
        (store_restrict (Σ ∪ erase_ctx Γ) (ctx_fv (CtxBind x τ))))) in Harg.
  2:{ symmetry. apply atom_store_to_lvar_store_insert. }
  replace (atom_env_to_lty_env (<[x := erase_ty τ]> Σ))
    with (<[LVFree x := erase_ty τ]> (atom_env_to_lty_env Σ)).
  2:{ symmetry. apply atom_store_to_lvar_store_insert. }
  eapply res_models_ty_denote_gas_env_agree_on
    with (X := relevant_lvars τ (tret (vfvar x)));
    [reflexivity| |exact Harg].
  apply storeA_map_eq. intros v.
  unfold lty_env_restrict_lvars.
  rewrite !storeA_restrict_lookup.
  destruct (decide (v ∈ relevant_lvars τ (tret (vfvar x))))
    as [Hv|Hv]; [|reflexivity].
  destruct (decide (v = LVFree x)) as [->|Hvx].
  - rewrite !lookup_insert_eq. reflexivity.
  - rewrite !lookup_insert_ne by congruence.
    destruct v as [k|y].
    + rewrite !atom_store_to_lvar_store_lookup_bound_none. reflexivity.
    + rewrite !atom_store_to_lvar_store_lookup_free.
      assert (HyΣ : y ∈ dom Σ).
      {
        pose proof (basic_context_ty_fv_subset (dom Σ) τ Hτ) as Hτfv.
        apply lvars_fv_elem in Hv.
        rewrite relevant_lvars_fv in Hv.
        cbn [fv_tm] in Hv. set_solver.
      }
      apply elem_of_dom in HyΣ as [T HT].
      transitivity (Some T).
      {
        rewrite storeA_restrict_lookup.
        destruct (decide (y ∈ ctx_fv (CtxBind x τ))) as [_|Hyfv].
        - apply map_lookup_union_Some_raw. left. exact HT.
        - exfalso. cbn [ctx_fv] in Hyfv.
          apply lvars_fv_elem in Hv.
          rewrite relevant_lvars_fv in Hv.
          cbn [fv_tm] in Hv. set_solver.
      }
      { symmetry. exact HT. }
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

Lemma ctx_denote_under_comma_left
    (Σ : gmap atom ty) Γ1 Γ2 (m : WfWorldT) :
  m ⊨ ctx_denote_under Σ (CtxComma Γ1 Γ2) ->
  m ⊨ ctx_denote_under Σ Γ1.
Proof.
  intros Hctx.
  cbn [ctx_denote_under] in Hctx.
  rewrite res_models_and_iff in Hctx.
  destruct Hctx as [_ Hbody].
  rewrite res_models_and_iff in Hbody.
  destruct Hbody as [Hleft _].
  rewrite ctx_denote_under_minimal.
  rewrite ctx_denote_under_minimal in Hleft.
  rewrite storeA_restrict_twice_subset in Hleft.
  - exact Hleft.
  - cbn [ctx_fv]. intros x Hx. apply elem_of_union_l. exact Hx.
Qed.

Lemma atom_env_to_lty_env_ctx_erasure_under_comma_union
    (Σ : gmap atom ty) Γ1 Γ2 :
  basic_ctx (dom Σ) Γ1 ->
  atom_env_to_lty_env (ctx_erasure_under Σ (CtxComma Γ1 Γ2)) =
  atom_env_to_lty_env
    (ctx_erasure_under
      (store_restrict Σ (ctx_fv (CtxComma Γ1 Γ2)))
      Γ1) ∪
  atom_env_to_lty_env
    (ctx_erasure_under
      (store_restrict Σ (ctx_fv (CtxComma Γ1 Γ2)) ∪ erase_ctx Γ1)
      Γ2).
Proof.
  intros Hbasic.
  pose proof (basic_ctx_erase_dom (dom Σ) Γ1 Hbasic) as Hdom1.
  pose proof (basic_ctx_dom_fresh (dom Σ) Γ1 Hbasic) as Hfresh1.
  unfold ctx_erasure_under.
  cbn [ctx_fv erase_ctx].
  rewrite <- atom_store_to_lvar_store_union.
  f_equal.
  symmetry.
  set (A := store_restrict Σ (ctx_fv Γ1 ∪ ctx_fv Γ2 ∖ ctx_dom Γ1)).
  set (E1 := erase_ctx Γ1).
  set (E2 := erase_ctx Γ2).
  change ((store_restrict A (ctx_fv Γ1) ∪ E1) ∪
    (store_restrict (A ∪ E1) (ctx_fv Γ2) ∪ E2) =
    A ∪ (E1 ∪ E2)).
  apply (storeA_restrict_union_frame_comma A E1 E2
    (ctx_fv Γ1) (ctx_fv Γ2) (ctx_dom Γ1)).
  - unfold A. rewrite storeA_restrict_dom. better_set_solver.
  - unfold E1. exact Hdom1.
  - unfold A. rewrite storeA_restrict_dom. better_set_solver.
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
  rewrite atom_env_to_lty_env_ctx_erasure_under_comma_union by exact Hbasic.
  exact Hunion.
Qed.

Lemma atom_env_to_lty_env_ctx_erasure_under_star_union
    (Σ : gmap atom ty) Γ1 Γ2 :
  basic_ctx (dom Σ) Γ1 ->
  atom_env_to_lty_env (ctx_erasure_under Σ (CtxStar Γ1 Γ2)) =
  atom_env_to_lty_env
    (ctx_erasure_under
      (store_restrict Σ (ctx_fv (CtxStar Γ1 Γ2)))
      Γ1) ∪
  atom_env_to_lty_env
    (ctx_erasure_under
      (store_restrict Σ (ctx_fv (CtxStar Γ1 Γ2)))
      Γ2).
Proof.
  intros Hbasic.
  pose proof (basic_ctx_erase_dom (dom Σ) Γ1 Hbasic) as Hdom1.
  pose proof (basic_ctx_dom_fresh (dom Σ) Γ1 Hbasic) as Hfresh1.
  unfold ctx_erasure_under.
  cbn [ctx_fv erase_ctx].
  rewrite <- atom_store_to_lvar_store_union.
  f_equal.
  symmetry.
  set (A := store_restrict Σ (ctx_fv Γ1 ∪ ctx_fv Γ2)).
  set (E1 := erase_ctx Γ1).
  set (E2 := erase_ctx Γ2).
  change ((store_restrict A (ctx_fv Γ1) ∪ E1) ∪
    (store_restrict A (ctx_fv Γ2) ∪ E2) =
    A ∪ (E1 ∪ E2)).
  apply storeA_restrict_union_frame_star.
  - unfold A. rewrite storeA_restrict_dom. better_set_solver.
  - unfold A, E1. rewrite storeA_restrict_dom, Hdom1. better_set_solver.
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
  rewrite atom_env_to_lty_env_ctx_erasure_under_star_union by exact Hbasic.
  exact Hunion.
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

Lemma ctx_denote_under_sum_elim
    (Σ : gmap atom ty) Γ1 Γ2 (m : WfWorldT) :
  m ⊨ ctx_denote_under Σ (CtxSum Γ1 Γ2) ->
  exists (m1 m2 : WfWorldT) (Hdef : raw_sum_defined m1 m2),
    res_sum m1 m2 Hdef ⊑ m /\
    m1 ⊨ ctx_denote_under Σ Γ1 /\
    m2 ⊨ ctx_denote_under Σ Γ2.
Proof.
  intros Hctx.
  cbn [ctx_denote_under] in Hctx.
  rewrite res_models_and_iff in Hctx.
  destruct Hctx as [_ Hplus].
  rewrite res_models_plus_iff in Hplus.
  destruct Hplus as (m1 & m2 & Hdef & Hle & HΓ1 & HΓ2).
  exists m1, m2, Hdef. split; [exact Hle|].
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

Lemma ctx_denote_under_star_bind_closed_to_comma
    (Σ : gmap atom ty) Γ x τ (m : WfWorldT) :
  basic_ctx (dom Σ) Γ ->
  basic_context_ty ∅ τ ->
  x ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ->
  m ⊨ ctx_denote_under Σ (CtxStar Γ (CtxBind x τ)) ->
  m ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind x τ)).
Proof.
  intros HbasicΓ Hτ_closed Hx Hstar.
  pose proof (ctx_denote_under_star_elim Σ Γ (CtxBind x τ) m Hstar)
    as (mΓ & mx & Hc & Hle & HΓ & Hxctx).
  assert (HΓm : m ⊨ ctx_denote_under Σ Γ).
  {
    eapply res_models_kripke; [|exact HΓ].
    etransitivity; [apply res_product_le_l|exact Hle].
  }
  pose proof (ctx_denote_under_bind_inv Σ x τ mx Hxctx) as Hxden.
  assert (Hxden_m :
      m ⊨ ty_denote_gas (cty_depth τ)
        (atom_env_to_lty_env
          (<[x := erase_ty τ]> (store_restrict Σ (ctx_fv (CtxBind x τ)))))
        τ (tret (vfvar x))).
  {
    eapply res_models_kripke; [|exact Hxden].
    etransitivity; [apply res_product_le_r|exact Hle].
  }
  assert (Hxnot : x ∉ dom (ctx_erasure_under Σ Γ)).
  { clear -Hx. better_set_solver. }
  assert (Hxden_comma :
      m ⊨ ty_denote_gas (cty_depth τ)
        (atom_env_to_lty_env (<[x := erase_ty τ]> (ctx_erasure_under Σ Γ)))
        τ (tret (vfvar x))).
  {
    eapply res_models_ty_denote_gas_env_agree_on
      with (X := relevant_lvars τ (tret (vfvar x)));
      [reflexivity| |exact Hxden_m].
    eapply atom_env_to_lty_env_restrict_lvars_agree_on
      with (X := fv_tm (tret (vfvar x)) ∪ fv_cty τ).
    - unfold ty_env_agree_on. intros y Hy.
      cbn [ctx_fv erase_ctx].
      destruct (decide (y = x)) as [->|Hyx].
      + transitivity (Some (erase_ty τ)).
        * apply map_lookup_insert.
        * symmetry. apply map_lookup_insert.
      + exfalso.
        assert (Hyτ : y ∈ fv_cty τ).
        { clear -Hy Hyx. cbn [fv_tm fv_value] in Hy. better_set_solver. }
        pose proof (basic_context_ty_fv_subset ∅ τ Hτ_closed y Hyτ).
        set_solver.
    - relevant_lvars_norm. better_set_solver.
  }
  assert (Hxden_lty :
      m ⊨ ty_denote_gas (cty_depth τ)
        (<[LVFree x := erase_ty τ]>
          (atom_env_to_lty_env (ctx_erasure_under Σ Γ)))
        τ (tret (vfvar x))).
  {
    replace (<[LVFree x := erase_ty τ]>
          (atom_env_to_lty_env (ctx_erasure_under Σ Γ)))
      with (atom_env_to_lty_env (<[x := erase_ty τ]> (ctx_erasure_under Σ Γ))).
    - exact Hxden_comma.
    - apply atom_store_to_lvar_store_insert.
  }
  assert (Hworld :
      m ⊨ basic_world_formula
        (atom_env_to_lty_env (<[x := erase_ty τ]> (ctx_erasure_under Σ Γ)))).
  {
    replace (atom_env_to_lty_env (<[x := erase_ty τ]> (ctx_erasure_under Σ Γ)))
      with (<[LVFree x := erase_ty τ]>
        (atom_env_to_lty_env (ctx_erasure_under Σ Γ))).
    2:{ symmetry. apply atom_store_to_lvar_store_insert. }
    eapply basic_world_insert_of_arg.
    - apply atom_env_to_lty_env_dom_free_notin. exact Hxnot.
    - exact (ctx_denote_under_basic_world Σ Γ m HΓm).
    - exact Hxden_lty.
  }
  eapply ctx_denote_under_comma_intro; [exact HbasicΓ|exact HΓm|].
  eapply ctx_bind_from_inserted_erasure_denotation.
  - exact Hxnot.
  - unfold ty_env_agree_on. intros y Hy.
    pose proof (basic_context_ty_fv_subset ∅ τ Hτ_closed y Hy) as Hyempty.
    set_solver.
  - exact Hworld.
  - exact Hxden_comma.
Qed.

End ContextDenotation.

Notation "'⌊ctx' Γ '⌋[' Σ ']'" :=
  (ctx_erasure_under Σ Γ)
  (at level 20, Γ at level 200, Σ at level 200,
   only parsing).

Notation "'⟦ctx' Γ '⟧[' Σ ']'" :=
  (ctx_denote_under Σ Γ)
  (at level 20, Γ at level 200, Σ at level 200,
   only parsing).

Notation "'⟦ctx' Γ '⟧'" :=
  (ctx_denote Γ)
  (at level 20, Γ at level 200,
   only parsing).

Notation "'⟦ty' τ '⟧[' Σ ';' Γ ']'" :=
  (ty_denote_under Σ Γ τ)
  (at level 20, τ at level 200, Σ at level 200, Γ at level 200,
   only parsing).

Notation "'⟦ty' τ '⟧[' Σ ';' Γ ']' e" :=
  (ty_denote_under Σ Γ τ e)
  (at level 20, τ at level 200, Σ at level 200,
   Γ at level 200, e at level 20,
   only parsing).

Notation "'⌊ctx⌋[' Σ ']' Γ" :=
  (ctx_erasure_under Σ Γ)
  (at level 20, Σ at level 200, Γ at level 200,
   format "⌊ctx⌋[ Σ ]  Γ").

Notation "'⟦ctx⟧[' Σ ']' Γ" :=
  (ctx_denote_under Σ Γ)
  (at level 20, Σ at level 200, Γ at level 200,
   format "⟦ctx⟧[ Σ ]  Γ").

Notation "'⟦ctx⟧' Γ" :=
  (ctx_denote Γ)
  (at level 20, Γ at level 200,
   format "⟦ctx⟧  Γ").

Notation "'⟦ty⟧[' Σ ';' Γ ']' τ" :=
  (ty_denote_under Σ Γ τ)
  (at level 20, Σ at level 200, Γ at level 200, τ at level 200,
   format "⟦ty⟧[ Σ ;  Γ ]  τ").

Notation "'⟦ty⟧[' Σ ';' Γ ']' τ e" :=
  (ty_denote_under Σ Γ τ e)
  (at level 20, Σ at level 200, Γ at level 200,
   τ at level 200, e at level 20,
   format "⟦ty⟧[ Σ ;  Γ ]  τ  e").

Ltac ctx_erasure_under_norm :=
  unfold ctx_erasure_under;
  cbn [ctx_fv erase_ctx ctx_dom];
  type_open_env_syntax_norm;
  store_normalize;
  rewrite ?ctx_erasure_under_minimal, ?ctx_erasure_under_bind,
    ?ctx_erasure_under_comma, ?ctx_erasure_under_star;
  rewrite ?storeA_restrict_dom, ?dom_empty_L, ?dom_singleton_L,
    ?dom_union_L, ?erase_ctx_bind_dom, ?erase_ctx_comma_bind_dom,
    ?erase_ctx_star_bind_dom.

Ltac ctx_erasure_under_norm_in H :=
  unfold ctx_erasure_under in H;
  cbn [ctx_fv erase_ctx ctx_dom] in H;
  type_open_env_syntax_norm_in H;
  store_normalize;
  rewrite ?ctx_erasure_under_minimal in H;
  rewrite ?ctx_erasure_under_bind in H;
  rewrite ?ctx_erasure_under_comma in H;
  rewrite ?ctx_erasure_under_star in H;
  rewrite ?storeA_restrict_dom in H;
  rewrite ?dom_empty_L in H;
  rewrite ?dom_singleton_L in H;
  rewrite ?dom_union_L in H;
  rewrite ?erase_ctx_bind_dom in H;
  rewrite ?erase_ctx_comma_bind_dom in H;
  rewrite ?erase_ctx_star_bind_dom in H.

Ltac ctx_erasure_set :=
  ctx_erasure_under_norm; better_set_solver.

#[global] Instance denot_cty_inst :
    Denotation context_ty (tm -> Formula (V := value)) :=
  fun τ e => ty_denote ∅ τ e.
#[global] Instance ctx_denote_inst :
    Denotation ctx (Formula (V := value)) := ctx_denote.
Arguments denot_cty_inst /.
Arguments ctx_denote_inst /.
