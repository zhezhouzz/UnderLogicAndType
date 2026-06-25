(** * Denotation.Context

    Denotation of type contexts, expressed directly with the new recursive
    context-type denotation. *)

From Denotation Require Export Notation TypeDenote TypePersistBase TypePersistArrow
  TypePersistSingleton TypePersistWandForward TypePersistWandReverse.
From Denotation Require Import TypeEquivCore TypeEquiv TypeEquivFiberBaseResult.
From ContextBasicDenotation Require Import TermExtension.

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

Lemma lvars_fv_atom_env_to_lty_env_dom (Δ : gmap atom ty) :
  lvars_fv (dom (atom_env_to_lty_env Δ)) = dom Δ.
Proof.
  rewrite atom_store_to_lvar_store_dom, lvars_fv_of_atoms.
  reflexivity.
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

Lemma soundness_result_ext_fresh_ctx_erasure
    (Σ : tyctx) Γ e x F (m mx : WfWorldT) :
  m ⊨ ctx_denote_under Σ Γ ->
  expr_result_extension_witness e x F ->
  res_extend_by m F mx ->
  x ∉ dom (ctx_erasure_under Σ Γ).
Proof.
  intros Hctx HF Hext HxΔ.
  pose proof (ctx_denote_under_basic_world Σ Γ m Hctx) as Hworld.
  pose proof (basic_world_formula_atom_env_dom_subset
    (ctx_erasure_under Σ Γ) m Hworld) as HΔworld.
  pose proof (HΔworld x HxΔ) as Hxworld.
  pose proof (res_extend_by_output_fresh m F mx Hext) as Hout_fresh.
  change (ext_out F ## world_dom (m : WorldT)) in Hout_fresh.
  destruct HF as [_ [_ Hout] _].
  assert (x ∈ ext_out F) by (rewrite Hout; set_solver).
  set_solver.
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

Lemma basic_ctx_erase_dom_fresh_none
    (Σ : gmap atom ty) Γ x :
  basic_ctx (dom Σ) Γ ->
  x ∈ dom (erase_ctx Γ) ->
  Σ !! x = None.
Proof.
  intros Hbasic HxΓ.
  apply not_elem_of_dom. intros HΣx.
  pose proof (basic_ctx_erase_dom (dom Σ) Γ Hbasic) as HdomΓ.
  pose proof (basic_ctx_dom_fresh (dom Σ) Γ Hbasic) as HfreshΓ.
  rewrite HdomΓ in HxΓ.
  set_solver.
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
  eapply basic_ctx_erase_dom_fresh_none; eauto.
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
  { eapply basic_ctx_erase_dom_fresh_none; eauto. }
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

Lemma soundness_fresh_erase_ctx_from_context_union
    (Σ : tyctx) Γ y A B C :
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ A ∪ B ∪ C ->
  y ∉ dom (erase_ctx Γ).
Proof.
  intros Hy.
  eapply ctx_erasure_under_notin_erase_ctx.
  intros Hyctx.
  apply Hy.
  apply elem_of_union_l.
  apply elem_of_union_l.
  apply elem_of_union_l.
  apply elem_of_union_r.
  exact Hyctx.
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
  eapply basic_world_formula_subenv.
  - intros v U Hv.
    destruct v as [k|z].
    + rewrite lookup_insert_ne in Hv by discriminate.
      apply map_lookup_union_Some_raw. left. exact Hv.
    + destruct (decide (z = y)) as [->|Hzy].
      * rewrite lookup_insert in Hv.
        apply map_lookup_union_Some_raw. right. split.
        -- apply not_elem_of_dom_1. exact HyΣ.
        -- unfold relevant_env, lty_env_restrict_lvars.
           apply storeA_restrict_lookup_some_2.
           ++ rewrite lookup_insert. exact Hv.
	           ++ unfold relevant_lvars.
	              apply elem_of_union_r.
	              cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys].
	              apply elem_of_singleton. reflexivity.
      * rewrite lookup_insert_ne in Hv by congruence.
        apply map_lookup_union_Some_raw. left. exact Hv.
  - eapply basic_world_formula_union; eauto.
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
        * unfold relevant_lvars, context_tm_support.
          apply elem_of_union_l.
          apply (proj1 (lvars_fv_elem (context_ty_lvars τ) y)).
          rewrite context_ty_lvars_fv. exact Hyτ.
      + apply (proj1 (lookup_singleton_Some x y (erase_ty τ) T)) in Hx
          as [-> ->].
        unfold relevant_env, lty_env_restrict_lvars.
        apply storeA_restrict_lookup_some_2.
        * rewrite atom_store_to_lvar_store_lookup_free.
          apply map_lookup_insert.
        * unfold relevant_lvars, context_tm_support.
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
      + unfold relevant_lvars, context_tm_support in Hv.
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
          apply (storeA_restrict_lookup_some_2 _ _ _ _ HT).
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
      unfold relevant_lvars, context_tm_support in Hv.
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
            apply (storeA_restrict_lookup_some_2 _ _ _ _ Hylookup Hyτ).
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

Lemma ctx_denote_under_star_self_of_persistent
    (Σ : gmap atom ty) Γ :
  basic_ctx (dom Σ) Γ ->
  persistent_formula (ctx_denote_under Σ Γ) ->
  formula_equiv
    (ctx_denote_under Σ (CtxStar Γ Γ))
    (ctx_denote_under Σ Γ).
Proof.
  intros Hbasic Hpersist. split.
  - intros m Hstar.
    pose proof (ctx_denote_under_star_elim Σ Γ Γ m Hstar)
      as (m1 & m2 & Hc & Hle & HΓ & _).
    eapply res_models_kripke; [|exact HΓ].
    etransitivity; [apply res_product_le_l|exact Hle].
  - intros m HΓ.
    pose proof (proj2 (persistent_star_self
      (ctx_denote_under Σ Γ) Hpersist) m HΓ) as Hstar_body.
    assert (HΓmin :
        m ⊨ ctx_denote_under
          (store_restrict Σ (ctx_fv (CtxStar Γ Γ))) Γ).
    {
      rewrite ctx_denote_under_minimal.
      rewrite ctx_denote_under_minimal in HΓ.
      cbn [ctx_fv].
      replace (ctx_fv Γ ∪ ctx_fv Γ) with (ctx_fv Γ) by set_solver.
      rewrite storeA_restrict_twice_same.
      exact HΓ.
    }
    cbn [ctx_denote_under].
    rewrite res_models_and_iff. split.
    + eapply ctx_erasure_under_star_basic_world; eauto;
        exact (ctx_denote_under_basic_world _ _ _ HΓmin).
    + cbn [ctx_fv].
      replace (ctx_fv Γ ∪ ctx_fv Γ) with (ctx_fv Γ) by set_solver.
      rewrite <- (ctx_denote_under_minimal Σ Γ).
      exact Hstar_body.
Qed.

Lemma formula_fv_ctx_bind_persist_subset
    (Σ : gmap atom ty) x τ :
  formula_fv (ctx_denote_under Σ (CtxBind x (CTPersist τ))) ⊆
  fv_cty τ ∪ {[x]}.
Proof.
  cbn [ctx_denote_under ctx_fv erase_ctx].
  rewrite formula_fv_and, formula_fv_basic_world_formula.
  intros a Ha.
  rewrite elem_of_union in Ha.
  destruct Ha as [Hbasic_fv|Hty_fv].
  - rewrite lvars_fv_atom_env_to_lty_env_dom in Hbasic_fv.
    apply elem_of_dom in Hbasic_fv as [T HT].
    apply map_lookup_union_Some_raw in HT as [HT|[_ HT]].
    + apply elem_of_dom_2 in HT.
      store_restrict_normalize.
      cbn [ctx_fv context_ty_lvars context_ty_lvars_at] in HT.
      better_set_solver.
    + change (({[x := erase_ty (CTPersist τ)]} : gmap atom ty) !! a =
        Some T) in HT.
      apply (proj1 (lookup_singleton_Some x a (erase_ty (CTPersist τ)) T))
        in HT as [-> _].
      set_solver.
  - pose proof (ty_denote_gas_fv_subset (cty_depth (CTPersist τ))
      (atom_env_to_lty_env
        (<[x:=erase_ty (CTPersist τ)]>
          (store_restrict Σ (ctx_fv (CtxBind x (CTPersist τ))))))
      (CTPersist τ) (tret (vfvar x))) as Hfv.
    cbn [fv_tm fv_value context_ty_lvars context_ty_lvars_at] in Hfv.
    set_solver.
Qed.

Lemma ctx_bind_persist_singleton_projection
    (Σ : gmap atom ty) x τ (m : WfWorldT) :
  basic_ctx (dom Σ) (CtxBind x (CTPersist τ)) ->
  m ⊨ ctx_denote_under Σ (CtxBind x (CTPersist τ)) ->
  exists σ : StoreT,
    dom (σ : StoreT) = fv_cty τ ∪ {[x]} /\
    res_restrict m (fv_cty τ ∪ {[x]}) =
      (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorldT).
Proof.
  intros Hbasic Hctx.
  destruct Hbasic as [HxΣ Hτ].
  pose proof (ctx_denote_under_bind_inv Σ x (CTPersist τ) m Hctx)
    as Hden.
  unfold ty_denote in Hden.
  cbn [cty_depth] in Hden.
  set (Σx :=
    atom_env_to_lty_env
      (<[x := erase_ty (CTPersist τ)]>
        (store_restrict Σ (ctx_fv (CtxBind x (CTPersist τ)))))).
  change (m ⊨ ty_denote_gas (S (cty_depth τ)) Σx
    (CTPersist τ) (tret (vfvar x))) in Hden.
  pose proof (ty_denote_gas_ret_fvar_world_dom
    (S (cty_depth τ)) Σx (CTPersist τ) x m Hden) as Hxm.
  pose proof (ty_denote_gas_ret_fvar_basic_world_singleton
    (S (cty_depth τ)) Σx (CTPersist τ) x m Hden) as Hbasic_x.
  pose proof (basic_world_formula_wfworld_closed_on_atoms
    (<[LVFree x := erase_ty (CTPersist τ)]> (∅ : lty_env))
    ({[x]} : aset) m ltac:(set_solver) Hbasic_x) as Hclosed_x_m.
  pose proof (ty_denote_gas_guard
    (S (cty_depth τ)) Σx (CTPersist τ) (tret (vfvar x)) m Hden)
    as Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [_ [Hworld_rel [_ Htotal]]].
  assert (Hrel_dom :
      lvars_fv (dom (relevant_env Σx (CTPersist τ) (tret (vfvar x)))) ⊆
      world_dom (m : WorldT)).
  {
    apply basic_world_formula_models_iff in Hworld_rel as [_ [Hdom _]].
    exact Hdom.
  }
  set (Dres := dom (relevant_env Σx (CTPersist τ) (tret (vfvar x)))).
  set (y := fresh_for
    (world_dom (m : WorldT) ∪ fv_cty τ ∪ {[x]} ∪ lvars_fv Dres ∪
      fv_tm (tret (vfvar x)))).
	  assert (Hyfresh :
	      y ∉ world_dom (m : WorldT) ∪ fv_cty τ ∪ {[x]} ∪ lvars_fv Dres ∪
	        fv_tm (tret (vfvar x))).
	  { subst y. apply fresh_for_not_in. }
	  assert (Hy_m : y ∉ world_dom (m : WorldT)).
	  { intros Hy. apply Hyfresh. repeat apply elem_of_union_l. exact Hy. }
	  assert (Hy_D : LVFree y ∉ Dres).
	  {
	    intros HyD.
	    assert (HyDfv : y ∈ lvars_fv Dres).
	    { apply lvars_fv_elem. exact HyD. }
	    apply Hyfresh. rewrite !elem_of_union. left. right. exact HyDfv.
	  }
  assert (Hlc_D : lc_lvars Dres).
  { subst Dres. apply relevant_env_closed.
    subst Σx. apply atom_store_to_lvar_store_closed. }
  assert (Htm_D : tm_lvars (tret (vfvar x)) ⊆ Dres).
	  {
	    subst Dres Σx.
	    intros v Hv.
	    unfold relevant_env, relevant_lvars, lty_env_restrict_lvars.
	    cbn [context_ty_lvars context_ty_lvars_at tm_lvars tm_lvars_at
	      value_lvars_at lvar_value_keys] in Hv.
	    assert (Hvx : v = LVFree x).
	    {
	      apply elem_of_singleton in Hv. exact Hv.
	    }
	    subst v.
	    apply elem_of_dom.
	    exists (erase_ty (CTPersist τ)).
	    apply storeA_restrict_lookup_some_2.
	    - rewrite atom_store_to_lvar_store_lookup_free.
	      apply map_lookup_insert.
    - unfold context_tm_support.
      cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys].
	      apply elem_of_union_r. apply elem_of_singleton. reflexivity.
	  }
  destruct (expr_result_extension_witness_on_exists
    (lvars_fv Dres) (tret (vfvar x)) y) as [Fx HFx].
  - intros a Ha.
    apply lvars_fv_elem.
    apply Htm_D.
    apply (proj1 (lvars_fv_elem (tm_lvars (tret (vfvar x))) a)).
	    rewrite tm_lvars_fv. exact Ha.
		  - intros HyD_atoms.
        apply Hyfresh. rewrite !elem_of_union. left. right. exact HyD_atoms.
  - destruct (res_extend_by_exists m Fx) as [my Hext].
    { constructor.
      - change (ext_in Fx ⊆ world_dom (m : WorldT)).
        destruct HFx as [_ _ [Hin _] _].
        rewrite Hin. exact Hrel_dom.
      - change (ext_out Fx ## world_dom (m : WorldT)).
      destruct HFx as [_ _ [Hin Hout] _].
        rewrite Hout.
        intros a Ha_out Ha_m.
        apply elem_of_singleton in Ha_out. subst a.
        exact (Hy_m Ha_m). }
    pose proof (res_extend_by_dom m Fx my Hext) as Hdom_my.
    pose proof (res_extend_by_restrict_base m Fx my Hext) as Hbase_my.
    destruct HFx as [_ _ [Hin_Fx Hout_Fx] Hrel_Fx].
    assert (Hdom_my' :
        world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]}).
    {
      rewrite Hdom_my.
      change (extA_out Fx) with (ext_out Fx).
      rewrite Hout_Fx. reflexivity.
    }
    assert (Hres_at :
        my ⊨ expr_result_formula_at Dres (tret (vfvar x)) (LVFree y)).
    {
      eapply expr_result_formula_at_of_result_extends_on.
      - exact Hlc_D.
      - exact Htm_D.
      - exact Hy_D.
      - exact Hrel_dom.
      - constructor.
        + intros a Ha. apply lvars_fv_elem. apply Htm_D.
          apply (proj1 (lvars_fv_elem (tm_lvars (tret (vfvar x))) a)).
          rewrite tm_lvars_fv. exact Ha.
	        + intros HyD_atoms.
            apply Hyfresh. rewrite !elem_of_union. left. right. exact HyD_atoms.
        + split; [exact Hin_Fx|exact Hout_Fx].
        + exact Hrel_Fx.
      - exact Hext.
      - apply expr_total_formula_to_atom_world. exact Htotal.
    }
    pose proof (ty_denote_gas_persist_open_result
      (cty_depth τ) Σx τ (tret (vfvar x)) y m my
      ltac:(subst Σx; apply atom_store_to_lvar_store_closed)
      ltac:(constructor; constructor)
      ltac:(cbn [fv_tm fv_value]; intros Hyx; apply Hyfresh;
        clear -Hyx; set_solver)
	      ltac:(subst Dres; intros Hyrel; apply Hy_D;
	        rewrite <- lvars_fv_elem; exact Hyrel)
      Hden Hy_m Hdom_my' Hbase_my Hres_at) as Hpersist_open.
	    rewrite formula_open_persist in Hpersist_open.
	    rewrite formula_open_ty_denote_gas_singleton in Hpersist_open.
		    2:{
		      rewrite typed_lty_env_bind_lvars_fv_dom.
		      subst Dres. intros Hyrel.
		      apply Hy_D. apply lvars_fv_elem. exact Hyrel.
		    }
	    2:{
	      cbn [fv_tm fv_value].
	      intros Hybad.
	      clear -Hybad. set_solver.
	    }
	    2:{
	      rewrite cty_shift_fv.
	      intros Hyτ. apply Hyfresh.
	      clear -Hyτ. set_solver.
	    }
	    apply res_models_persist_iff in Hpersist_open
	      as [σy [Hdomσy [Hsingle_y _]]].
	    assert (HxA : x ∉ fv_cty τ).
	    {
	      clear -HxΣ Hτ.
	      pose proof (basic_context_ty_fv_subset (dom Σ) (CTPersist τ) Hτ)
	        as Hτfv.
	      cbn [context_ty_lvars context_ty_lvars_at] in Hτfv.
	      set_solver.
	    }
	    assert (Hlcτ : cty_lc_at 0 τ).
	    {
	      pose proof (basic_context_ty_lc (dom Σ) (CTPersist τ) Hτ)
	        as Hlc.
	      cbn [cty_lc_at] in Hlc.
	      exact Hlc.
	    }
	    assert (HA_D : fv_cty τ ⊆ lvars_fv Dres).
	    {
	      intros a Ha.
	      apply lvars_fv_elem.
	      subst Dres Σx.
	      unfold relevant_env, lty_env_restrict_lvars.
	      apply elem_of_dom.
	      pose proof (basic_context_ty_fv_subset (dom Σ) (CTPersist τ) Hτ)
	        as Hτfv.
	      cbn [context_ty_lvars context_ty_lvars_at] in Hτfv.
	      pose proof (Hτfv a Ha) as HaΣ.
	      apply elem_of_dom in HaΣ as [T HT].
	      exists T.
	      apply storeA_restrict_lookup_some_2.
	      - rewrite atom_store_to_lvar_store_lookup_free.
		        transitivity
		          ((store_restrict Σ (ctx_fv (CtxBind x (CTPersist τ))) : gmap atom ty)
		            !! a).
		        + apply map_lookup_insert_ne. intros ->. exact (HxA Ha).
		        + apply storeA_restrict_lookup_some_2.
		          * exact HT.
		          * cbn [ctx_fv context_ty_lvars context_ty_lvars_at]. exact Ha.
		      - unfold relevant_lvars, context_tm_support.
	        apply elem_of_union_l.
	        rewrite <- lvars_fv_elem.
	        rewrite context_ty_lvars_fv.
	        exact Ha.
	    }
	    assert (HA_m : fv_cty τ ⊆ world_dom (m : WorldT)).
	    { clear -HA_D Hrel_dom. set_solver. }
	    assert (HyA : y ∉ fv_cty τ).
	    { clear -Hyfresh. set_solver. }
	    assert (Hclosed_x_my : wfworld_closed_on ({[x]} : aset) my).
	    {
	      eapply wfworld_closed_on_le.
	      - intros a Ha. apply elem_of_singleton in Ha. subst a. exact Hxm.
	      - rewrite <- Hbase_my. apply res_restrict_le.
	      - exact Hclosed_x_m.
	    }
	    assert (HAy_σy : fv_cty τ ∪ {[y]} ⊆ dom (σy : StoreT)).
	    {
	      rewrite Hdomσy.
	      etransitivity.
	      2:{
	        apply (relevant_env_fv_ty_denote_gas_subset_formula
	          (cty_depth τ)
	          (lvar_store_open_one 0 y
	            (typed_lty_env_bind
	              (relevant_env Σx (CTPersist τ) (tret (vfvar x)))
	              (erase_ty (CTPersist τ))))
	          (cty_open 0 y (cty_shift 0 τ))
	          (open_tm 0 (vfvar y) (tret (vbvar 0)))).
	      }
	      intros a HaAy.
	      apply lvars_fv_elem.
	      unfold relevant_env, lty_env_restrict_lvars.
	      apply elem_of_dom.
	      apply elem_of_union in HaAy as [Haτ|Hay].
	      - pose proof (HA_D a Haτ) as HaDfv.
	        apply lvars_fv_elem in HaDfv.
	        apply elem_of_dom in HaDfv as [T HT].
	        exists T.
	        apply storeA_restrict_lookup_some_2.
	        + rewrite lty_env_open_one_typed_bind_lookup_free_ne
	            by (clear -HyA Haτ; set_solver).
	          exact HT.
		        + unfold relevant_lvars, context_tm_support.
	          apply elem_of_union_l.
	          rewrite cty_open_shift_from_lc_fresh; [|exact Hlcτ|exact HyA].
	          rewrite <- lvars_fv_elem, context_ty_lvars_fv.
	          exact Haτ.
	      - apply elem_of_singleton in Hay. subst a.
	        exists (erase_ty (CTPersist τ)).
	        apply storeA_restrict_lookup_some_2.
		        + apply lty_env_open_one_typed_bind_lookup_current.
				        + unfold relevant_lvars, context_tm_support.
			          apply elem_of_union_r.
			          cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys
                  open_tm open_value].
			          apply elem_of_singleton. reflexivity.
	    }
	    assert (Hsingle_Ay :
	        res_restrict my (fv_cty τ ∪ {[y]}) =
	        (exist _ (singleton_world
	          (store_restrict σy (fv_cty τ ∪ {[y]})))
	          (wf_singleton_world
	            (store_restrict σy (fv_cty τ ∪ {[y]}))) : WfWorldT)).
	    {
	      rewrite <- Hdomσy in Hsingle_y.
		      transitivity (res_restrict (res_restrict my (dom (σy : StoreT)))
		        (fv_cty τ ∪ {[y]})).
		      - rewrite res_restrict_restrict_eq.
		        replace (dom (σy : StoreT) ∩ (fv_cty τ ∪ {[y]}))
		          with (fv_cty τ ∪ {[y]}).
			        2:{
			          apply set_eq. intros a. split.
			          - intros Ha. apply elem_of_intersection. split; [|exact Ha].
			            exact (HAy_σy a Ha).
			          - intros Ha. apply elem_of_intersection in Ha as [_ Ha].
			            exact Ha.
			        }
		        reflexivity.
	      - rewrite Hsingle_y. apply res_restrict_singleton_world.
	    }
	    pose proof (res_restrict_singleton_pullback_ret_fvar_result
	      (fv_cty τ) Dres x y m my
	      (store_restrict σy (fv_cty τ ∪ {[y]}))
	      HA_m Hxm Hy_m HxA HyA Htm_D
	      Hy_D
	      Hres_at
	      Hclosed_x_my
	      Hdom_my' Hbase_my
	      Hsingle_Ay) as [σx [Hdomσx Hsingle_x]].
    exists σx. split; [exact Hdomσx|exact Hsingle_x].
Qed.

Lemma ctx_bind_persist_persistent
    (Σ : gmap atom ty) x τ :
  basic_ctx (dom Σ) (CtxBind x (CTPersist τ)) ->
  persistent_formula (ctx_denote_under Σ (CtxBind x (CTPersist τ))).
Proof.
  intros Hbasic.
  apply persistent_formula_of_singleton_projection_subset.
  intros m Hctx.
  destruct (ctx_bind_persist_singleton_projection Σ x τ m Hbasic Hctx)
    as [σ [Hdom Hrestrict]].
  exists (fv_cty τ ∪ {[x]}), σ.
  repeat split.
  - apply formula_fv_ctx_bind_persist_subset.
  - exact Hdom.
  - exact Hrestrict.
Qed.

Theorem ctx_bind_persist_star_dup
    (Σ : gmap atom ty) x τ :
  basic_ctx (dom Σ) (CtxBind x (CTPersist τ)) ->
  formula_equiv
    (ctx_denote_under Σ
      (CtxStar (CtxBind x (CTPersist τ))
               (CtxBind x (CTPersist τ))))
    (ctx_denote_under Σ (CtxBind x (CTPersist τ))).
Proof.
  intros Hbasic.
  apply ctx_denote_under_star_self_of_persistent; [exact Hbasic|].
  apply ctx_bind_persist_persistent. exact Hbasic.
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
