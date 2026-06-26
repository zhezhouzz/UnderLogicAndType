(** * ContextTyping.PrimOpConcreteContext

    Concrete top/top primitive-operation context for the current core
    operators.

    The core primitives are unary.  The generator operations ignore their
    argument operationally, but the erased core typing still gives them an
    argument base type.  The context type below therefore uses an
    over-approximate top argument and a top precise result:

      [{: arg | top }] -> [{: ret | top } ∩ [: ret | top]]

    This intentionally does not record the deterministic graph of [eq0],
    [plus1], or [minus1].  It is the weakest concrete context needed by the
    parameterized soundness theorem and works uniformly for nondeterministic
    [boolGen]/[natGen]. *)

From CoreLang Require Import BasicTyping BasicTypingProps SmallStep StrongNormalization.
From ContextLogic Require Import FormulaSemantics.
From ContextTypeLanguage Require Import WF.
From Denotation Require Import Context ConstDenote TypeDenote TypeEquivCore
  TypeEquivFiberBaseCore TypeEquiv DenotationSetMapFacts.
From ContextTyping Require Import PrimOpContext.

Definition topq : type_qualifier := qual_top.

Definition concrete_primop_sig (op : prim_op) : primop_sig :=
  match prim_op_type op with
  | (arg_b, ret_b) => mk_primop_sig arg_b topq ret_b topq
  end.

Definition concrete_Φ : primop_ctx := concrete_primop_sig.

Local Ltac primop_rewrite_tm_support :=
  repeat match goal with
  | |- context [lvars_at_depth ?d (tm_lvars ?e)] =>
      rewrite (tm_lvars_depth e d)
  | H : context [lvars_at_depth ?d (tm_lvars ?e)] |- _ =>
      rewrite (tm_lvars_depth e d) in H
  end.

Local Ltac primop_unfold_formula_lvars_atoms :=
  unfold ty_guard_formula, context_ty_wf_formula, basic_world_formula,
    expr_basic_typing_formula, expr_total_formula, expr_result_formula,
    expr_result_formula_at, expr_result_atom_formula, FFiberAtom;
  cbn [formula_lvars_at];
  unfold context_ty_wf_qual, basic_world_qual,
    expr_basic_typing_qual, expr_total_qual, expr_result_qual;
  cbn [qual_dom qual_vars qual_lvars].

Local Ltac primop_normalize_denot_formula_lvars :=
  primop_unfold_formula_lvars_atoms;
  repeat rewrite ?lvars_at_depth_union;
  primop_rewrite_tm_support;
  rewrite ?context_ty_lvars_depth;
  rewrite ?tm_lvars_at_shift_under by lia;
  rewrite ?context_ty_lvars_at_shift_under by lia;
  rewrite ?lvars_at_depth_shift_under by lia;
  rewrite ?value_lvars_at_bound0_under;
  rewrite ?tm_lvars_at_tret_bound0_under;
  rewrite ?lvars_at_depth_dom_singleton_bound0_succ;
  rewrite ?lvars_at_depth_singleton_bound0_succ;
  rewrite ?lvars_at_depth_empty;
  cbn [context_ty_lvars_at tm_lvars_at value_lvars_at].

Lemma primop_result_ty_eq op :
  primop_result_ty (concrete_Φ op) =
  precise_ty (prim_ret_base (concrete_Φ op)) topq.
Proof.
  unfold primop_result_ty, concrete_Φ, concrete_primop_sig.
  destruct (prim_op_type op) as [arg_b ret_b]. reflexivity.
Qed.

Lemma primop_arg_ty_eq op :
  primop_arg_ty (concrete_Φ op) =
  over_ty (prim_arg_base (concrete_Φ op)) qual_top.
Proof.
  unfold primop_arg_ty, concrete_Φ, concrete_primop_sig.
  destruct (prim_op_type op) as [arg_b ret_b]. reflexivity.
Qed.

Lemma qual_top_lvars_wf_at d D :
  lvars_wf_at d D (qual_vars topq).
Proof.
  unfold topq, qual_top. cbn [qual_vars qual_lvars].
  intros v Hv. set_solver.
Qed.

Lemma over_top_basic b :
  basic_context_ty ∅ (CTOver b topq).
Proof.
  cbn [basic_context_ty wf_context_ty_at].
  apply qual_top_lvars_wf_at.
Qed.

Lemma precise_top_wf_at d D b :
  wf_context_ty_at d D (precise_ty b topq).
Proof.
  unfold precise_ty, over_ty, under_ty.
  cbn [wf_context_ty_at erase_ty].
  repeat split; try reflexivity; apply qual_top_lvars_wf_at.
Qed.

Lemma primop_erasure op :
  primop_erasure_ok op (concrete_Φ op).
Proof.
  unfold primop_erasure_ok, concrete_Φ, concrete_primop_sig.
  destruct (prim_op_type op) as [arg_b ret_b]. reflexivity.
Qed.

Lemma primop_arg_basic op :
  basic_context_ty ∅ (primop_arg_ty (concrete_Φ op)).
Proof.
  rewrite primop_arg_ty_eq.
  apply over_top_basic.
Qed.

Lemma primop_result_wf op :
  wf_context_ty_at 1 ∅ (primop_result_ty (concrete_Φ op)).
Proof.
  rewrite primop_result_ty_eq.
  apply precise_top_wf_at.
Qed.

Lemma prim_step_total_for_base op c arg_b ret_b :
  prim_op_type op = (arg_b, ret_b) ->
  base_ty_of_const c = arg_b ->
  exists c', prim_step op c c'.
Proof.
  intros Hop Hbase.
  destruct op; cbn [prim_op_type] in Hop;
    injection Hop as <- <-; destruct c; cbn in Hbase; try discriminate.
  - exists (cbool (n =? 0)). constructor.
  - exists (cnat (S n)). constructor.
  - exists (cnat (Nat.pred n)). constructor.
  - exists (cbool true). constructor.
  - exists (cnat 0). constructor.
Qed.

Lemma res_models_atom_top (m : WfWorldT) :
  m ⊨ FAtom topq.
Proof.
  apply res_models_atom_exact_iff.
  unfold qualifier_exact_denote, topq, qual_top.
  cbn [qual_vars qual_lvars qual_prop].
  assert (Hlc : lc_lvars (∅ : lvset)).
  { intros v Hv. set_solver. }
  assert (Hsub : lvars_fv (∅ : lvset) ⊆ world_dom (m : WorldT)).
  { rewrite lvars_fv_empty. intros a Ha. set_solver. }
  exists Hlc. exists Hsub.
  intros s. split; [intros _|intros _; exact I].
  destruct (world_wf m) as [[σ Hσ] _].
  assert (Hsubσ : lvars_fv (∅ : lvset) ⊆ dom (σ : StoreT)).
  { rewrite lvars_fv_empty. set_solver. }
  replace s with (lstore_on_lift_store (∅ : lvset) σ Hlc Hsubσ).
  - apply lstore_in_lworld_on_lift_store_of_world. exact Hσ.
  - apply (lstore_on_ext (∅ : lvset)).
    unfold lstore_on_lift_store, LStore.
    cbn [lso_store storeAO_store].
    symmetry. apply (map_eq (M:=gmap logic_var)). intros v.
    destruct v as [k|a].
    + transitivity (@None value).
      * destruct ((lso_store s : gmap logic_var value) !! LVBound k) eqn:Hs.
        -- exfalso.
           assert (LVBound k ∈ dom (lso_store s : gmap logic_var value)).
           { eapply elem_of_dom_2. exact Hs. }
           pose proof (lso_dom s) as Hdoms.
           change (dom (lso_store s : gmap logic_var value) = (∅ : lvset))
             in Hdoms.
           rewrite Hdoms in H.
           rewrite elem_of_empty in H. contradiction.
        -- reflexivity.
      * symmetry. apply storeA_restrict_lookup_none_r. set_solver.
    + transitivity (@None value).
      * destruct ((lso_store s : gmap logic_var value) !! LVFree a) eqn:Hs.
        -- exfalso.
           assert (LVFree a ∈ dom (lso_store s : gmap logic_var value)).
           { eapply elem_of_dom_2. exact Hs. }
           pose proof (lso_dom s) as Hdoms.
           change (dom (lso_store s : gmap logic_var value) = (∅ : lvset))
             in Hdoms.
           rewrite Hdoms in H.
           rewrite elem_of_empty in H. contradiction.
        -- reflexivity.
	      * symmetry. apply storeA_restrict_lookup_none_r. set_solver.
Qed.

Lemma top_over_under_formula (m : WfWorldT) :
  m ⊨ FOver (FAtom topq) /\
  m ⊨ FUnder (FAtom topq).
Proof.
  split;
    [apply res_models_over_intro_same_from_model
    |apply res_models_under_intro_same_from_model];
    apply res_models_atom_top.
Qed.

Lemma top_result_body (m : WfWorldT) :
  m ⊨ FFibVars ∅ (FOver (FAtom topq)) /\
  m ⊨ FFibVars ∅ (FUnder (FAtom topq)).
Proof.
  destruct (top_over_under_formula m) as [Hover Hunder].
  split; apply res_models_fibvars_empty_intro; assumption.
Qed.

Lemma over_top_denotation_gas
    gas b Σ e (m : WfWorldT) :
  m ⊨ ty_guard_formula (relevant_env Σ (CTOver b topq) e)
      (CTOver b topq) e ->
  m ⊨ ty_denote_gas gas Σ (CTOver b topq) e.
Proof.
  destruct gas as [|gas']; intros Hguard.
  - cbn [ty_denote_gas]. rewrite res_models_and_iff. split; [exact Hguard|apply res_models_true].
  - cbn [ty_denote_gas].
    rewrite res_models_and_iff. split; [exact Hguard|].
    eapply res_models_forall_rev_intro.
    + assert (HΣscope :
        lvars_fv (dom (relevant_env Σ (CTOver b topq) e)) ⊆
          world_dom (m : WorldT)).
      {
        unfold ty_guard_formula in Hguard.
        repeat rewrite res_models_and_iff in Hguard.
        destruct Hguard as [_ [Hworld _]].
        apply basic_world_formula_models_iff in Hworld as [_ [Hscope _]].
        exact Hscope.
      }
      assert (Hzero : m ⊨ ty_denote_gas 0 Σ (CTOver b topq) e).
      {
        cbn [ty_denote_gas]. rewrite res_models_and_iff.
        split; [exact Hguard|apply res_models_true].
      }
      pose proof (ty_denote_gas_zero_tm_lvars_dom
        Σ (CTOver b topq) e m Hzero) as Htmrel.
      assert (Hefv :
        fv_tm e ⊆ lvars_fv (dom (relevant_env Σ (CTOver b topq) e))).
      {
        intros a Ha.
        rewrite <- tm_lvars_fv in Ha.
        apply lvars_fv_elem.
        apply Htmrel.
        apply lvars_fv_elem in Ha. exact Ha.
      }
      unfold formula_scoped_in_world.
      formula_fv_syntax_norm.
      cbn [formula_lvars formula_lvars_at].
      primop_normalize_denot_formula_lvars.
      pose proof (lvars_at_depth_relevant_env_subset_relevant
        0 Σ (CTOver b topq) e).
      pose proof (expr_result_shift0_lvars_subset 0
        (dom (relevant_env Σ (CTOver b topq) e)) e).
      rewrite ?lvars_fv_union, ?lvars_fv_empty,
        ?lvars_fv_lvars_at_depth.
      rewrite ?tm_lvars_at_fv.
      unfold topq, qual_top.
      cbn [qual_vars qual_lvars].
      rewrite ?lvars_fv_empty.
      intros a Ha.
      set_unfold in Ha.
      set_unfold in HΣscope.
      set_unfold in Hefv.
      repeat match goal with
      | H : _ \/ _ |- _ => destruct H as [H|H]
      | H : False |- _ => contradiction
      end;
        try solve [apply HΣscope; assumption
          | apply HΣscope; apply Hefv; assumption
          | contradiction].
      match goal with
      | H : a ∈ lvars_fv ((∅ : lvset) ∖ {[LVBound 0]}) |- _ =>
          exfalso;
          assert (((∅ : lvset) ∖ {[LVBound 0]}) = ∅) as Hempty by set_solver;
          rewrite Hempty, lvars_fv_empty in H;
          rewrite elem_of_empty in H; exact H
      end.
    + exists (world_dom (m : WorldT) ∪ formula_fv
        (expr_result_formula_at
          (lvars_shift_from 0 (dom (relevant_env Σ (CTOver b topq) e)))
          (tm_shift 0 e) (LVBound 0))).
      intros y Hy my Hdom Hrestrict.
      cbn [formula_open].
      eapply res_models_impl_intro.
      * unfold formula_scoped_in_world.
        assert (HΣscope :
          lvars_fv (dom (relevant_env Σ (CTOver b topq) e)) ⊆
            world_dom (m : WorldT)).
        {
          unfold ty_guard_formula in Hguard.
          repeat rewrite res_models_and_iff in Hguard.
          destruct Hguard as [_ [Hworld _]].
          apply basic_world_formula_models_iff in Hworld as [_ [Hscope _]].
          exact Hscope.
        }
        assert (HΣlc : lc_lvars (dom (relevant_env Σ (CTOver b topq) e))).
        {
          unfold ty_guard_formula in Hguard.
          repeat rewrite res_models_and_iff in Hguard.
          destruct Hguard as [_ [Hworld _]].
          apply basic_world_formula_models_iff in Hworld as [Hlc _].
          exact Hlc.
        }
        assert (Hlc_tm : lc_tm e).
        {
          unfold ty_guard_formula in Hguard.
          repeat rewrite res_models_and_iff in Hguard.
          destruct Hguard as [_ [_ [Hbasic _]]].
          apply expr_basic_typing_formula_models_iff in Hbasic as [_ [_ Hty]].
          eapply basic_tm_has_ltype_lc; [exact HΣlc|exact Hty].
        }
        assert (Hzero : m ⊨ ty_denote_gas 0 Σ (CTOver b topq) e).
        {
          cbn [ty_denote_gas]. rewrite res_models_and_iff.
          split; [exact Hguard|apply res_models_true].
        }
        pose proof (ty_denote_gas_zero_tm_lvars_dom
          Σ (CTOver b topq) e m Hzero) as Htmrel.
        assert (Hefv :
          fv_tm e ⊆ lvars_fv (dom (relevant_env Σ (CTOver b topq) e))).
        {
          intros a Ha.
          rewrite <- tm_lvars_fv in Ha.
          apply lvars_fv_elem.
          apply Htmrel.
          apply lvars_fv_elem in Ha. exact Ha.
        }
        rewrite formula_open_expr_result_formula_at_shift0.
        formula_fv_syntax_norm.
        cbn [formula_lvars formula_lvars_at].
        primop_normalize_denot_formula_lvars.
        rewrite ?lvars_fv_union, ?lvars_fv_empty,
          ?lvars_fv_lvars_at_depth, ?tm_lvars_at_fv,
          ?lvars_fv_singleton_free, ?lvars_shift_from_fv.
        unfold topq, qual_top.
        cbn [qual_vars qual_lvars].
        rewrite ?lvars_fv_empty.
        rewrite Hdom.
        intros a Ha.
        set_unfold in Ha.
        repeat match goal with
        | H : _ \/ _ |- _ => destruct H as [H|H]
        | H : False |- _ => contradiction
        | H : _ = _ |- _ => subst
        end;
          try solve [apply elem_of_union_l; apply HΣscope; assumption
            | apply elem_of_union_l; apply HΣscope; apply Hefv; assumption
            | apply elem_of_union_r; apply elem_of_singleton_2; reflexivity
            | apply lvars_shift_from_lc; exact HΣlc
            | match goal with
              | H : a ∈ lvars_fv (dom ?R) |- _ =>
                  apply elem_of_union_l; apply HΣscope; exact H
              end
            | match goal with
              | H : a ∈ lvars_fv ?D |- _ =>
                  exfalso;
                  assert (D = ∅) as Hempty
                    by (rewrite ?set_swap_empty; set_solver);
                  rewrite Hempty, lvars_fv_empty in H;
                  rewrite elem_of_empty in H; exact H
              end].
        try (apply lvars_shift_from_lc; exact HΣlc).
        try (rewrite lvars_shift_from_fv;
          intros HyD; apply Hy; apply elem_of_union_l; apply HΣscope; exact HyD).
        try (intros Hye; apply Hy; apply elem_of_union_l;
          apply HΣscope; apply Hefv; exact Hye).
        try exact Hlc_tm.
        try (let Hbad := fresh "Hbad" in
          intro Hbad; apply Hy; apply elem_of_union_l;
          apply HΣscope; apply Hefv; exact Hbad).
      * intros _.
        destruct (top_result_body my) as [Hover _].
        replace (set_swap (LVBound 0) (LVFree y) ((∅ : lvset) ∖ {[LVBound 0]})) with (∅ : lvset)
          by set_solver.
        replace (qual_open_atom 0 y topq) with topq by reflexivity.
        replace (set_swap (LVBound 0) (LVFree y) (qual_vars topq ∖ {[LVBound 0]})) with (∅ : lvset)
          by (unfold topq, qual_top; cbn [qual_vars qual_lvars]; set_solver).
        exact Hover.
Qed.

Lemma under_top_denotation_gas
    gas b Σ e (m : WfWorldT) :
  m ⊨ ty_guard_formula (relevant_env Σ (CTUnder b topq) e)
      (CTUnder b topq) e ->
  m ⊨ ty_denote_gas gas Σ (CTUnder b topq) e.
Proof.
  destruct gas as [|gas']; intros Hguard.
  - cbn [ty_denote_gas]. rewrite res_models_and_iff. split; [exact Hguard|apply res_models_true].
  - cbn [ty_denote_gas].
    rewrite res_models_and_iff. split; [exact Hguard|].
    eapply res_models_forall_rev_intro.
    + assert (HΣscope :
        lvars_fv (dom (relevant_env Σ (CTUnder b topq) e)) ⊆
          world_dom (m : WorldT)).
      {
        unfold ty_guard_formula in Hguard.
        repeat rewrite res_models_and_iff in Hguard.
        destruct Hguard as [_ [Hworld _]].
        apply basic_world_formula_models_iff in Hworld as [_ [Hscope _]].
        exact Hscope.
      }
      assert (Hzero : m ⊨ ty_denote_gas 0 Σ (CTUnder b topq) e).
      {
        cbn [ty_denote_gas]. rewrite res_models_and_iff.
        split; [exact Hguard|apply res_models_true].
      }
      pose proof (ty_denote_gas_zero_tm_lvars_dom
        Σ (CTUnder b topq) e m Hzero) as Htmrel.
      assert (Hefv :
        fv_tm e ⊆ lvars_fv (dom (relevant_env Σ (CTUnder b topq) e))).
      {
        intros a Ha.
        rewrite <- tm_lvars_fv in Ha.
        apply lvars_fv_elem.
        apply Htmrel.
        apply lvars_fv_elem in Ha. exact Ha.
      }
      unfold formula_scoped_in_world.
      formula_fv_syntax_norm.
      cbn [formula_lvars formula_lvars_at].
      primop_normalize_denot_formula_lvars.
      pose proof (lvars_at_depth_relevant_env_subset_relevant
        0 Σ (CTUnder b topq) e).
      pose proof (expr_result_shift0_lvars_subset 0
        (dom (relevant_env Σ (CTUnder b topq) e)) e).
      rewrite ?lvars_fv_union, ?lvars_fv_empty,
        ?lvars_fv_lvars_at_depth.
      rewrite ?tm_lvars_at_fv.
      unfold topq, qual_top.
      cbn [qual_vars qual_lvars].
      rewrite ?lvars_fv_empty.
      intros a Ha.
      set_unfold in Ha.
      set_unfold in HΣscope.
      set_unfold in Hefv.
      repeat match goal with
      | H : _ \/ _ |- _ => destruct H as [H|H]
      | H : False |- _ => contradiction
      end;
        try solve [apply HΣscope; assumption
          | apply HΣscope; apply Hefv; assumption
          | contradiction].
      match goal with
      | H : a ∈ lvars_fv ((∅ : lvset) ∖ {[LVBound 0]}) |- _ =>
          exfalso;
          assert (((∅ : lvset) ∖ {[LVBound 0]}) = ∅) as Hempty by set_solver;
          rewrite Hempty, lvars_fv_empty in H;
          rewrite elem_of_empty in H; exact H
      end.
    + exists (world_dom (m : WorldT) ∪ formula_fv
        (expr_result_formula_at
          (lvars_shift_from 0 (dom (relevant_env Σ (CTUnder b topq) e)))
          (tm_shift 0 e) (LVBound 0))).
      intros y Hy my Hdom Hrestrict.
      cbn [formula_open].
      eapply res_models_impl_intro.
      * unfold formula_scoped_in_world.
        assert (HΣscope :
          lvars_fv (dom (relevant_env Σ (CTUnder b topq) e)) ⊆
            world_dom (m : WorldT)).
        {
          unfold ty_guard_formula in Hguard.
          repeat rewrite res_models_and_iff in Hguard.
          destruct Hguard as [_ [Hworld _]].
          apply basic_world_formula_models_iff in Hworld as [_ [Hscope _]].
          exact Hscope.
        }
        assert (HΣlc : lc_lvars (dom (relevant_env Σ (CTUnder b topq) e))).
        {
          unfold ty_guard_formula in Hguard.
          repeat rewrite res_models_and_iff in Hguard.
          destruct Hguard as [_ [Hworld _]].
          apply basic_world_formula_models_iff in Hworld as [Hlc _].
          exact Hlc.
        }
        assert (Hlc_tm : lc_tm e).
        {
          unfold ty_guard_formula in Hguard.
          repeat rewrite res_models_and_iff in Hguard.
          destruct Hguard as [_ [_ [Hbasic _]]].
          apply expr_basic_typing_formula_models_iff in Hbasic as [_ [_ Hty]].
          eapply basic_tm_has_ltype_lc; [exact HΣlc|exact Hty].
        }
        assert (Hzero : m ⊨ ty_denote_gas 0 Σ (CTUnder b topq) e).
        {
          cbn [ty_denote_gas]. rewrite res_models_and_iff.
          split; [exact Hguard|apply res_models_true].
        }
        pose proof (ty_denote_gas_zero_tm_lvars_dom
          Σ (CTUnder b topq) e m Hzero) as Htmrel.
        assert (Hefv :
          fv_tm e ⊆ lvars_fv (dom (relevant_env Σ (CTUnder b topq) e))).
        {
          intros a Ha.
          rewrite <- tm_lvars_fv in Ha.
          apply lvars_fv_elem.
          apply Htmrel.
          apply lvars_fv_elem in Ha. exact Ha.
        }
        rewrite formula_open_expr_result_formula_at_shift0.
        formula_fv_syntax_norm.
        cbn [formula_lvars formula_lvars_at].
        primop_normalize_denot_formula_lvars.
        rewrite ?lvars_fv_union, ?lvars_fv_empty,
          ?lvars_fv_lvars_at_depth, ?tm_lvars_at_fv,
          ?lvars_fv_singleton_free, ?lvars_shift_from_fv.
        unfold topq, qual_top.
        cbn [qual_vars qual_lvars].
        rewrite ?lvars_fv_empty.
        rewrite Hdom.
        intros a Ha.
        set_unfold in Ha.
        repeat match goal with
        | H : _ \/ _ |- _ => destruct H as [H|H]
        | H : False |- _ => contradiction
        | H : _ = _ |- _ => subst
        end;
          try solve [apply elem_of_union_l; apply HΣscope; assumption
            | apply elem_of_union_l; apply HΣscope; apply Hefv; assumption
            | apply elem_of_union_r; apply elem_of_singleton_2; reflexivity
            | apply lvars_shift_from_lc; exact HΣlc
            | match goal with
              | H : a ∈ lvars_fv (dom ?R) |- _ =>
                  apply elem_of_union_l; apply HΣscope; exact H
              end
            | match goal with
              | H : a ∈ lvars_fv ?D |- _ =>
                  exfalso;
                  assert (D = ∅) as Hempty
                    by (rewrite ?set_swap_empty; set_solver);
                  rewrite Hempty, lvars_fv_empty in H;
                  rewrite elem_of_empty in H; exact H
              end].
        try (apply lvars_shift_from_lc; exact HΣlc).
        try (rewrite lvars_shift_from_fv;
          intros HyD; apply Hy; apply elem_of_union_l; apply HΣscope; exact HyD).
        try (intros Hye; apply Hy; apply elem_of_union_l;
          apply HΣscope; apply Hefv; exact Hye).
        try exact Hlc_tm.
        try (let Hbad := fresh "Hbad" in
          intro Hbad; apply Hy; apply elem_of_union_l;
          apply HΣscope; apply Hefv; exact Hbad).
      * intros _.
        destruct (top_result_body my) as [_ Hunder].
        replace (set_swap (LVBound 0) (LVFree y) ((∅ : lvset) ∖ {[LVBound 0]})) with (∅ : lvset)
          by set_solver.
        replace (qual_open_atom 0 y topq) with topq by reflexivity.
        replace (set_swap (LVBound 0) (LVFree y) (qual_vars topq ∖ {[LVBound 0]})) with (∅ : lvset)
          by (unfold topq, qual_top; cbn [qual_vars qual_lvars]; set_solver).
        exact Hunder.
Qed.

Lemma relevant_env_precise_top_over b Σ e :
  relevant_env Σ (CTOver b topq) e =
  relevant_env Σ (precise_ty b topq) e.
Proof.
  unfold relevant_env, lty_env_restrict_lvars, relevant_lvars,
    precise_ty, over_ty, under_ty, topq, qual_top.
  cbn [context_ty_lvars context_ty_lvars_at qual_vars qual_lvars].
  f_equal; try set_solver.
Qed.

Lemma relevant_env_precise_top_under b Σ e :
  relevant_env Σ (CTUnder b topq) e =
  relevant_env Σ (precise_ty b topq) e.
Proof.
  unfold relevant_env, lty_env_restrict_lvars, relevant_lvars,
    precise_ty, over_ty, under_ty, topq, qual_top.
  cbn [context_ty_lvars context_ty_lvars_at qual_vars qual_lvars].
  f_equal; try set_solver.
Qed.

Lemma precise_top_guard_over b Σ e (m : WfWorldT) :
  m ⊨ ty_guard_formula (relevant_env Σ (precise_ty b topq) e)
      (precise_ty b topq) e ->
  m ⊨ ty_guard_formula (relevant_env Σ (CTOver b topq) e)
      (CTOver b topq) e.
Proof.
  rewrite relevant_env_precise_top_over.
  unfold ty_guard_formula.
  repeat rewrite res_models_and_iff.
  intros [Hwf [Hworld [Hbasic Htotal]]].
  split.
  - apply context_ty_wf_formula_models_iff.
    apply basic_world_formula_models_iff in Hworld as [Hlc [Hscope _]].
    split; [exact Hlc|]. split; [exact Hscope|].
    cbn [basic_context_ty_lvars context_ty_lvars context_ty_lvars_at
      context_ty_shape_ok qual_vars qual_lvars topq qual_top].
    split.
    + intros v Hv.
      exfalso.
      clear -Hv.
      unfold topq, qual_top in Hv.
      cbn [qual_vars qual_lvars] in Hv.
      change (v ∈ (∅ : lvset)) in Hv.
      rewrite elem_of_empty in Hv. exact Hv.
    + exact I.
  - split; [exact Hworld|]. split; [exact Hbasic|exact Htotal].
Qed.

Lemma precise_top_guard_under b Σ e (m : WfWorldT) :
  m ⊨ ty_guard_formula (relevant_env Σ (precise_ty b topq) e)
      (precise_ty b topq) e ->
  m ⊨ ty_guard_formula (relevant_env Σ (CTUnder b topq) e)
      (CTUnder b topq) e.
Proof.
  rewrite relevant_env_precise_top_under.
  unfold ty_guard_formula.
  repeat rewrite res_models_and_iff.
  intros [Hwf [Hworld [Hbasic Htotal]]].
  split.
  - apply context_ty_wf_formula_models_iff.
    apply basic_world_formula_models_iff in Hworld as [Hlc [Hscope _]].
    split; [exact Hlc|]. split; [exact Hscope|].
    cbn [basic_context_ty_lvars context_ty_lvars context_ty_lvars_at
      context_ty_shape_ok qual_vars qual_lvars topq qual_top].
    split.
    + intros v Hv.
      exfalso.
      clear -Hv.
      unfold topq, qual_top in Hv.
      cbn [qual_vars qual_lvars] in Hv.
      change (v ∈ (∅ : lvset)) in Hv.
      rewrite elem_of_empty in Hv. exact Hv.
    + exact I.
  - split; [exact Hworld|]. split; [exact Hbasic|exact Htotal].
Qed.

Lemma precise_top_denotation_gas
    gas b Σ e (m : WfWorldT) :
  m ⊨ ty_guard_formula (relevant_env Σ (precise_ty b topq) e)
      (precise_ty b topq) e ->
  m ⊨ ty_denote_gas gas Σ (precise_ty b topq) e.
Proof.
  destruct gas as [|gas']; intros Hguard.
  - cbn [ty_denote_gas]. rewrite res_models_and_iff. split; [exact Hguard|apply res_models_true].
  - unfold precise_ty, over_ty, under_ty in *.
    cbn [ty_denote_gas].
    rewrite res_models_and_iff. split; [exact Hguard|].
    rewrite res_models_and_iff.
    split.
    + apply over_top_denotation_gas.
      apply precise_top_guard_over. exact Hguard.
    + apply under_top_denotation_gas.
      apply precise_top_guard_under. exact Hguard.
Qed.

Lemma primop_arg_env_lookup op x :
  atom_env_to_lty_env
    (ctx_erasure_under ∅ (CtxBind x (primop_arg_ty (concrete_Φ op))))
    !! LVFree x =
  Some (TBase (prim_arg_base (concrete_Φ op))).
Proof.
  rewrite ctx_erasure_under_bind.
  rewrite atom_store_to_lvar_store_lookup_free.
  rewrite primop_arg_ty_eq.
  cbn [erase_ty].
  apply map_lookup_union_Some_raw.
  right. split.
  - apply storeA_restrict_lookup_none_l. apply lookup_empty.
  - change ((<[x := TBase (prim_arg_base (concrete_Φ op))]>
        (∅ : gmap atom ty)) !! x =
      Some (TBase (prim_arg_base (concrete_Φ op)))).
    apply map_lookup_insert.
Qed.

Lemma primop_arg_erase_env_lookup op x :
  atom_env_to_lty_env (erase_ctx (CtxBind x (primop_arg_ty (concrete_Φ op))))
    !! LVFree x =
  Some (TBase (prim_arg_base (concrete_Φ op))).
Proof.
  cbn [erase_ctx].
  rewrite atom_store_to_lvar_store_lookup_free.
  rewrite primop_arg_ty_eq.
  cbn [erase_ty].
  change ((<[x := TBase (prim_arg_base (concrete_Φ op))]>
        (∅ : gmap atom ty)) !! x =
      Some (TBase (prim_arg_base (concrete_Φ op)))).
  apply map_lookup_insert.
Qed.

Lemma primop_result_ty_open_eq op x :
  {0 ~> x} (primop_result_ty (concrete_Φ op)) =
  precise_ty (prim_ret_base (concrete_Φ op)) topq.
Proof.
  rewrite primop_result_ty_eq.
  unfold precise_ty, over_ty, under_ty, topq, qual_top.
  cbn [cty_open qual_open_atom].
  reflexivity.
Qed.

Lemma primop_arg_guard_formula
    op x (m : WfWorldT) :
  m ⊨ basic_world_formula
    (<[LVFree x := TBase (prim_arg_base (concrete_Φ op))]> ∅) ->
  m ⊨ ty_guard_formula
    (relevant_env
      (atom_env_to_lty_env
        (<[x := erase_ty (primop_arg_ty (concrete_Φ op))]>
          (∅ : gmap atom ty)))
      (primop_arg_ty (concrete_Φ op)) (tret (vfvar x)))
    (primop_arg_ty (concrete_Φ op)) (tret (vfvar x)).
Proof.
  intros Hworld_single.
  rewrite primop_arg_ty_eq.
  assert (Hworld :
    m ⊨ basic_world_formula
      (relevant_env
        (atom_env_to_lty_env
          (<[x := TBase (prim_arg_base (concrete_Φ op))]>
            (∅ : gmap atom ty)))
        (CTOver (prim_arg_base (concrete_Φ op)) topq)
        (tret (vfvar x)))).
  {
    eapply basic_world_formula_subenv; [|exact Hworld_single].
    intros v T Hlook.
    destruct v as [k|a].
    - unfold relevant_env, lty_env_restrict_lvars in Hlook.
      apply storeA_restrict_lookup_some in Hlook as [_ Hlook].
      rewrite atom_store_to_lvar_store_lookup_bound_none in Hlook.
      discriminate.
    - destruct (decide (a = x)) as [->|Hax].
      + unfold relevant_env, lty_env_restrict_lvars in Hlook.
        apply storeA_restrict_lookup_some in Hlook as [_ Hlook].
        rewrite atom_store_to_lvar_store_lookup_free in Hlook.
        unfold store_insert, store_empty in Hlook.
        rewrite lookup_insert in Hlook.
        rewrite decide_True in Hlook by reflexivity.
        transitivity (Some (TBase (prim_arg_base (concrete_Φ op)))).
        * apply map_lookup_insert.
        * exact Hlook.
      + unfold relevant_env, lty_env_restrict_lvars in Hlook.
        apply storeA_restrict_lookup_some in Hlook as [_ Hlook].
        rewrite atom_store_to_lvar_store_lookup_free in Hlook.
        unfold store_insert, store_empty in Hlook.
        rewrite lookup_insert_ne in Hlook by congruence.
        rewrite lookup_empty in Hlook. discriminate.
  }
  assert (Hbasic :
    m ⊨ expr_basic_typing_formula
      (relevant_env
        (atom_env_to_lty_env
          (<[x := TBase (prim_arg_base (concrete_Φ op))]>
            (∅ : gmap atom ty)))
        (CTOver (prim_arg_base (concrete_Φ op)) topq)
        (tret (vfvar x)))
      (tret (vfvar x)) (TBase (prim_arg_base (concrete_Φ op)))).
  {
    apply expr_basic_typing_formula_models_iff.
    apply basic_world_formula_models_iff in Hworld as [Hlc [Hscope _]].
    split; [exact Hlc|]. split; [exact Hscope|].
    constructor. constructor.
    unfold relevant_env, lty_env_restrict_lvars.
    apply storeA_restrict_lookup_some_2.
    - rewrite atom_store_to_lvar_store_lookup_free.
      unfold store_insert, store_empty.
      apply map_lookup_insert.
    - unfold relevant_lvars.
      cbn [tm_lvars tm_lvars_at value_lvars_at].
      unfold over_ty, topq, qual_top.
      cbn [context_ty_lvars context_ty_lvars_at qual_vars qual_lvars].
      apply elem_of_union_r.
      apply elem_of_singleton. reflexivity.
  }
  unfold ty_guard_formula.
  repeat rewrite res_models_and_iff.
  split.
  - apply context_ty_wf_formula_models_iff.
    apply basic_world_formula_models_iff in Hworld as [Hlc [Hscope _]].
    split; [exact Hlc|]. split; [exact Hscope|].
    eapply (basic_context_ty_lvars_mono (lvars_of_atoms ∅)).
    + intros v Hv.
      unfold lvars_of_atoms in Hv.
      apply elem_of_map in Hv as [a [-> Ha]].
      rewrite elem_of_empty in Ha. contradiction.
    + apply basic_context_ty_to_lvars.
      rewrite <- primop_arg_ty_eq.
      apply primop_arg_basic.
  - split; [exact Hworld|]. split; [exact Hbasic|].
    eapply expr_total_formula_tret_of_basic; eauto.
Qed.

Lemma primop_arg_const_from_ctx
    op x (m : WfWorldT) σ :
  m ⊨ ctx_denote (CtxBind x (primop_arg_ty (concrete_Φ op))) ->
  (m : WorldT) σ ->
  exists c,
    σ !! x = Some (vconst c) /\
    base_ty_of_const c = prim_arg_base (concrete_Φ op).
Proof.
  intros Hctx Hσ.
  pose proof (ctx_denote_under_basic_world
    ∅ (CtxBind x (primop_arg_ty (concrete_Φ op))) m Hctx) as Hworld.
  apply basic_world_formula_models_iff in Hworld as [_ [Hscope Htyped]].
  assert (Hxworld : x ∈ world_dom (m : WorldT)).
  {
    apply Hscope. apply lvars_fv_elem.
    apply elem_of_dom. exists (TBase (prim_arg_base (concrete_Φ op))).
    apply primop_arg_env_lookup.
  }
  assert (Hxdom : x ∈ dom (σ : StoreT)).
  {
    change (x ∈ dom (σ : gmap atom value)).
    rewrite (wfworld_store_dom m σ Hσ). exact Hxworld.
  }
  change (x ∈ dom (σ : gmap atom value)) in Hxdom.
  apply elem_of_dom in Hxdom as [vx Hxσ].
  unfold lworld_has_type, worldA_has_type in Htyped.
  destruct Htyped as [_ Hstores].
  assert (Hlift : (res_lift_free m : LWorld) (lstore_lift_free σ)).
  { exists σ. split; [exact Hσ|reflexivity]. }
  specialize (Hstores (lstore_lift_free σ) Hlift).
  pose proof (Hstores (LVFree x)
    (TBase (prim_arg_base (concrete_Φ op))) vx
    (primop_arg_env_lookup op x)) as Hval.
  rewrite lstore_lift_free_lookup_free in Hval.
  specialize (Hval Hxσ).
  apply basic_typing_base_canonical_form in Hval as [c [-> Hbase]].
  exists c. split; [exact Hxσ|exact Hbase].
Qed.

Lemma expr_total_formula_tprim_from_primop_arg
    op x (m : WfWorldT) :
  m ⊨ ctx_denote (CtxBind x (primop_arg_ty (concrete_Φ op))) ->
  m ⊨ expr_total_formula (tprim op (vfvar x)).
Proof.
  intros Hctx.
  apply expr_total_atom_world_to_formula.
  split.
  - rewrite res_lift_free_dom.
    intros v Hv.
    cbn [tm_lvars tm_lvars_at value_lvars_at] in Hv.
    destruct v as [k|a].
    + apply elem_of_singleton in Hv. discriminate.
    + apply elem_of_singleton in Hv. inversion Hv. subst a.
      unfold lvars_of_atoms. apply elem_of_map.
      exists x. split; [reflexivity|].
      pose proof (ctx_denote_under_basic_world
        ∅ (CtxBind x (primop_arg_ty (concrete_Φ op))) m Hctx) as Hworld.
      apply basic_world_formula_models_iff in Hworld as [_ [Hscope _]].
      apply Hscope. apply lvars_fv_elem.
      apply elem_of_dom. exists (TBase (prim_arg_base (concrete_Φ op))).
      apply primop_arg_env_lookup.
  - intros τ Hτ.
    destruct Hτ as [σ [Hσ ->]].
    destruct (primop_arg_const_from_ctx op x m σ Hctx Hσ)
      as [c [Hxσ Hbase]].
    unfold lstore_instantiate_tm, lstore_instantiate_tm_at.
    cbn [lstore_instantiate_tm_at lstore_instantiate_value_at].
    rewrite lstore_free_part_lift_free.
    cbn [lstore_instantiate_tm_split_at lstore_instantiate_value_split_at].
    change ((σ : gmap atom value) !! x = Some (vconst c)) in Hxσ.
    change (must_terminating
      (tprim op
        (match ((σ : gmap atom value) !! x) with
         | Some u => u
         | None => vfvar x
         end))).
    destruct ((σ : gmap atom value) !! x) as [vx|] eqn:Hlook.
    2:{ congruence. }
    assert (vx = vconst c) as -> by congruence.
    apply must_terminating_tprim_const.
    + constructor. constructor.
    + eapply prim_step_total_for_base.
      * apply primop_erasure.
      * exact Hbase.
Qed.

Lemma primop_opened_result_guard_formula
    op x (m : WfWorldT) :
  m ⊨ ctx_denote (CtxBind x (primop_arg_ty (concrete_Φ op))) ->
  m ⊨ ty_guard_formula
    (relevant_env
      (atom_env_to_lty_env (erase_ctx (CtxBind x (primop_arg_ty (concrete_Φ op)))))
      ({0 ~> x} (primop_result_ty (concrete_Φ op)))
      (tprim op (vfvar x)))
    ({0 ~> x} (primop_result_ty (concrete_Φ op)))
    (tprim op (vfvar x)).
Proof.
  intros Hctx.
  rewrite primop_result_ty_open_eq.
  set (Σres := relevant_env
    (atom_env_to_lty_env (erase_ctx (CtxBind x (primop_arg_ty (concrete_Φ op)))))
    (precise_ty (prim_ret_base (concrete_Φ op)) topq)
    (tprim op (vfvar x))).
  assert (Hworld_ctx :
    m ⊨ basic_world_formula
      (atom_env_to_lty_env
        (ctx_erasure_under ∅ (CtxBind x (primop_arg_ty (concrete_Φ op)))))).
  {
    eapply ctx_denote_under_basic_world. exact Hctx.
  }
  assert (Hworld : m ⊨ basic_world_formula Σres).
  {
    subst Σres.
    eapply basic_world_formula_subenv; [|exact Hworld_ctx].
    intros v T Hlook.
    unfold relevant_env, lty_env_restrict_lvars in Hlook.
    apply storeA_restrict_lookup_some in Hlook as [_ Hlook].
    destruct v as [k|a].
    - rewrite atom_store_to_lvar_store_lookup_bound_none in Hlook.
      discriminate.
    - rewrite ctx_erasure_under_bind.
      rewrite !atom_store_to_lvar_store_lookup_free in Hlook |- *.
      cbn [erase_ctx] in Hlook.
      apply map_lookup_union_Some_raw.
      right. split.
      * apply storeA_restrict_lookup_none_l. apply lookup_empty.
      * exact Hlook.
  }
  unfold ty_guard_formula.
  repeat rewrite res_models_and_iff.
  split.
  - apply context_ty_wf_formula_models_iff.
    apply basic_world_formula_models_iff in Hworld as [Hlc [Hscope _]].
    split; [exact Hlc|]. split; [exact Hscope|].
    unfold precise_ty, over_ty, under_ty, topq, qual_top.
    cbn [basic_context_ty_lvars context_ty_lvars context_ty_lvars_at
      context_ty_shape_ok qual_vars qual_lvars erase_ty].
    repeat split; try reflexivity; intros v Hv;
      change (v ∈ (∅ : lvset)) in Hv;
      rewrite elem_of_empty in Hv; exfalso; exact Hv.
  - split; [exact Hworld|]. split.
    + apply expr_basic_typing_formula_models_iff.
      apply basic_world_formula_models_iff in Hworld as [Hlc [Hscope _]].
      split; [exact Hlc|]. split; [exact Hscope|].
      replace (erase_ty (precise_ty (prim_ret_base (concrete_Φ op)) topq))
        with (TBase (prim_ret_base (concrete_Φ op))) by reflexivity.
      econstructor.
      * apply primop_erasure.
      * constructor.
        subst Σres.
        unfold relevant_env, lty_env_restrict_lvars.
        apply storeA_restrict_lookup_some_2.
        -- apply primop_arg_erase_env_lookup.
        -- unfold relevant_lvars.
           cbn [tm_lvars tm_lvars_at value_lvars_at].
           unfold precise_ty, over_ty, under_ty, topq, qual_top.
           cbn [context_ty_lvars context_ty_lvars_at qual_vars qual_lvars].
           apply elem_of_union_r.
           apply elem_of_singleton. reflexivity.
    + apply expr_total_formula_tprim_from_primop_arg. exact Hctx.
Qed.

Lemma primop_graph_result_denotation
    op x :
  ctx_denote (CtxBind x (primop_arg_ty (concrete_Φ op))) ⊫
    ty_denote (erase_ctx (CtxBind x (primop_arg_ty (concrete_Φ op))))
      ({0 ~> x} (primop_result_ty (concrete_Φ op)))
      (tprim op (vfvar x)).
Proof.
  intros m Hctx.
  unfold ty_denote.
  rewrite primop_result_ty_open_eq.
  eapply (precise_top_denotation_gas
    (cty_depth (precise_ty (prim_ret_base (concrete_Φ op)) topq))
    (prim_ret_base (concrete_Φ op))
    (atom_env_to_lty_env (erase_ctx (CtxBind x (primop_arg_ty (concrete_Φ op)))))
    (tprim op (vfvar x))).
  pose proof (primop_opened_result_guard_formula op x m Hctx) as Hguard.
  rewrite primop_result_ty_open_eq in Hguard.
  exact Hguard.
Qed.

Lemma primop_result_denotation_arg_world
    op x (m : WfWorldT) :
  m ⊨ ty_denote (erase_ctx (CtxBind x (primop_arg_ty (concrete_Φ op))))
    ({0 ~> x} (primop_result_ty (concrete_Φ op)))
    (tprim op (vfvar x)) ->
  m ⊨ basic_world_formula (<[LVFree x := TBase (prim_arg_base (concrete_Φ op))]> ∅).
Proof.
  intros Hden.
  unfold ty_denote in Hden.
  rewrite primop_result_ty_open_eq in Hden.
  pose proof (ty_denote_gas_guard_formula _ _ _ _ _ Hden) as Hguard.
  unfold ty_guard_formula in Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [_ [Hworld _]].
  eapply basic_world_formula_subenv; [|exact Hworld].
  intros v T Hlook.
  destruct v as [k|a].
  - rewrite lookup_insert_ne in Hlook by discriminate.
    rewrite lookup_empty in Hlook. discriminate.
  - destruct (decide (a = x)) as [->|Hax].
    + rewrite lookup_insert_eq in Hlook. inversion Hlook. subst T.
      unfold relevant_env, lty_env_restrict_lvars.
      apply storeA_restrict_lookup_some_2.
      * apply primop_arg_erase_env_lookup.
      * unfold relevant_lvars.
        cbn [tm_lvars tm_lvars_at value_lvars_at].
        unfold precise_ty, over_ty, under_ty, topq, qual_top.
        cbn [context_ty_lvars context_ty_lvars_at qual_vars qual_lvars].
        apply elem_of_union_r.
        apply elem_of_singleton. reflexivity.
    + rewrite lookup_insert_ne in Hlook by congruence.
      rewrite lookup_empty in Hlook. discriminate.
Qed.

Lemma primop_graph_result_to_arg_ctx
    op x :
  ty_denote (erase_ctx (CtxBind x (primop_arg_ty (concrete_Φ op))))
    ({0 ~> x} (primop_result_ty (concrete_Φ op)))
    (tprim op (vfvar x)) ⊫
  ctx_denote (CtxBind x (primop_arg_ty (concrete_Φ op))).
Proof.
  intros m Hden.
  pose proof (primop_result_denotation_arg_world op x m Hden) as Hworld_arg.
  eapply ctx_denote_bind_from_arg_denotation.
  - apply primop_arg_basic.
  - rewrite primop_arg_ty_eq. cbn [erase_ty].
    apply map_lookup_insert.
  - rewrite primop_arg_ty_eq.
    pose proof (primop_arg_guard_formula op x m Hworld_arg) as Hguard_arg.
    rewrite primop_arg_ty_eq in Hguard_arg.
    exact (over_top_denotation_gas
      (cty_depth (CTOver (prim_arg_base (concrete_Φ op)) topq))
      (prim_arg_base (concrete_Φ op))
      (atom_env_to_lty_env
        (<[x := erase_ty (primop_arg_ty (concrete_Φ op))]>
          (∅ : gmap atom ty)))
      (tret (vfvar x)) m Hguard_arg).
Qed.

Theorem concrete_Φ_wf : wf_primop_ctx concrete_Φ.
Proof.
  intros op.
  refine {| wf_primop_erasure := primop_erasure op;
            wf_primop_arg_basic := primop_arg_basic op;
            wf_primop_result_basic := primop_result_wf op;
            wf_primop_semantic := _ |}.
  unfold primop_semantic_ok.
  intros x. split.
  - apply primop_graph_result_denotation.
  - apply primop_graph_result_to_arg_ctx.
Qed.
