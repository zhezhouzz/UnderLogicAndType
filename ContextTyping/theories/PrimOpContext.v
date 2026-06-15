(** * ContextTyping.PrimOpContext

    Concrete primitive-operation signatures for the context typing rules. *)

From CoreLang Require Import BasicTyping SmallStep.
From ContextLogic Require Import FormulaSemantics.
From ContextTypeLanguage Require Import WF.
From Denotation Require Import Context ConstDenote TypeEquivCore TypeEquiv.

(** Paper-level primitive-operation signatures.  CoreLang keeps the erased
    unary type [prim_op_type]; this layer refines it with an over-approximate
    argument qualifier and a precise graph result qualifier. *)

Record primop_sig := mk_primop_sig {
  prim_arg_base : base_ty;
  prim_arg_qual : type_qualifier;
  prim_ret_base : base_ty;
  prim_ret_qual : type_qualifier;
}.

Definition primop_result_ty (sig : primop_sig) : context_ty :=
  precise_ty sig.(prim_ret_base) sig.(prim_ret_qual).

Definition primop_arg_ty (sig : primop_sig) : context_ty :=
  over_ty sig.(prim_arg_base) sig.(prim_arg_qual).

Definition primop_ctx : Type := prim_op -> primop_sig.

Definition primop_erasure_ok (op : prim_op) (sig : primop_sig) : Prop :=
  prim_op_type op = (sig.(prim_arg_base), sig.(prim_ret_base)).

(** Paper-level semantic well-formedness for primitive operators.

    In the paper this is written as

      [Phi(op) = x : {b_x | phi_x} -> precise(b, phi)]
      and [models [[x : {b_x | phi_x}]] iff [[precise(b, phi)]] (op x)].

    The result type is scoped as an arrow body, so its qualifier may mention the
    outer argument binder. *)
Definition primop_semantic_ok (op : prim_op) (sig : primop_sig) : Prop :=
  forall x : atom,
    let Γx := CtxBind x (primop_arg_ty sig) in
    (ctx_denote Γx ⊫
      ty_denote (erase_ctx Γx) ({0 ~> x} (primop_result_ty sig))
        (tprim op (vfvar x))) /\
    (ty_denote (erase_ctx Γx) ({0 ~> x} (primop_result_ty sig))
        (tprim op (vfvar x)) ⊫
      ctx_denote Γx).

Record wf_primop_sig (op : prim_op) (sig : primop_sig) : Prop := {
  wf_primop_erasure : primop_erasure_ok op sig;
  wf_primop_arg_basic : basic_context_ty ∅ (primop_arg_ty sig);
  wf_primop_result_basic : wf_context_ty_at 1 ∅ (primop_result_ty sig);
  wf_primop_semantic : primop_semantic_ok op sig;
}.

Definition wf_primop_ctx (Φ : primop_ctx) : Prop :=
  forall op, wf_primop_sig op (Φ op).

(** The graph qualifier is written at the result-type binder depth: [#0] is
    the result value and [#1] is the surrounding primitive argument. *)
Definition primop_graph_qual (op : prim_op) : type_qualifier :=
  tqual ({[LVBound 0; LVBound 1]})
    (fun σ =>
       exists carg cret,
         denote_lvar_value (lso_store σ) (vbvar 1) = Some (vconst carg) /\
         denote_lvar_value (lso_store σ) (vbvar 0) = Some (vconst cret) /\
         prim_step op carg cret).

Definition concrete_primop_sig (op : prim_op) : primop_sig :=
  match prim_op_type op with
  | (arg_b, ret_b) =>
      mk_primop_sig arg_b qual_top ret_b (primop_graph_qual op)
  end.

Definition Φ : primop_ctx := concrete_primop_sig.

Lemma primop_result_ty_eq op :
  primop_result_ty (Φ op) =
  precise_ty (prim_ret_base (Φ op)) (primop_graph_qual op).
Proof.
  unfold primop_result_ty, Φ, concrete_primop_sig.
  destruct (prim_op_type op); reflexivity.
Qed.

Lemma primop_arg_ty_eq op :
  primop_arg_ty (Φ op) =
  over_ty (prim_arg_base (Φ op)) qual_top.
Proof.
  unfold primop_arg_ty, Φ, concrete_primop_sig.
  destruct (prim_op_type op); reflexivity.
Qed.

Lemma primop_graph_qual_lc op :
  lvars_wf_at 2 ∅ (qual_vars (primop_graph_qual op)).
Proof.
  unfold primop_graph_qual, qual_vars.
  cbn [qual_lvars].
  unfold lvars_wf_at. set_solver.
Qed.

Lemma primop_graph_qual_open_vars op x y :
  x <> y ->
  qual_vars
    (qual_open_atom 0 y (qual_open_atom 1 x (primop_graph_qual op))) =
  ({[LVFree x; LVFree y]} : lvset).
Proof.
  intros Hxy.
  rewrite !qual_open_atom_vars.
  unfold primop_graph_qual, qual_vars.
  cbn [qual_lvars].
  rewrite set_swap_union, !set_swap_singleton.
  base_swap_normalize.
    better_set_solver.
Qed.

Lemma primop_graph_qual_arg_open_vars op x :
  qual_vars (qual_open_atom 1 x (primop_graph_qual op)) =
  ({[LVBound 0; LVFree x]} : lvset).
Proof.
  rewrite qual_open_atom_vars.
  unfold primop_graph_qual, qual_vars.
  cbn [qual_lvars].
  rewrite set_swap_union, !set_swap_singleton.
  base_swap_normalize.
  better_set_solver.
Qed.

Lemma primop_graph_qual_fibvars_set op x y :
  x <> y ->
  set_swap (LVBound 0) (LVFree y)
    (qual_vars (qual_open_atom 1 x (primop_graph_qual op)) ∖
      {[LVBound 0]}) =
  qual_vars
    (qual_open_atom 0 y (qual_open_atom 1 x (primop_graph_qual op))) ∖
    {[LVFree y]}.
Proof.
  intros Hxy.
  transitivity ({[LVFree x]} : lvset).
  - rewrite qual_open_atom_vars.
    unfold primop_graph_qual, qual_vars.
    cbn [qual_lvars].
    replace (set_swap (LVBound 1) (LVFree x)
        ({[LVBound 0; LVBound 1]} : lvset))
      with ({[LVBound 0; LVFree x]} : lvset).
    2:{ rewrite set_swap_union, !set_swap_singleton.
        base_swap_normalize. better_set_solver. }
    replace (({[LVBound 0; LVFree x]} : lvset) ∖ {[LVBound 0]})
      with ({[LVFree x]} : lvset) by set_solver.
    rewrite set_swap_singleton.
    unfold swap.
    destruct (decide (LVFree x = LVBound 0)) as [Hbad|_];
      [discriminate|].
    destruct (decide (LVFree x = LVFree y)) as [Hbad|_].
    + inversion Hbad. congruence.
    + reflexivity.
  - rewrite primop_graph_qual_open_vars by exact Hxy.
    better_set_solver.
Qed.

Lemma primop_graph_qual_open_prop_iff op x y
    (Hxy : x <> y)
    (s : LStoreOn (V := value)
      (qual_vars
        (qual_open_atom 0 y (qual_open_atom 1 x (primop_graph_qual op))))) :
  qual_prop
    (qual_open_atom 0 y (qual_open_atom 1 x (primop_graph_qual op))) s <->
  exists carg cret,
    (lso_store s : LStore (V := value)) !! LVFree x = Some (vconst carg) /\
    (lso_store s : LStore (V := value)) !! LVFree y = Some (vconst cret) /\
    prim_step op carg cret.
Proof.
  unfold qual_open_atom, primop_graph_qual.
  cbn [qual_prop qual_lvars denote_lvar_value
    lstore_on_open_back lso_store].
  unfold lstore_on_open_back.
  cbn [lso_store storeAO_store].
  rewrite !lstore_swap_lookup_inv_value.
  base_swap_normalize.
  tauto.
Qed.

Lemma prim_step_total_for_base op c arg_b ret_b :
  prim_op_type op = (arg_b, ret_b) ->
  base_ty_of_const c = arg_b ->
  exists c', prim_step op c c'.
Proof.
  destruct op, c; cbn; intros Hop Hbase; inversion Hop; subst;
    try discriminate; eauto using prim_step.
Qed.

Lemma expr_eval_prim_fvar_const_intro σ op x carg cret :
  (σ : LStore (V := value)) !! LVFree x = Some (vconst carg) ->
  prim_step op carg cret ->
  expr_eval_in_store σ (tprim op (vfvar x)) (vconst cret).
Proof.
  intros Hx Hstep.
  unfold expr_eval_in_store, lstore_instantiate_tm.
  cbn [lstore_instantiate_tm_at lstore_instantiate_value_at
    lstore_instantiate_tm_split_at lstore_instantiate_value_split_at].
  change (lstore_free_part σ !! x)
    with ((lstore_to_store σ : gmap atom value) !! x).
  rewrite (@lstore_to_store_lookup value σ x).
  replace ((σ : LStore (V := value)) !! LVFree x)
    with (Some (vconst carg)) by (symmetry; exact Hx).
  apply reduction_prim_intro. exact Hstep.
Qed.

Lemma expr_eval_prim_fvar_const_elim σ op x carg cret :
  (σ : LStore (V := value)) !! LVFree x = Some (vconst carg) ->
  expr_eval_in_store σ (tprim op (vfvar x)) (vconst cret) ->
  prim_step op carg cret.
Proof.
  intros Hx Heval.
  unfold expr_eval_in_store, lstore_instantiate_tm in Heval.
  cbn [lstore_instantiate_tm_at lstore_instantiate_value_at
    lstore_instantiate_tm_split_at lstore_instantiate_value_split_at] in Heval.
  change (lstore_free_part σ !! x)
    with ((lstore_to_store σ : gmap atom value) !! x) in Heval.
  rewrite (@lstore_to_store_lookup value σ x) in Heval.
  replace ((σ : LStore (V := value)) !! LVFree x)
    with (Some (vconst carg)) in Heval by (symmetry; exact Hx).
  apply reduction_prim_const in Heval as [c' [Hstep Heq]].
  inversion Heq. subst c'. exact Hstep.
Qed.

Lemma expr_eval_prim_fvar_const_result σ op x carg v :
  (σ : LStore (V := value)) !! LVFree x = Some (vconst carg) ->
  expr_eval_in_store σ (tprim op (vfvar x)) v ->
  exists cret,
    prim_step op carg cret /\
    v = vconst cret.
Proof.
  intros Hx Heval.
  unfold expr_eval_in_store, lstore_instantiate_tm in Heval.
  cbn [lstore_instantiate_tm_at lstore_instantiate_value_at
    lstore_instantiate_tm_split_at lstore_instantiate_value_split_at] in Heval.
  change (lstore_free_part σ !! x)
    with ((lstore_to_store σ : gmap atom value) !! x) in Heval.
  rewrite (@lstore_to_store_lookup value σ x) in Heval.
  replace ((σ : LStore (V := value)) !! LVFree x)
    with (Some (vconst carg)) in Heval by (symmetry; exact Hx).
  apply reduction_prim_const in Heval as [cret [Hstep ->]].
  eauto.
Qed.

Lemma expr_result_formula_prim_fvar_lookup
    op x y (m : WfWorldT) σ carg :
  m ⊨ expr_result_formula (tprim op (vfvar x)) (LVFree y) ->
  (m : WorldT) σ ->
  σ !! x = Some (vconst carg) ->
  exists cret,
    σ !! y = Some (vconst cret) /\
    prim_step op carg cret.
Proof.
  intros Hexpr Hσ Hx.
  pose proof (expr_result_formula_to_atom_world
    (tprim op (vfvar x)) (LVFree y) m Hexpr) as Hres.
  destruct Hres as [_ [_ Hstores]].
  specialize (Hstores (lstore_lift_free σ)).
  assert (Hlift :
      (res_lift_free m : LWorldT) (lstore_lift_free σ)).
  { exists σ. split; [exact Hσ|reflexivity]. }
  specialize (Hstores Hlift).
  destruct Hstores as [_ [v [Hy Heval]]].
  rewrite lstore_lift_free_lookup_free in Hy.
  assert (Hxl :
      (lstore_lift_free σ : LStoreT) !! LVFree x =
      Some (vconst carg)).
  { rewrite lstore_lift_free_lookup_free. exact Hx. }
  pose proof (expr_eval_prim_fvar_const_result
    (lstore_lift_free σ) op x carg v Hxl Heval)
    as [cret [Hstep ->]].
  exists cret. split; [exact Hy|exact Hstep].
Qed.

Lemma primop_arg_const_from_ctx op x (m : WfWorldT) σ :
  m ⊨ ctx_denote (CtxBind x (primop_arg_ty (Φ op))) ->
  (m : WorldT) σ ->
  exists c,
    σ !! x = Some (vconst c) /\
    base_ty_of_const c = prim_arg_base (Φ op).
Proof.
  intros Hctx Hσ.
  pose proof (ctx_denote_under_bind_inv ∅ x (primop_arg_ty (Φ op)) m Hctx)
    as Harg.
  unfold ty_denote in Harg.
  eapply (ty_denote_ret_fvar_base_const
    (cty_depth (primop_arg_ty (Φ op)))
    (atom_env_to_lty_env
      (<[x := erase_ty (primop_arg_ty (Φ op))]>
        (store_restrict ∅ (ctx_fv (CtxBind x (primop_arg_ty (Φ op)))))))
    (primop_arg_ty (Φ op)) (prim_arg_base (Φ op)) x m).
  - unfold primop_arg_ty, over_ty. reflexivity.
  - exact Harg.
  - exact Hσ.
Qed.

Lemma primop_arg_in_world op x (m : WfWorldT) :
  m ⊨ ctx_denote (CtxBind x (primop_arg_ty (Φ op))) ->
  x ∈ world_dom (m : WorldT).
Proof.
  intros Hctx.
  pose proof (ctx_denote_under_basic_world
    (∅ : gmap atom ty) (CtxBind x (primop_arg_ty (Φ op))) m Hctx)
    as Hworld.
  ctx_erasure_under_norm_in Hworld.
  apply basic_world_formula_models_iff in Hworld as [_ [Hscope _]].
  apply Hscope.
  rewrite atom_store_to_lvar_store_dom.
  cbn.
  unfold lvars_of_atoms.
  apply lvars_fv_elem.
  apply elem_of_map.
  exists x. split; [reflexivity|].
  apply elem_of_dom.
  eexists. apply lookup_singleton_Some. split; reflexivity.
Qed.

Lemma res_models_atom_top (m : WfWorldT) :
	  m ⊨ FAtom qual_top.
	Proof.
	  apply res_models_atom_exact_iff.
	  unfold qualifier_exact_denote, qual_top.
	  cbn [qual_prop qual_vars qual_lvars].
  assert (Hlc : lc_lvars (∅ : lvset)) by (unfold lc_lvars; set_solver).
  assert (Hsub : lvars_fv (∅ : lvset) ⊆ world_dom (m : WorldT)).
  { rewrite lvars_fv_empty. set_solver. }
  exists Hlc, Hsub.
  intros s. split; [|intros _; exact I].
  intros _.
  unfold lstore_in_lworld_on, lworld_on_lift.
  cbn [lw lraw_world raw_worldA worldA_stores].
  destruct (world_wf m) as [[σ Hσ] _].
  exists (lstore_lift_free (store_restrict σ (∅ : aset))).
  split.
  - exists (store_restrict σ (∅ : aset)). split.
    + exists σ. split; [exact Hσ|reflexivity].
    + reflexivity.
  - apply map_eq. intros v.
    transitivity (@None value).
    + apply storeA_restrict_lookup_none_r. set_solver.
    + symmetry. apply not_elem_of_dom.
      rewrite lso_dom. set_solver.
Qed.

Lemma qual_top_open y :
  qual_open_atom 0 y (qual_top (V := value)) = qual_top.
Proof.
  apply qual_open_atom_fresh_lc_at.
  - unfold qual_top, qual_vars.
    cbn [qual_lvars]. intros n Hn.
    apply lvars_bv_elem in Hn.
    apply elem_of_empty in Hn as [].
  - unfold qual_top, qual_dom.
    cbn [qual_lvars]. apply not_elem_of_empty.
Qed.

Lemma over_top_basic b :
  basic_context_ty ∅ (CTOver b qual_top).
Proof.
  unfold basic_context_ty, qual_top.
  cbn [wf_context_ty_at qual_vars qual_lvars].
  intros v Hv.
  unfold elem_of, mapset.mapset_elem_of in Hv.
  cbn in Hv. discriminate.
Qed.

Lemma over_top_basic_lvars_relevant b x T :
  basic_context_ty_lvars
    (dom (relevant_env (<[LVFree x := T]> ∅)
      (CTOver b qual_top) (tret (vfvar x))))
    (CTOver b qual_top).
Proof.
  apply basic_context_ty_lvars_relevant_env.
  unfold basic_context_ty_lvars, qual_top.
  cbn [context_ty_lvars context_ty_lvars_at qual_vars qual_lvars
    context_ty_shape_ok].
  rewrite lvars_at_depth_empty.
  split; [apply empty_subseteq|reflexivity].
Qed.

Lemma basic_world_insert_relevant_ret_fvar_scope b x τ (m : WfWorldT) :
  wf_context_ty_at 0 ∅ τ ->
  m ⊨ basic_world_formula (<[LVFree x := TBase b]> ∅) ->
  lvars_fv
    (dom (relevant_env (<[LVFree x := TBase b]> ∅)
      τ (tret (vfvar x)))) ⊆ world_dom (m : WorldT).
Proof.
  intros Hτ Hworld.
  apply basic_world_formula_models_iff in Hworld as [_ [Hscope _]].
  etransitivity.
  - apply lvars_fv_mono.
    unfold relevant_env, lty_env_restrict_lvars.
    rewrite storeA_restrict_dom.
    intros u Hu.
    apply elem_of_intersection in Hu as [Hu _].
    exact Hu.
  - etransitivity; [|exact Hscope].
    reflexivity.
Qed.

Lemma over_top_ret_fvar_guard b x (m : WfWorldT) :
  m ⊨ basic_world_formula (<[LVFree x := TBase b]> ∅) ->
  m ⊨ ty_guard_formula
    (relevant_env (<[LVFree x := TBase b]> ∅)
      (CTOver b qual_top) (tret (vfvar x)))
    (CTOver b qual_top) (tret (vfvar x)).
Proof.
  intros Hworld.
  unfold ty_guard_formula.
  eapply res_models_and_intro_from_models.
  - apply context_ty_wf_formula_models_iff.
    repeat split.
    + relevant_env_norm. unfold lc_lvars. set_solver.
    + apply basic_world_insert_relevant_ret_fvar_scope.
      * apply over_top_basic.
      * exact Hworld.
    + apply over_top_basic_lvars_relevant.
  - eapply res_models_and_intro_from_models.
    + eapply basic_world_formula_subenv; [|exact Hworld].
      intros v T Hv. relevant_env_norm_in Hv. exact Hv.
    + eapply res_models_and_intro_from_models.
      * apply expr_basic_typing_formula_models_iff.
        repeat split.
        -- relevant_env_norm. unfold lc_lvars. set_solver.
        -- apply basic_world_insert_relevant_ret_fvar_scope.
           ++ apply over_top_basic.
           ++ exact Hworld.
        -- relevant_env_norm. constructor. constructor.
           rewrite lookup_insert_eq. reflexivity.
      * eapply (expr_total_formula_tret_of_basic
          (relevant_env (<[LVFree x := TBase b]> ∅)
            (CTOver b qual_top) (tret (vfvar x)))
          (vfvar x) (TBase b) m).
        -- eapply basic_world_formula_subenv; [|exact Hworld].
           intros v T Hv. relevant_env_norm_in Hv. exact Hv.
        -- apply expr_basic_typing_formula_models_iff.
           repeat split.
           ++ relevant_env_norm. unfold lc_lvars. set_solver.
           ++ apply basic_world_insert_relevant_ret_fvar_scope.
              ** apply over_top_basic.
              ** exact Hworld.
           ++ relevant_env_norm. constructor. constructor.
              rewrite lookup_insert_eq. reflexivity.
Qed.

Lemma over_top_ret_fvar_ty_denote_gas_scope gas b x (m : WfWorldT) :
  m ⊨ basic_world_formula (<[LVFree x := TBase b]> ∅) ->
  formula_scoped_in_world m
    (ty_denote_gas gas (<[LVFree x := TBase b]> ∅)
      (CTOver b qual_top) (tret (vfvar x))).
Proof.
  intros Hworld.
  unfold formula_scoped_in_world.
  etransitivity.
  - apply ty_denote_gas_fv_subset.
  - apply basic_world_formula_models_iff in Hworld as [_ [Hscope _]].
    etransitivity; [|exact Hscope].
    cbn [fv_tm fv_value fv_cty context_ty_lvars context_ty_lvars_at
      qual_vars qual_lvars].
    rewrite ?lvars_at_depth_empty, ?lvars_fv_empty.
    rewrite dom_insert_L, dom_empty_L.
    rewrite lvars_fv_union, lvars_fv_empty, lvars_fv_singleton_free.
    set_solver.
Qed.

Lemma over_top_ret_fvar_denotation_gas gas b x (m : WfWorldT) :
  m ⊨ basic_world_formula (<[LVFree x := TBase b]> ∅) ->
  m ⊨ ty_denote_gas gas (<[LVFree x := TBase b]> ∅)
    (CTOver b qual_top) (tret (vfvar x)).
Proof.
  intros Hworld.
  induction gas as [|gas IH]; cbn [ty_denote_gas].
  - eapply res_models_and_intro_from_models.
    + apply over_top_ret_fvar_guard. exact Hworld.
    + apply res_models_true.
  - eapply res_models_and_intro_from_models.
    + eapply ty_denote_gas_guard. exact IH.
    + eapply res_models_forall_intro.
      * pose proof (over_top_ret_fvar_ty_denote_gas_scope
            (S gas) b x m Hworld) as Hscope.
        cbn [ty_denote_gas] in Hscope.
        apply formula_scoped_and_r in Hscope. exact Hscope.
      * exists ({[x]} : aset).
        intros y Hy F HFin HFout my Hext.
        pose proof (res_extend_by_dom m F my Hext) as Hmydom.
        unfold ext_out in HFout. rewrite HFout in Hmydom.
        pose proof (basic_world_formula_models_iff
          (<[LVFree x := TBase b]> ∅) m) as Hworld_iff.
        apply Hworld_iff in Hworld as [_ [Hxscope _]].
        assert (Hxdom : x ∈ world_dom (m : WorldT)).
        {
          apply Hxscope.
          rewrite dom_insert_L, dom_empty_L, lvars_fv_union,
            lvars_fv_empty, lvars_fv_singleton_free.
          better_set_solver.
        }
	        (* The top qualifier branch is independent of the concrete result;
	           it only needs the singleton result cell introduced by [FForall]. *)
	        rewrite !formula_open_impl.
	        rewrite formula_open_expr_result_formula_shift0
	          by (try (constructor; constructor);
	              cbn [fv_tm fv_value]; set_solver).
	        rewrite formula_open_fibvars, formula_open_over.
		        rewrite formula_open_atom.
		        eapply res_models_impl_intro_scoped.
	        -- unfold formula_scoped_in_world.
	           rewrite formula_fv_expr_result_formula.
	           cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys].
	           rewrite ?lvars_fv_union, ?lvars_fv_empty,
	             ?lvars_fv_singleton_free.
	           rewrite Hmydom. clear -Hxdom.
	           intros a Ha.
	           apply elem_of_union in Ha as [Ha|Ha].
	           ++ apply elem_of_singleton in Ha as ->.
	              apply elem_of_union_l. exact Hxdom.
	           ++ apply elem_of_singleton in Ha as ->.
	              apply elem_of_union_r. apply elem_of_singleton. reflexivity.
	        -- unfold formula_scoped_in_world.
	           rewrite formula_fv_fibvars, formula_fv_over,
	             formula_fv_atom.
	           unfold qual_dom, qual_top, qual_vars.
	           cbn [qual_open_atom qual_lvars].
	           rewrite ?set_swap_empty, ?lvars_fv_empty.
	           replace (set_swap (LVBound 0) (LVFree y)
	               (∅ ∖ {[LVBound 0]} : lvset))
	             with (∅ : lvset).
	           2:{ replace (∅ ∖ {[LVBound 0]} : lvset) with (∅ : lvset)
	                 by better_set_solver.
	               rewrite set_swap_empty. reflexivity. }
	           rewrite lvars_fv_empty.
	           intros a Ha.
	           apply elem_of_union in Ha as [Ha|Ha];
	             apply elem_of_empty in Ha as [].
	        -- intros _.
	           replace (set_swap (LVBound 0) (LVFree y)
	               (qual_vars qual_top ∖ {[LVBound 0]}))
	             with (∅ : lvset).
	           2:{ unfold qual_top, qual_vars. cbn [qual_lvars].
	               better_set_solver. }
	           eapply res_models_FFibVars_intro.
	           ++ unfold formula_scoped_in_world.
	              rewrite formula_fv_fibvars, formula_fv_over,
	                formula_fv_atom.
	              rewrite qual_top_open.
	              unfold qual_dom, qual_top. cbn [qual_lvars].
	              rewrite lvars_fv_empty.
	              apply empty_subseteq.
	           ++ unfold lc_lvars. intros k Hk.
	              apply elem_of_empty in Hk as [].
	           ++ intros σ mfib Hproj.
	              rewrite formula_msubst_store_empty.
	              ** rewrite qual_top_open.
	                 eapply res_models_over_intro_same_from_model.
	                 apply res_models_atom_top.
	              ** eapply res_fiber_from_projection_empty_store_dom.
	                 exact Hproj.
Qed.

Lemma expr_total_formula_tprim_from_primop_arg
    op x (m : WfWorldT) :
  m ⊨ ctx_denote (CtxBind x (primop_arg_ty (Φ op))) ->
  m ⊨ expr_total_formula (tprim op (vfvar x)).
Proof.
  intros Hctx.
  apply expr_total_atom_world_to_formula.
  split.
  - rewrite res_lift_free_dom.
    cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys].
    intros v Hv.
    apply elem_of_singleton in Hv as ->.
    unfold lvars_of_atoms. apply elem_of_map.
    exists x. split; [reflexivity|].
    destruct (world_wf m) as [[σ Hσ] _].
    destruct (primop_arg_const_from_ctx op x m σ Hctx Hσ)
      as [c [Hlookup _]].
    pose proof (wfworld_store_dom m σ Hσ) as Hdom.
    assert (Hxdom : x ∈ dom (σ : gmap atom value)).
    { eapply elem_of_dom_2. exact Hlookup. }
    rewrite Hdom in Hxdom. exact Hxdom.
  - intros τ Hτ.
    destruct Hτ as [σ [Hσ ->]].
    destruct (primop_arg_const_from_ctx op x m σ Hctx Hσ)
      as [c [Hlookup Hbase]].
    assert (Herasure :
        prim_op_type op = (prim_arg_base (Φ op), prim_ret_base (Φ op))).
    {
      unfold Φ, concrete_primop_sig.
      destruct (prim_op_type op); reflexivity.
    }
    pose proof (prim_step_total_for_base op c
      (prim_arg_base (Φ op)) (prim_ret_base (Φ op))
      Herasure Hbase) as [c' Hstep].
    exists (vconst c').
    apply (expr_eval_prim_fvar_const_intro
      (lstore_lift_free σ) op x c c').
    * rewrite lstore_lift_free_lookup_free. exact Hlookup.
    * exact Hstep.
  all: try solve [better_set_solver | eauto].
Unshelve.
  all: try exact inhabitant; eauto.
  all: match goal with |- ?G => fail 1 G end.
Qed.

Lemma primop_graph_qual_open_msubst_prop_iff
    op x y (σx : StoreT)
    (s : LStoreOn
      (qual_vars
        (qual_msubst_store σx
          (qual_open_atom 0 y
            (qual_open_atom 1 x (primop_graph_qual op)))))) :
  x <> y ->
  dom (σx : StoreT) = {[x]} ->
  qual_prop
    (qual_msubst_store σx
      (qual_open_atom 0 y
        (qual_open_atom 1 x (primop_graph_qual op)))) s <->
  exists carg cret,
    σx !! x = Some (vconst carg) /\
    (lso_store s : LStore) !! LVFree y = Some (vconst cret) /\
    prim_step op carg cret.
Proof.
  intros Hxy Hσx_dom.
  cbn [qual_msubst_store qual_mlsubst qual_prop qual_lvars].
  set (q := qual_open_atom 0 y
    (qual_open_atom 1 x (primop_graph_qual op))).
  set (D := qual_vars q).
  set (ρ := atom_store_to_lvar_store σx : LStore).
  assert (HD : D = ({[LVFree x; LVFree y]} : lvset)).
  { subst D q. rewrite primop_graph_qual_open_vars by exact Hxy. reflexivity. }
  assert (Hρ_dom : dom (ρ : LStore) = ({[LVFree x]} : lvset)).
  {
    subst ρ.
    rewrite atom_store_to_lvar_store_dom.
    change (lvars_of_atoms (dom (σx : StoreT)) = ({[LVFree x]} : lvset)).
    rewrite Hσx_dom.
    unfold lvars_of_atoms. rewrite set_map_singleton_L. reflexivity.
  }
  split.
  - intros Hprop.
    change (qual_prop q (lstore_on_mlsubst_back D ρ s)) in Hprop.
    subst q.
    apply primop_graph_qual_open_prop_iff in Hprop; [|exact Hxy].
    destruct Hprop as [carg [cret [Hx [Hy Hstep]]]].
    exists carg, cret. split; [|split].
    + unfold lstore_on_mlsubst_back in Hx.
      cbn [lso_store storeAO_store] in Hx.
      apply map_lookup_union_Some_raw in Hx as [Hx | [_ Hx]].
      * apply elem_of_dom_2 in Hx as Hxdom.
        change (LVFree x ∈ dom (lso_store s : LStore)) in Hxdom.
        rewrite (lso_dom s) in Hxdom.
        change (LVFree x ∈ D ∖ dom (ρ : LStore)) in Hxdom.
        rewrite HD, Hρ_dom in Hxdom. better_set_solver.
      * unfold storeA_restrict, map_restrict in Hx.
        apply map_lookup_filter_Some in Hx as [Hx _].
        subst ρ. rewrite atom_store_to_lvar_store_lookup_free in Hx.
        exact Hx.
    + unfold lstore_on_mlsubst_back in Hy.
      cbn [lso_store storeAO_store] in Hy.
      apply map_lookup_union_Some_raw in Hy as [Hy | [_ Hy]].
      * exact Hy.
      * unfold storeA_restrict, map_restrict in Hy.
        apply map_lookup_filter_Some in Hy as [Hy _].
        subst ρ. rewrite atom_store_to_lvar_store_lookup_free in Hy.
        assert (Hyσx : (σx : gmap atom value) !! y = None).
        {
          apply not_elem_of_dom_1.
          change (y ∉ dom (σx : StoreT)).
          rewrite Hσx_dom. better_set_solver.
        }
        change ((σx : gmap atom value) !! y = Some (vconst cret)) in Hy.
        rewrite Hyσx in Hy. discriminate.
    + exact Hstep.
  - intros [carg [cret [Hx [Hy Hstep]]]].
    change (qual_prop q (lstore_on_mlsubst_back D ρ s)).
    subst q.
    apply primop_graph_qual_open_prop_iff; [exact Hxy|].
    exists carg, cret. split; [|split].
    + unfold lstore_on_mlsubst_back.
      cbn [lso_store storeAO_store].
      apply map_lookup_union_Some_raw. right. split.
      * apply not_elem_of_dom_1.
        change (LVFree x ∉ dom (lso_store s : LStore)).
        rewrite (lso_dom s).
        change (LVFree x ∉ D ∖ dom (ρ : LStore)).
        rewrite HD, Hρ_dom. better_set_solver.
      * apply storeA_restrict_lookup_some_2.
        -- subst ρ. rewrite atom_store_to_lvar_store_lookup_free. exact Hx.
        -- subst D. rewrite HD. better_set_solver.
    + unfold lstore_on_mlsubst_back.
      cbn [lso_store storeAO_store].
      apply map_lookup_union_Some_raw. left. exact Hy.
    + exact Hstep.
Qed.

Lemma primop_graph_type_qualifier_open_msubst_from_expr
    op x y (m mfib : WfWorldT) σx :
  x <> y ->
  res_fiber_from_projection m ({[x]} : aset) σx mfib ->
  m ⊨ ctx_denote (CtxBind x (primop_arg_ty (Φ op))) ->
  m ⊨ expr_result_formula (tprim op (vfvar x)) (LVFree y) ->
  mfib ⊨ formula_msubst_store σx
    (FAtom
      (qual_open_atom 0 y
        (qual_open_atom 1 x (primop_graph_qual op)))).
Proof.
  intros Hxy Hfiber Hctx Hexpr.
  formula_msubst_syntax_norm.
  apply res_models_atom_exact_iff.
  cbn [qualifier_exact_denote qual_msubst_store qual_mlsubst].
  set (q := qual_open_atom 0 y
    (qual_open_atom 1 x (primop_graph_qual op))).
  set (D := qual_vars q).
  set (ρ := atom_store_to_lvar_store σx : LStore).
  assert (HD : D = ({[LVFree x; LVFree y]} : lvset)).
  { subst D q. rewrite primop_graph_qual_open_vars by exact Hxy. reflexivity. }
  assert (Hρ_dom : dom (ρ : LStore) = ({[LVFree x]} : lvset)).
  {
    subst ρ.
    rewrite atom_store_to_lvar_store_dom.
    assert (Hxdom_m : x ∈ world_dom (m : WorldT)).
    {
      destruct (world_wf m) as [[σ Hσ] _].
      destruct (primop_arg_const_from_ctx op x m σ Hctx Hσ)
        as [c [Hx _]].
      pose proof (wfworld_store_dom m σ Hσ) as Hdom.
      apply elem_of_dom_2 in Hx. rewrite Hdom in Hx. exact Hx.
    }
    assert (Hσx_dom : dom (σx : StoreT) = {[x]}).
    {
      destruct Hfiber as [Hproj _].
      pose proof (wfworld_store_dom (res_restrict m ({[x]} : aset))
        σx Hproj) as Hdom.
      change (dom (σx : StoreT) =
        world_dom (res_restrict m ({[x]} : aset) : WorldT)) in Hdom.
      cbn in Hdom.
      rewrite Hdom.
      apply set_eq. intros a. split.
      - intros Ha. apply elem_of_intersection in Ha as [_ Ha]. exact Ha.
      - intros Ha. apply elem_of_singleton in Ha as ->.
        apply elem_of_intersection. split; [exact Hxdom_m|].
        apply elem_of_singleton. reflexivity.
    }
    change (lvars_of_atoms (dom (σx : StoreT)) = ({[LVFree x]} : lvset)).
    rewrite Hσx_dom.
    unfold lvars_of_atoms. rewrite set_map_singleton_L. reflexivity.
  }
  assert (HD' : D ∖ dom (ρ : LStore) = ({[LVFree y]} : lvset)).
  { rewrite HD, Hρ_dom. better_set_solver. }
  assert (Hσx_dom : dom (σx : StoreT) = {[x]}).
  {
    destruct Hfiber as [Hproj _].
    pose proof (wfworld_store_dom (res_restrict m ({[x]} : aset))
      σx Hproj) as Hdom.
    change (dom (σx : StoreT) =
      world_dom (res_restrict m ({[x]} : aset) : WorldT)) in Hdom.
    cbn in Hdom.
    assert (Hxdom_m : x ∈ world_dom (m : WorldT)).
    {
      destruct (world_wf m) as [[σ Hσ] _].
      destruct (primop_arg_const_from_ctx op x m σ Hctx Hσ)
        as [c [Hx _]].
      pose proof (wfworld_store_dom m σ Hσ) as Hdomσ.
      apply elem_of_dom_2 in Hx. rewrite Hdomσ in Hx. exact Hx.
    }
    rewrite Hdom.
    apply set_eq. intros a. split.
    - intros Ha. apply elem_of_intersection in Ha as [_ Ha]. exact Ha.
    - intros Ha. apply elem_of_singleton in Ha as ->.
      apply elem_of_intersection. split; [exact Hxdom_m|].
      apply elem_of_singleton. reflexivity.
  }
  destruct (world_wf mfib) as [[σ0 Hσ0] _].
  pose proof (res_fiber_from_projection_store_source m mfib ({[x]} : aset)
    σx σ0 Hfiber Hσ0) as Hσ0m.
  destruct (primop_arg_const_from_ctx op x m σ0 Hctx Hσ0m)
    as [carg0 [Hx0 _]].
  destruct (expr_result_formula_prim_fvar_lookup op x y m σ0 carg0
    Hexpr Hσ0m Hx0) as [cret0 [Hy0 Hstep0]].
  assert (Hymfib : y ∈ world_dom (mfib : WorldT)).
  {
    apply elem_of_dom_2 in Hy0.
    pose proof (wfworld_store_dom mfib σ0 Hσ0) as Hdom.
    rewrite Hdom in Hy0. exact Hy0.
  }
  assert (Hlc : lc_lvars (D ∖ dom (ρ : LStore))).
  {
    rewrite HD'. unfold lc_lvars. intros v Hv.
    apply elem_of_singleton in Hv as ->. constructor.
  }
  assert (Hsub : lvars_fv (D ∖ dom (ρ : LStore)) ⊆
      world_dom (mfib : WorldT)).
  {
    rewrite HD', lvars_fv_singleton_free.
    intros a Ha. apply elem_of_singleton in Ha as ->. exact Hymfib.
  }
  exists Hlc, Hsub.
  intros s.
  rewrite (primop_graph_qual_open_msubst_prop_iff op x y σx s Hxy Hσx_dom).
  split.
  - intros [carg [cret [Hx [Hy Hstep]]]].
    unfold lstore_in_lworld_on, lworld_on_lift.
    cbn [lw lraw_world raw_worldA worldA_stores].
    exists (lstore_lift_free (store_restrict σ0 (lvars_fv (D ∖ dom (ρ : LStore))))).
    split.
    + exists (store_restrict σ0 (lvars_fv (D ∖ dom (ρ : LStore)))).
      split.
      * exists σ0. split; [exact Hσ0|reflexivity].
      * reflexivity.
	    + assert (cret = cret0).
	      {
	        assert (carg = carg0).
	        {
	          pose proof (res_fiber_from_projection_lookup m mfib
	            ({[x]} : aset) σx σ0 x Hfiber Hσ0 ltac:(set_solver))
	            as Hxlookup.
	          change ((σ0 : gmap atom value) !! x =
	            (σx : gmap atom value) !! x) in Hxlookup.
	          change ((σx : gmap atom value) !! x =
	            Some (vconst carg)) in Hx.
	          rewrite Hx0 in Hxlookup.
	          rewrite Hx in Hxlookup.
	          inversion Hxlookup. reflexivity.
	        }
	        subst carg.
	        eapply prim_step_det; eassumption.
	      }
	      subst cret.
	      eapply (lstore_lift_restrict_singleton_free_eq y
	        (D ∖ dom (ρ : LStore)) s σ0 (vconst cret0));
	        eassumption.
  - intros Hmem.
    destruct (lstore_in_lworld_on_singleton_free_lookup y
      (D ∖ dom (ρ : LStore)) mfib Hlc Hsub s HD' Hmem)
      as [τfull [Hτfull Hsy]].
    pose proof (res_fiber_from_projection_store_source m mfib ({[x]} : aset)
      σx τfull Hfiber Hτfull) as Hτm.
    destruct (primop_arg_const_from_ctx op x m τfull Hctx Hτm)
      as [carg [Hxτ _]].
    destruct (expr_result_formula_prim_fvar_lookup op x y m τfull carg
      Hexpr Hτm Hxτ) as [cret [Hyτ Hstep]].
    exists carg, cret. split; [|split].
    + pose proof (res_fiber_from_projection_lookup m mfib ({[x]} : aset)
        σx τfull x Hfiber Hτfull ltac:(set_solver)) as Hlook.
      change ((τfull : gmap atom value) !! x =
        (σx : gmap atom value) !! x) in Hlook.
      change ((τfull : gmap atom value) !! x =
        Some (vconst carg)) in Hxτ.
      rewrite Hxτ in Hlook. symmetry. exact Hlook.
    + replace (storeAO_store s !! LVFree y)
        with ((τfull : gmap atom value) !! y).
      { exact Hyτ. }
    + exact Hstep.
Qed.

Lemma primop_graph_fib_over_from_expr
    op x y (m : WfWorldT) :
  x <> y ->
  m ⊨ ctx_denote (CtxBind x (primop_arg_ty (Φ op))) ->
  m ⊨ expr_result_formula (tprim op (vfvar x)) (LVFree y) ->
  m ⊨ FFibVars
    (qual_vars
      (qual_open_atom 0 y
        (qual_open_atom 1 x (primop_graph_qual op))) ∖ {[LVFree y]})
    (FOver (FAtom
      (qual_open_atom 0 y
        (qual_open_atom 1 x (primop_graph_qual op))))).
Proof.
  intros Hxy Hctx Hexpr.
  eapply res_models_FFibVars_intro.
  - pose proof (res_models_scoped _ _ Hexpr) as Hscope.
    unfold formula_scoped_in_world in Hscope |- *.
    intros a Ha.
    apply Hscope.
    rewrite formula_fv_expr_result_formula.
    cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys].
	    rewrite !lvars_fv_union, !lvars_fv_singleton_free.
	    rewrite formula_fv_fibvars, formula_fv_over,
	      formula_fv_atom in Ha.
	    unfold qual_dom in Ha.
	    replace (lvars_fv
	        (qual_vars
	          (qual_open_atom 0 y (qual_open_atom 1 x (primop_graph_qual op))) ∖
	          {[LVFree y]})) with ({[x]} : aset) in Ha.
	    2:{
	      rewrite primop_graph_qual_open_vars by exact Hxy.
	      replace (({[LVFree x; LVFree y]} ∖ {[LVFree y]}) : lvset)
	        with ({[LVFree x]} : lvset) by better_set_solver.
	      symmetry. apply lvars_fv_singleton_free.
	    }
	    replace (lvars_fv
	        (qual_vars
	          (qual_open_atom 0 y (qual_open_atom 1 x (primop_graph_qual op))))
	        ) with ({[x; y]} : aset) in Ha.
	    2:{
	      rewrite primop_graph_qual_open_vars by exact Hxy.
	      rewrite lvars_fv_union, !lvars_fv_singleton_free.
	      better_set_solver.
	    }
	    better_set_solver.
  - rewrite primop_graph_qual_open_vars by exact Hxy.
    unfold lc_lvars. set_solver.
  - intros σ mfib Hproj.
    formula_msubst_syntax_norm.
    replace (lvars_fv
        (qual_vars
          (qual_open_atom 0 y (qual_open_atom 1 x (primop_graph_qual op))) ∖
          {[LVFree y]})) with ({[x]} : aset) in Hproj.
    2:{
      rewrite primop_graph_qual_open_vars by exact Hxy.
      replace (({[LVFree x; LVFree y]} ∖ {[LVFree y]}) : lvset)
        with ({[LVFree x]} : lvset) by better_set_solver.
      symmetry. apply lvars_fv_singleton_free.
    }
    eapply res_models_over_intro_same_from_model.
    eapply (primop_graph_type_qualifier_open_msubst_from_expr
      op x y m mfib σ);
      [exact Hxy|exact Hproj|exact Hctx|exact Hexpr].
Qed.

Lemma primop_graph_fib_under_from_expr
    op x y (m : WfWorldT) :
  x <> y ->
  m ⊨ ctx_denote (CtxBind x (primop_arg_ty (Φ op))) ->
  m ⊨ expr_result_formula (tprim op (vfvar x)) (LVFree y) ->
  m ⊨ FFibVars
    (qual_vars
      (qual_open_atom 0 y
        (qual_open_atom 1 x (primop_graph_qual op))) ∖ {[LVFree y]})
    (FUnder (FAtom
      (qual_open_atom 0 y
        (qual_open_atom 1 x (primop_graph_qual op))))).
Proof.
  intros Hxy Hctx Hexpr.
  eapply res_models_FFibVars_intro.
  - pose proof (res_models_scoped _ _ Hexpr) as Hscope.
    unfold formula_scoped_in_world in Hscope |- *.
    intros a Ha.
    apply Hscope.
    rewrite formula_fv_expr_result_formula.
    cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys].
	    rewrite !lvars_fv_union, !lvars_fv_singleton_free.
	    rewrite formula_fv_fibvars, formula_fv_under,
	      formula_fv_atom in Ha.
	    unfold qual_dom in Ha.
	    replace (lvars_fv
	        (qual_vars
	          (qual_open_atom 0 y (qual_open_atom 1 x (primop_graph_qual op))) ∖
	          {[LVFree y]})) with ({[x]} : aset) in Ha.
	    2:{
	      rewrite primop_graph_qual_open_vars by exact Hxy.
	      replace (({[LVFree x; LVFree y]} ∖ {[LVFree y]}) : lvset)
	        with ({[LVFree x]} : lvset) by better_set_solver.
	      symmetry. apply lvars_fv_singleton_free.
	    }
	    replace (lvars_fv
	        (qual_vars
	          (qual_open_atom 0 y (qual_open_atom 1 x (primop_graph_qual op))))
	        ) with ({[x; y]} : aset) in Ha.
	    2:{
	      rewrite primop_graph_qual_open_vars by exact Hxy.
	      rewrite lvars_fv_union, !lvars_fv_singleton_free.
	      better_set_solver.
	    }
	    better_set_solver.
  - rewrite primop_graph_qual_open_vars by exact Hxy.
    unfold lc_lvars. set_solver.
  - intros σ mfib Hproj.
    formula_msubst_syntax_norm.
    replace (lvars_fv
        (qual_vars
          (qual_open_atom 0 y (qual_open_atom 1 x (primop_graph_qual op))) ∖
          {[LVFree y]})) with ({[x]} : aset) in Hproj.
    2:{
      rewrite primop_graph_qual_open_vars by exact Hxy.
      replace (({[LVFree x; LVFree y]} ∖ {[LVFree y]}) : lvset)
        with ({[LVFree x]} : lvset) by better_set_solver.
      symmetry. apply lvars_fv_singleton_free.
    }
    eapply res_models_under_intro_same_from_model.
    eapply (primop_graph_type_qualifier_open_msubst_from_expr
      op x y m mfib σ);
      [exact Hxy|exact Hproj|exact Hctx|exact Hexpr].
Qed.

Lemma primop_opened_result_guard_formula
    op x τbody (τ : context_ty) (m : WfWorldT) :
  τ = ({0 ~> x} τbody) ->
  wf_context_ty_at 1 ∅ τbody ->
  erase_ty τbody = TBase (prim_ret_base (Φ op)) ->
  m ⊨ ctx_denote (CtxBind x (primop_arg_ty (Φ op))) ->
  m ⊨ ty_guard_formula
    (relevant_env
      (atom_env_to_lty_env (erase_ctx (CtxBind x (primop_arg_ty (Φ op)))))
      τ (tprim op (vfvar x)))
    τ (tprim op (vfvar x)).
Proof.
  intros -> Hwf Herase Hctx.
  unfold ty_guard_formula.
  repeat rewrite res_models_and_iff.
  assert (Hstatic_full :
      m ⊨ ty_static_guard_formula
        (atom_env_to_lty_env
          (erase_ctx (CtxBind x (primop_arg_ty (Φ op)))))
        ({0 ~> x} τbody) (tprim op (vfvar x))).
  {
    unfold ty_static_guard_formula.
    repeat rewrite res_models_and_iff.
    pose proof (ctx_denote_under_basic_world
      (∅ : gmap atom ty) (CtxBind x (primop_arg_ty (Φ op))) m Hctx)
      as Hworld.
    ctx_erasure_under_norm_in Hworld.
    apply basic_world_formula_models_iff in Hworld
      as [Hlc [Hscope Htyped]].
    split.
    - apply context_ty_wf_formula_models_iff.
      split; [exact Hlc|]. split; [exact Hscope|].
      unfold basic_context_ty_lvars, context_ty_lvars.
      replace (dom (atom_env_to_lty_env
          (erase_ctx (CtxBind x (primop_arg_ty (Φ op))))))
        with (lvars_of_atoms ({[x]} : aset)).
      2:{
        rewrite atom_store_to_lvar_store_dom.
        rewrite erase_ctx_bind_dom.
        unfold lvars_of_atoms.
        rewrite set_map_singleton_L.
        reflexivity.
      }
      eapply wf_context_ty_at_to_lvars_shape.
      replace ({[x]} : aset) with (∅ ∪ {[x]} : aset) by set_solver.
      eapply wf_context_ty_at_open_at.
      + set_solver.
      + exact Hwf.
    - split.
      + apply basic_world_formula_models_iff.
        split; [exact Hlc|]. split; [exact Hscope|exact Htyped].
      + apply expr_basic_typing_formula_models_iff.
        split; [exact Hlc|]. split; [exact Hscope|].
        rewrite cty_open_preserves_erasure, Herase.
        eapply (BTT_Op _ op _ (prim_arg_base (Φ op))
          (prim_ret_base (Φ op))).
        * unfold Φ, concrete_primop_sig.
          destruct (prim_op_type op); reflexivity.
        * apply BVT_FVar.
          cbn [erase_ctx].
          rewrite atom_store_to_lvar_store_lookup_free.
          cbn.
          unfold primop_arg_ty, Φ, concrete_primop_sig.
          destruct (prim_op_type op).
          apply lookup_singleton_Some. split; reflexivity.
  }
  pose proof (ty_static_guard_relevant_of_full
    (atom_env_to_lty_env (erase_ctx (CtxBind x (primop_arg_ty (Φ op)))))
    ({0 ~> x} τbody) (tprim op (vfvar x)) m Hstatic_full)
    as Hstatic_rel.
  unfold ty_static_guard_formula in Hstatic_rel.
  repeat rewrite res_models_and_iff in Hstatic_rel.
  destruct Hstatic_rel as [Hwf_rel [Hworld_rel Hbasic_rel]].
  split; [exact Hwf_rel|].
  split; [exact Hworld_rel|].
  split; [exact Hbasic_rel|].
  apply expr_total_formula_tprim_from_primop_arg. exact Hctx.
Qed.

Definition primop_graph_over_formula (op : prim_op) (x : atom) : FormulaT :=
  FForall
    (FImpl
      (expr_result_formula (tm_shift 0 (tprim op (vfvar x))) (LVBound 0))
      (FFibVars
        (qual_vars (qual_open_atom 1 x (primop_graph_qual op)) ∖
          {[LVBound 0]})
        (FOver
          (FAtom
            (qual_open_atom 1 x (primop_graph_qual op)))))).

Definition primop_graph_under_formula (op : prim_op) (x : atom) : FormulaT :=
  FForall
    (FImpl
      (expr_result_formula (tm_shift 0 (tprim op (vfvar x))) (LVBound 0))
      (FFibVars
        (qual_vars (qual_open_atom 1 x (primop_graph_qual op)) ∖
          {[LVBound 0]})
        (FUnder
          (FAtom
            (qual_open_atom 1 x (primop_graph_qual op)))))).

Lemma formula_fv_primop_graph_over_formula op x :
  formula_fv (primop_graph_over_formula op x) = ({[x]} : aset).
Proof.
  unfold primop_graph_over_formula, formula_fv, formula_lvars.
  unfold expr_result_formula,
    expr_result_qual, qual_vars.
  cbn [formula_lvars_at qual_lvars tm_shift value_shift tm_lvars
    tm_lvars_at value_lvars_at lvar_value_keys primop_graph_qual].
  rewrite ?lvars_at_depth_union, ?lvars_at_depth_empty,
    ?lvars_at_depth_singleton_bound0_succ,
    ?lvars_at_depth_singleton_free.
  rewrite primop_graph_qual_arg_open_vars.
  replace ({[LVBound 0; LVFree x]} ∖ {[LVBound 0]} : lvset)
    with ({[LVFree x]} : lvset) by set_solver.
  cbn [qual_vars qual_lvars].
  rewrite primop_graph_qual_arg_open_vars.
  replace ({[LVFree x; LVBound 0]} : lvset)
    with ({[LVFree x]} ∪ {[LVBound 0]} : lvset) by set_solver.
  rewrite ?lvars_at_depth_union, ?lvars_at_depth_singleton_free,
    ?lvars_at_depth_singleton_bound0_succ.
  rewrite ?lvars_at_depth_singleton_free.
  rewrite ?lvars_fv_union, ?lvars_fv_empty,
    ?lvars_fv_singleton_bound, ?lvars_fv_singleton_free.
  set_solver.
Qed.

Lemma formula_fv_primop_graph_under_formula op x :
  formula_fv (primop_graph_under_formula op x) = ({[x]} : aset).
Proof.
  unfold primop_graph_under_formula, formula_fv, formula_lvars.
  unfold expr_result_formula,
    expr_result_qual, qual_vars.
  cbn [formula_lvars_at qual_lvars tm_shift value_shift tm_lvars
    tm_lvars_at value_lvars_at lvar_value_keys primop_graph_qual].
  rewrite ?lvars_at_depth_union, ?lvars_at_depth_empty,
    ?lvars_at_depth_singleton_bound0_succ,
    ?lvars_at_depth_singleton_free.
  rewrite primop_graph_qual_arg_open_vars.
  replace ({[LVBound 0; LVFree x]} ∖ {[LVBound 0]} : lvset)
    with ({[LVFree x]} : lvset) by set_solver.
  cbn [qual_vars qual_lvars].
  rewrite primop_graph_qual_arg_open_vars.
  replace ({[LVFree x; LVBound 0]} : lvset)
    with ({[LVFree x]} ∪ {[LVBound 0]} : lvset) by set_solver.
  rewrite ?lvars_at_depth_union, ?lvars_at_depth_singleton_free,
    ?lvars_at_depth_singleton_bound0_succ.
  rewrite ?lvars_at_depth_singleton_free.
  rewrite ?lvars_fv_union, ?lvars_fv_empty,
    ?lvars_fv_singleton_bound, ?lvars_fv_singleton_free.
  set_solver.
Qed.

Local Ltac primop_graph_scope_norm :=
  unfold formula_scoped_in_world;
	  rewrite ?formula_fv_forall, ?formula_fv_impl, ?formula_fv_fibvars,
	    ?formula_fv_over, ?formula_fv_under, ?formula_fv_basic_world_formula,
	    ?formula_fv_expr_result_formula, ?formula_fv_atom;
	  unfold qual_dom, basic_world_formula, expr_result_formula,
	    FFiberAtom;
	  cbn [tm_shift value_shift tm_lvars tm_lvars_at value_lvars_at
	    lvar_value_keys formula_lvars formula_lvars_at qual_vars
	    qual_lvars primop_graph_qual];
  rewrite ?lvars_at_depth_union, ?lvars_at_depth_empty,
    ?lvars_at_depth_singleton_bound0_succ,
    ?lvars_at_depth_singleton_free,
    ?lvars_fv_union, ?lvars_fv_empty, ?lvars_fv_singleton_bound,
    ?lvars_fv_singleton_free, ?dom_insert_L, ?dom_empty_L.

Local Ltac primop_graph_scope_from Hctx Hdom HFout :=
  primop_graph_scope_norm;
  try rewrite primop_graph_qual_arg_open_vars;
  try rewrite primop_graph_qual_open_vars by set_solver;
  repeat match goal with
  | |- context[({[?v]} ∖ {[?v]} : lvset)] =>
      replace ({[v]} ∖ {[v]} : lvset) with (∅ : lvset) by set_solver
  | |- context[lvars_at_depth 1 ({[LVBound 0]} ∪ ∅)] =>
      replace (lvars_at_depth 1 ({[LVBound 0]} ∪ ∅))
        with (∅ : lvset)
        by (rewrite lvars_at_depth_union,
              lvars_at_depth_singleton_bound0_succ,
              lvars_at_depth_empty; set_solver)
  | |- context[lvars_at_depth 1 ({[LVBound 0; LVFree ?x]} ∖ {[LVBound 0]})] =>
      replace (lvars_at_depth 1 ({[LVBound 0; LVFree x]} ∖ {[LVBound 0]}))
        with ({[LVFree x]} : lvset)
        by (replace (({[LVBound 0; LVFree x]} ∖ {[LVBound 0]}) : lvset)
              with ({[LVFree x]} : lvset) by set_solver;
            rewrite lvars_at_depth_singleton_free; reflexivity)
  | |- context[lvars_at_depth 1 ({[LVBound 0; LVFree ?x]})] =>
      replace (lvars_at_depth 1 ({[LVBound 0; LVFree x]}))
        with ({[LVFree x]} : lvset)
        by (replace ({[LVBound 0; LVFree x]} : lvset)
              with ({[LVBound 0]} ∪ {[LVFree x]} : lvset) by set_solver;
            rewrite lvars_at_depth_union,
              lvars_at_depth_singleton_bound0_succ,
              lvars_at_depth_singleton_free; set_solver)
  | |- context[lvars_fv (({[LVFree ?x; LVFree ?y]} ∖ {[LVFree ?y]}) : lvset)] =>
      replace (lvars_fv (({[LVFree x; LVFree y]} ∖ {[LVFree y]}) : lvset))
        with ({[x]} : aset)
        by (replace (({[LVFree x; LVFree y]} ∖ {[LVFree y]}) : lvset)
              with ({[LVFree x]} : lvset) by set_solver;
            symmetry; apply lvars_fv_singleton_free)
  end;
  try (rewrite Hdom, HFout);
  let Hx := fresh "Hx_world" in
  pose proof (primop_arg_in_world _ _ _ Hctx) as Hx;
  set_solver.

Local Ltac primop_graph_closed_scope_from Hctx :=
  primop_graph_scope_norm;
  try rewrite primop_graph_qual_arg_open_vars;
  try rewrite primop_graph_qual_open_vars by set_solver;
  repeat match goal with
  | |- context[({[?v]} ∖ {[?v]} : lvset)] =>
      replace ({[v]} ∖ {[v]} : lvset) with (∅ : lvset) by set_solver
  | |- context[lvars_at_depth 1 ({[LVBound 0]} ∪ ∅)] =>
      replace (lvars_at_depth 1 ({[LVBound 0]} ∪ ∅))
        with (∅ : lvset)
        by (rewrite lvars_at_depth_union,
              lvars_at_depth_singleton_bound0_succ,
              lvars_at_depth_empty; set_solver)
  | |- context[lvars_at_depth 1 ({[LVBound 0; LVFree ?x]} ∖ {[LVBound 0]})] =>
      replace (lvars_at_depth 1 ({[LVBound 0; LVFree x]} ∖ {[LVBound 0]}))
        with ({[LVFree x]} : lvset)
        by (replace (({[LVBound 0; LVFree x]} ∖ {[LVBound 0]}) : lvset)
              with ({[LVFree x]} : lvset) by set_solver;
            rewrite lvars_at_depth_singleton_free; reflexivity)
  | |- context[lvars_at_depth 1 ({[LVBound 0; LVFree ?x]})] =>
      replace (lvars_at_depth 1 ({[LVBound 0; LVFree x]}))
        with ({[LVFree x]} : lvset)
        by (replace ({[LVBound 0; LVFree x]} : lvset)
              with ({[LVBound 0]} ∪ {[LVFree x]} : lvset) by set_solver;
            rewrite lvars_at_depth_union,
              lvars_at_depth_singleton_bound0_succ,
              lvars_at_depth_singleton_free; set_solver)
  | |- context[lvars_fv (({[LVFree ?x; LVFree ?y]} ∖ {[LVFree ?y]}) : lvset)] =>
      replace (lvars_fv (({[LVFree x; LVFree y]} ∖ {[LVFree y]}) : lvset))
        with ({[x]} : aset)
        by (replace (({[LVFree x; LVFree y]} ∖ {[LVFree y]}) : lvset)
              with ({[LVFree x]} : lvset) by set_solver;
            symmetry; apply lvars_fv_singleton_free)
  end;
  rewrite ?lvars_fv_empty, ?lvars_fv_singleton_free;
  let Hx := fresh "Hx_world" in
  pose proof (primop_arg_in_world _ _ _ Hctx) as Hx;
  better_set_solver.

Lemma primop_graph_over_formula_scope op x (m : WfWorldT) :
  m ⊨ ctx_denote (CtxBind x (primop_arg_ty (Φ op))) ->
  formula_scoped_in_world m (primop_graph_over_formula op x).
Proof.
  intros Hctx.
  unfold formula_scoped_in_world.
  rewrite formula_fv_primop_graph_over_formula.
  intros a Ha.
  apply elem_of_singleton in Ha as ->.
  exact (primop_arg_in_world op x m Hctx).
Qed.

Lemma primop_graph_under_formula_scope op x (m : WfWorldT) :
  m ⊨ ctx_denote (CtxBind x (primop_arg_ty (Φ op))) ->
  formula_scoped_in_world m (primop_graph_under_formula op x).
Proof.
  intros Hctx.
  unfold formula_scoped_in_world.
  rewrite formula_fv_primop_graph_under_formula.
  intros a Ha.
  apply elem_of_singleton in Ha as ->.
  exact (primop_arg_in_world op x m Hctx).
Qed.

Lemma primop_graph_over_denotation_gas
    gas op x (m : WfWorldT) :
  m ⊨ ctx_denote (CtxBind x (primop_arg_ty (Φ op))) ->
  m ⊨ ty_denote_gas gas
    (atom_env_to_lty_env (erase_ctx (CtxBind x (primop_arg_ty (Φ op)))))
    ({0 ~> x}
      (CTOver (prim_ret_base (Φ op)) (primop_graph_qual op)))
    (tprim op (vfvar x)).
Proof.
  intros Hctx.
  induction gas as [|gas IH]; cbn [ty_denote_gas].
  - eapply res_models_and_intro_from_models.
    + eapply primop_opened_result_guard_formula.
      * reflexivity.
      * unfold Φ, concrete_primop_sig.
        destruct (prim_op_type op); unfold over_ty.
        cbn [wf_context_ty_at qual_vars primop_graph_qual qual_lvars].
        unfold lvars_wf_at. set_solver.
      * reflexivity.
      * exact Hctx.
    + apply res_models_true.
  - eapply res_models_and_intro_from_models.
    + eapply primop_opened_result_guard_formula.
      * reflexivity.
      * unfold Φ, concrete_primop_sig.
        destruct (prim_op_type op); unfold over_ty.
        cbn [wf_context_ty_at qual_vars primop_graph_qual qual_lvars].
        unfold lvars_wf_at. set_solver.
      * reflexivity.
      * exact Hctx.
    + change (m ⊨ primop_graph_over_formula op x).
      pose proof (primop_graph_over_formula_scope op x m Hctx)
        as Hforall_scope.
      eapply res_models_forall_intro.
      * exact Hforall_scope.
      * exists ({[x]} : aset).
        intros y Hy F HFin HFout my Hext.
        pose proof (res_extend_by_dom m F my Hext) as Hdom.
        pose proof (res_extend_by_le m F my Hext) as Hle.
        pose proof (res_models_kripke _ _ _ Hle Hctx) as Hctx_my.
        assert (Hxy : x <> y) by set_solver.
        match goal with
        | |- my ⊨ formula_open 0 y ?φ =>
            assert (Hopened_scope :
              formula_scoped_in_world my (formula_open 0 y φ))
            by (eapply formula_scoped_forall_open_res_le;
                [exact Hforall_scope
                |exact Hle
                |rewrite Hdom; try rewrite HFout; set_solver])
	        end.
	        rewrite !formula_open_impl in Hopened_scope |- *.
	        rewrite formula_open_expr_result_formula_shift0 in Hopened_scope
	          by (try (constructor; constructor);
	              cbn [fv_tm fv_value]; set_solver).
	        rewrite formula_open_expr_result_formula_shift0
	          by (try (constructor; constructor);
	              cbn [fv_tm fv_value]; set_solver).
	        rewrite formula_open_fibvars, formula_open_over in Hopened_scope |- *.
	        rewrite formula_open_atom in Hopened_scope.
	        rewrite formula_open_atom.
		        eapply res_models_impl_intro.
	        -- exact Hopened_scope.
	        -- intros Hexpr.
	           replace
	             (set_swap (LVBound 0) (LVFree y)
	               (qual_vars (qual_open_atom 1 x (primop_graph_qual op)) ∖
	                 {[LVBound 0]}))
	             with
	             (qual_vars
	               (qual_open_atom 0 y
	                 (qual_open_atom 1 x (primop_graph_qual op))) ∖
	               {[LVFree y]}).
	           2:{ symmetry. apply primop_graph_qual_fibvars_set. exact Hxy. }
	           exact (primop_graph_fib_over_from_expr
	             op x y my Hxy Hctx_my Hexpr).
Qed.

Lemma primop_graph_under_denotation_gas
    gas op x (m : WfWorldT) :
  m ⊨ ctx_denote (CtxBind x (primop_arg_ty (Φ op))) ->
  m ⊨ ty_denote_gas gas
    (atom_env_to_lty_env (erase_ctx (CtxBind x (primop_arg_ty (Φ op)))))
    ({0 ~> x}
      (CTUnder (prim_ret_base (Φ op)) (primop_graph_qual op)))
    (tprim op (vfvar x)).
Proof.
  intros Hctx.
  induction gas as [|gas IH]; cbn [ty_denote_gas].
  - eapply res_models_and_intro_from_models.
    + eapply primop_opened_result_guard_formula.
      * reflexivity.
      * unfold Φ, concrete_primop_sig.
        destruct (prim_op_type op); unfold under_ty.
        cbn [wf_context_ty_at qual_vars primop_graph_qual qual_lvars].
        unfold lvars_wf_at. set_solver.
      * reflexivity.
      * exact Hctx.
    + apply res_models_true.
  - eapply res_models_and_intro_from_models.
    + eapply primop_opened_result_guard_formula.
      * reflexivity.
      * unfold Φ, concrete_primop_sig.
        destruct (prim_op_type op); unfold under_ty.
        cbn [wf_context_ty_at qual_vars primop_graph_qual qual_lvars].
        unfold lvars_wf_at. set_solver.
      * reflexivity.
      * exact Hctx.
    + change (m ⊨ primop_graph_under_formula op x).
      pose proof (primop_graph_under_formula_scope op x m Hctx)
        as Hforall_scope.
      eapply res_models_forall_intro.
      * exact Hforall_scope.
      * exists ({[x]} : aset).
        intros y Hy F HFin HFout my Hext.
        pose proof (res_extend_by_dom m F my Hext) as Hdom.
        pose proof (res_extend_by_le m F my Hext) as Hle.
        pose proof (res_models_kripke _ _ _ Hle Hctx) as Hctx_my.
        assert (Hxy : x <> y) by set_solver.
        match goal with
        | |- my ⊨ formula_open 0 y ?φ =>
            assert (Hopened_scope :
              formula_scoped_in_world my (formula_open 0 y φ))
            by (eapply formula_scoped_forall_open_res_le;
                [exact Hforall_scope
                |exact Hle
                |rewrite Hdom; try rewrite HFout; set_solver])
	        end.
	        rewrite !formula_open_impl in Hopened_scope |- *.
	        rewrite formula_open_expr_result_formula_shift0 in Hopened_scope
	          by (try (constructor; constructor);
	              cbn [fv_tm fv_value]; set_solver).
	        rewrite formula_open_expr_result_formula_shift0
	          by (try (constructor; constructor);
	              cbn [fv_tm fv_value]; set_solver).
	        rewrite formula_open_fibvars, formula_open_under in Hopened_scope |- *.
	        rewrite formula_open_atom in Hopened_scope.
	        rewrite formula_open_atom.
		        eapply res_models_impl_intro.
	        -- exact Hopened_scope.
	        -- intros Hexpr.
	           replace
	             (set_swap (LVBound 0) (LVFree y)
	               (qual_vars (qual_open_atom 1 x (primop_graph_qual op)) ∖
	                 {[LVBound 0]}))
	             with
	             (qual_vars
	               (qual_open_atom 0 y
	                 (qual_open_atom 1 x (primop_graph_qual op))) ∖
	               {[LVFree y]}).
	           2:{ symmetry. apply primop_graph_qual_fibvars_set. exact Hxy. }
	           exact (primop_graph_fib_under_from_expr
	             op x y my Hxy Hctx_my Hexpr).
Qed.

Lemma primop_graph_result_denotation
    op x :
  ctx_denote (CtxBind x (primop_arg_ty (Φ op))) ⊫
    ty_denote (erase_ctx (CtxBind x (primop_arg_ty (Φ op))))
      ({0 ~> x} (primop_result_ty (Φ op)))
      (tprim op (vfvar x)).
Proof.
  intros m Hctx.
  unfold ty_denote.
  rewrite primop_result_ty_eq.
  unfold precise_ty.
  cbn [cty_depth Nat.max ty_denote_gas cty_open].
  eapply res_models_and_intro_from_models.
  - eapply primop_opened_result_guard_formula.
    + reflexivity.
    + unfold Φ, concrete_primop_sig, primop_result_ty.
      destruct (prim_op_type op) as [arg_b ret_b].
      unfold precise_ty, over_ty, under_ty.
      repeat split; cbn [erase_ty context_ty_lvars_at qual_vars qual_lvars
        lvars_at_depth context_ty_shape_ok];
        try reflexivity; unfold lvars_wf_at; set_solver.
    + reflexivity.
    + exact Hctx.
  - eapply res_models_and_intro_from_models.
    + apply primop_graph_over_denotation_gas. exact Hctx.
    + apply primop_graph_under_denotation_gas. exact Hctx.
Qed.

Lemma primop_result_denotation_arg_world
    op x (m : WfWorldT) :
  m ⊨ ty_denote (erase_ctx (CtxBind x (primop_arg_ty (Φ op))))
    ({0 ~> x} (primop_result_ty (Φ op)))
    (tprim op (vfvar x)) ->
  m ⊨ basic_world_formula (<[LVFree x := TBase (prim_arg_base (Φ op))]> ∅).
Proof.
  intros Hres.
  unfold ty_denote in Hres.
  pose proof (ty_denote_gas_guard
    (cty_depth ({0 ~> x} (primop_result_ty (Φ op))))
    (atom_env_to_lty_env (erase_ctx (CtxBind x (primop_arg_ty (Φ op)))))
    ({0 ~> x} (primop_result_ty (Φ op)))
    (tprim op (vfvar x)) m Hres) as Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [_ [Hworld _]].
  eapply basic_world_formula_subenv; [|exact Hworld].
  intros v T Hlook.
  destruct v as [k|a].
  - rewrite lookup_insert_ne in Hlook by discriminate.
    rewrite lookup_empty in Hlook. discriminate.
  - destruct (decide (a = x)) as [->|Hneq].
    2:{
      rewrite lookup_insert_ne in Hlook by congruence.
      rewrite lookup_empty in Hlook. discriminate.
    }
    change ((<[LVFree x := TBase (prim_arg_base (Φ op))]>
      (∅ : gmap logic_var ty)) !! LVFree x = Some T) in Hlook.
    rewrite lookup_insert in Hlook.
    destruct (decide (LVFree x = LVFree x)) as [_|Hbad];
      [|exfalso; apply Hbad; reflexivity].
    apply Some_inj in Hlook. symmetry in Hlook. subst T.
    unfold relevant_env, lty_env_restrict_lvars.
    eapply storeA_restrict_lookup_some_2.
    + rewrite atom_store_to_lvar_store_lookup_free.
      change (erase_ctx (CtxBind x (primop_arg_ty (Φ op))) !! x =
        Some (TBase (prim_arg_base (Φ op)))).
      cbn [erase_ctx].
      unfold primop_arg_ty, Φ, concrete_primop_sig.
      destruct (prim_op_type op) as [arg_b ret_b].
      change (({[x := TBase arg_b]} : gmap atom ty) !! x =
        Some (TBase arg_b)).
      apply map_lookup_singleton.
    + relevant_lvars_norm. better_set_solver.
Qed.

Lemma primop_graph_result_to_arg_ctx
    op x :
  ty_denote (erase_ctx (CtxBind x (primop_arg_ty (Φ op))))
    ({0 ~> x} (primop_result_ty (Φ op)))
    (tprim op (vfvar x)) ⊫
  ctx_denote (CtxBind x (primop_arg_ty (Φ op))).
Proof.
  intros m Hres.
  eapply ctx_denote_bind_from_arg_denotation
    with (Σ := <[x := erase_ty (primop_arg_ty (Φ op))]> ∅).
  - unfold Φ, concrete_primop_sig, primop_arg_ty.
    destruct (prim_op_type op) as [arg_b ret_b].
    unfold over_ty, qual_top.
    repeat split; cbn [erase_ty context_ty_lvars_at qual_vars qual_lvars
      lvars_at_depth context_ty_shape_ok].
    all: try reflexivity.
    all: unfold lvars_wf_at; set_solver.
  - apply map_lookup_insert.
  - rewrite primop_arg_ty_eq.
    cbn [erase_ty].
    replace (atom_env_to_lty_env
        (<[x := TBase (prim_arg_base (Φ op))]> (∅ : gmap atom ty)))
      with (<[LVFree x := TBase (prim_arg_base (Φ op))]>
        (∅ : gmap logic_var ty)) by better_store_solver.
    eapply over_top_ret_fvar_denotation_gas.
    exact (primop_result_denotation_arg_world op x m Hres).
Qed.

Lemma primop_arg_basic op :
  basic_context_ty ∅ (primop_arg_ty (Φ op)).
Proof.
  unfold Φ, concrete_primop_sig, primop_arg_ty.
  destruct (prim_op_type op) as [arg_b ret_b].
  unfold over_ty, qual_top.
  repeat split; cbn [erase_ty context_ty_lvars_at qual_vars qual_lvars
    lvars_at_depth context_ty_shape_ok].
  all: try reflexivity.
  all: unfold lvars_wf_at; set_solver.
Qed.

Lemma primop_result_wf op :
  wf_context_ty_at 1 ∅ (primop_result_ty (Φ op)).
Proof.
  unfold Φ, concrete_primop_sig, primop_result_ty.
  destruct (prim_op_type op) as [arg_b ret_b].
  unfold precise_ty, over_ty, under_ty.
  repeat split; cbn [erase_ty context_ty_lvars_at qual_vars qual_lvars
    lvars_at_depth context_ty_shape_ok].
  all: try reflexivity.
  all: unfold lvars_wf_at; set_solver.
Qed.

Lemma primop_erasure op :
  primop_erasure_ok op (Φ op).
Proof.
  unfold primop_erasure_ok, Φ, concrete_primop_sig.
  destruct (prim_op_type op); reflexivity.
Qed.

Theorem Φ_wf : wf_primop_ctx Φ.
Proof.
  intros op.
  constructor.
  - apply primop_erasure.
  - apply primop_arg_basic.
  - apply primop_result_wf.
  - unfold primop_semantic_ok.
    intros x.
    split.
    + apply primop_graph_result_denotation.
    + apply primop_graph_result_to_arg_ctx.
Qed.

Definition cons_arg1_ty : context_ty := precise_ty TNat qual_top.
Definition cons_arg2_ty : context_ty := precise_ty TList qual_top.
Definition cons_res_qual : type_qualifier :=
  tqual ({[LVBound 0; LVBound 1; LVBound 2]})
    (λ σ, ∃ x l l',
        denote_lvar_value (lso_store σ) (vbvar 2) = Some (vconst x) ∧
        denote_lvar_value (lso_store σ) (vbvar 1) = Some (vconst l) ∧
        denote_lvar_value (lso_store σ) (vbvar 0) = Some (vconst l') ∧ 
        binop_step op_cons x l l').
Definition cons_res_ty : context_ty := over_ty TList cons_res_qual.
