(** * Denotation.ConstDenote

    Constant and primitive-operation direct denotation support for
    Fundamental. *)

From Denotation Require Import Context TypeEquivCore
  TypeEquiv ConstDenoteBase.

Section ConstDenote.

Local Ltac solve_const_over_guard :=
  cbn [erase_ty];
  eapply res_models_and_intro_from_models;
  [apply context_ty_wf_formula_const_over_empty|];
  eapply res_models_and_intro_from_models;
  [apply basic_world_formula_empty|];
  eapply res_models_and_intro_from_models;
  [apply expr_basic_typing_formula_ret_const_empty|];
  apply expr_total_formula_ret_const.

Local Ltac solve_const_under_guard :=
  cbn [erase_ty];
  eapply res_models_and_intro_from_models;
  [apply context_ty_wf_formula_const_under_empty|];
  eapply res_models_and_intro_from_models;
  [apply basic_world_formula_empty|];
  eapply res_models_and_intro_from_models;
  [apply expr_basic_typing_formula_ret_const_empty|];
  apply expr_total_formula_ret_const.

Local Definition empty_lvset : lvset := ∅.

Local Lemma const_lc_lvars_shift_empty k :
  lc_lvars (lvars_shift_from k empty_lvset).
Proof.
  unfold lc_lvars, lvars_shift_from.
  intros v Hv.
  apply elem_of_map in Hv as [u [_ Hu]].
  set_solver.
Qed.

Local Lemma const_lvars_shift_empty k :
  lvars_shift_from k empty_lvset = empty_lvset.
Proof.
  apply set_eq. intros v. split.
  - unfold lvars_shift_from. intros Hv.
    apply elem_of_map in Hv as [u [_ Hu]].
    set_solver.
  - set_solver.
Qed.

Local Definition bound0_lvset : lvset := {[LVBound 0]}.

Local Definition const_bound_removed_qual c : lvset :=
  qual_vars (mk_q_eq (vbvar 0) (vconst c)) ∖ bound0_lvset.

Local Lemma const_expr_result_open_scoped c y (m : WfWorldT) :
  y ∈ world_dom (m : WorldT) ->
  formula_scoped_in_world m
    (expr_result_formula_at (lvars_shift_from 0 empty_lvset)
      (tret (vconst c)) (LVFree y)).
Proof.
  intros Hy.
  unfold formula_scoped_in_world.
  rewrite formula_fv_expr_result_formula_at.
  replace (lvars_fv (lvars_shift_from 0 empty_lvset)) with (∅ : aset).
  2:{ rewrite const_lvars_shift_empty. unfold empty_lvset.
      apply lvars_fv_empty. }
  replace (lvars_fv (tm_lvars (tret (vconst c)) ∪ {[LVFree y]}))
    with ({[y]} : aset).
  2:{
    apply set_eq. intros a.
    cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys].
    rewrite ?lvars_fv_union, ?lvars_fv_empty, ?lvars_fv_singleton_free.
    set_solver.
  }
  intros a Ha.
  apply elem_of_union in Ha as [Ha|Ha].
  - rewrite elem_of_empty in Ha. contradiction.
  - apply elem_of_singleton in Ha. subst. exact Hy.
Qed.

Local Lemma const_open_fib_over_swapped_scoped c y (m : WfWorldT) :
  y ∈ world_dom (m : WorldT) ->
  formula_scoped_in_world m
    (FFibVars
      (set_swap (LVBound 0) (LVFree y)
        (qual_vars (mk_q_eq (vbvar 0) (vconst c)) ∖ {[LVBound 0]}))
      (FOver (FAtom (mk_q_eq (vfvar y) (vconst c))))).
Proof.
  intros Hy.
  unfold formula_scoped_in_world.
  rewrite formula_fv_fibvars, formula_fv_over, formula_fv_atom.
  unfold qual_dom.
  replace (lvars_fv
      (set_swap (LVBound 0) (LVFree y)
        (qual_vars (mk_q_eq (vbvar 0) (vconst c)) ∖ {[LVBound 0]})))
    with (∅ : aset).
  2:{ symmetry. apply const_swapped_removed_vars_fv_empty. }
  replace (lvars_fv
      (qual_vars (mk_q_eq (vfvar y) (vconst c))))
    with ({[y]} : aset).
  2:{ symmetry. apply const_open_qual_vars_fv. }
  intros a Ha.
  apply elem_of_union in Ha as [Ha|Ha].
  - rewrite elem_of_empty in Ha. contradiction.
  - apply elem_of_singleton in Ha. subst. exact Hy.
Qed.

Local Lemma const_open_fib_under_swapped_scoped c y (m : WfWorldT) :
  y ∈ world_dom (m : WorldT) ->
  formula_scoped_in_world m
    (FFibVars
      (set_swap (LVBound 0) (LVFree y)
        (qual_vars (mk_q_eq (vbvar 0) (vconst c)) ∖ {[LVBound 0]}))
      (FUnder (FAtom (mk_q_eq (vfvar y) (vconst c))))).
Proof.
  intros Hy.
  unfold formula_scoped_in_world.
  rewrite formula_fv_fibvars, formula_fv_under, formula_fv_atom.
  unfold qual_dom.
  replace (lvars_fv
      (set_swap (LVBound 0) (LVFree y)
        (qual_vars (mk_q_eq (vbvar 0) (vconst c)) ∖ {[LVBound 0]})))
    with (∅ : aset).
  2:{ symmetry. apply const_swapped_removed_vars_fv_empty. }
  replace (lvars_fv
      (qual_vars (mk_q_eq (vfvar y) (vconst c))))
    with ({[y]} : aset).
  2:{ symmetry. apply const_open_qual_vars_fv. }
  intros a Ha.
  apply elem_of_union in Ha as [Ha|Ha].
  - rewrite elem_of_empty in Ha. contradiction.
  - apply elem_of_singleton in Ha. subst. exact Hy.
Qed.

Local Ltac const_scope_set :=
  intros z Hz; better_set_solver.

Local Ltac const_forall_scope_norm :=
  unfold formula_scoped_in_world;
	  rewrite ?formula_fv_atom, ?formula_fv_forall, ?formula_fv_impl, ?formula_fv_fibvars,
	    ?formula_fv_over, ?formula_fv_under, ?formula_fv_expr_result_formula,
	    ?formula_fv_expr_result_formula_at,
	    ?formula_fv_atom, ?formula_fv_basic_world_formula;
	  unfold basic_world_formula, expr_result_formula, expr_result_formula_at;
	  unfold FFiberAtom, qual_dom, qual_vars;
	  cbn [formula_lvars formula_lvars_at
	    tm_shift value_shift tm_lvars tm_lvars_at value_lvars_at
	    lvar_value_keys qual_lvars];
  rewrite ?const_lvars_shift_empty;
  repeat rewrite ?lvars_at_depth_union;
  rewrite ?lvars_at_depth_empty;
  rewrite ?lvars_at_depth_singleton_bound0_succ;
  rewrite ?lvars_fv_union, ?lvars_fv_empty, ?lvars_fv_singleton_bound,
    ?lvars_fv_singleton_free, ?dom_insert_L, ?dom_empty_L;
  rewrite ?const_qual_open_vars;
  rewrite ?const_qual_vars_bound;
  rewrite ?set_swap_empty;
  repeat match goal with
  | |- context[({[?v]} ∖ {[?v]} : lvset)] =>
      replace ({[v]} ∖ {[v]} : lvset) with (∅ : lvset) by set_solver
  | H : context[({[?v]} ∖ {[?v]} : lvset)] |- _ =>
      replace ({[v]} ∖ {[v]} : lvset) with (∅ : lvset) in H by set_solver
  end;
  rewrite ?lvars_fv_union, ?lvars_fv_empty, ?lvars_fv_singleton_bound,
    ?lvars_fv_singleton_free.

Local Ltac solve_const_forall_closed_scope :=
  const_forall_scope_norm;
  try replace (lvars_fv ({[LVBound 0]} ∪ ∅ : lvset)) with (∅ : aset)
    by (rewrite lvars_fv_union, lvars_fv_singleton_bound,
          lvars_fv_empty; set_solver);
  try replace (lvars_fv ({[LVBound 0]} : lvset)) with (∅ : aset)
    by apply lvars_fv_singleton_bound;
  try replace (lvars_fv ({[(#ₗ0)%ctx]} : lvset)) with (∅ : aset)
    by apply lvars_fv_singleton_bound;
  try rewrite (lvars_fv_singleton_bound 0);
  try unfold formula_scoped_in_world;
  try const_forall_scope_norm;
  first [const_scope_set | better_set_solver].

Local Ltac solve_const_forall_open_scope :=
  const_forall_scope_norm;
  lazymatch goal with
  | |- context[lvars_fv ({[LVFree ?y]} ∪ ∅ : lvset)] =>
      replace (lvars_fv ({[LVFree y]} ∪ ∅ : lvset)) with ({[y]} : aset)
        by (rewrite lvars_fv_union, lvars_fv_singleton_free,
              lvars_fv_empty; set_solver)
  | _ => idtac
  end;
  lazymatch goal with
  | |- context[lvars_fv ({[LVFree ?y]} : lvset)] =>
      replace (lvars_fv ({[LVFree y]} : lvset)) with ({[y]} : aset)
        by (symmetry; apply lvars_fv_singleton_free)
  | _ => idtac
  end;
  lazymatch goal with
  | |- context[lvars_fv (set_swap ?a ?b ∅)] =>
      replace (lvars_fv (set_swap a b ∅)) with (∅ : aset)
        by (rewrite set_swap_empty, lvars_fv_empty; reflexivity)
  | _ => idtac
  end;
  match goal with
  | Hdom : world_dom (?n : WorldT) = world_dom (?m : WorldT) ∪ extA_out ?F,
    HFout : ext_out ?F = {[?y]} |- _ =>
      unfold ext_out in HFout;
      rewrite Hdom, HFout;
      const_scope_set
  | |- _ => const_scope_set
  end.

Lemma const_over_denotation_gas gas (Σ : gmap atom ty) c (m : WfWorldT) :
  m ⊨ ty_denote_gas gas (atom_env_to_lty_env Σ)
    (CTOver (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
    (tret (vconst c)).
Proof.
  induction gas as [|gas IH]; cbn [ty_denote_gas].
  - rewrite relevant_env_const_over_atom_env_empty.
    eapply res_models_and_intro_from_models;
      [solve_const_over_guard | apply res_models_true].
  - rewrite relevant_env_const_over_atom_env_empty.
		    eapply res_models_and_intro_from_models; [solve_const_over_guard|].
		    eapply res_models_forall_intro.
		    + unfold formula_scoped_in_world.
		      intros z Hz.
		      unfold formula_fv, formula_lvars in Hz.
		      unfold expr_result_formula_at,
		        expr_result_qual, qual_vars, const_bound_removed_qual,
		        bound0_lvset, empty_lvset in Hz.
		      cbn [formula_lvars_at qual_lvars tm_shift value_shift
		        tm_lvars tm_lvars_at value_lvars_at lvar_value_keys] in Hz.
		      rewrite ?const_lvars_shift_empty in Hz.
		      rewrite ?const_qual_vars_bound in Hz.
		      repeat match type of Hz with
		      | context[∅ ∪ ?D] => rewrite (left_id ∅ union D) in Hz
		      | context[?D ∪ ∅] => rewrite (right_id ∅ union D) in Hz
		      | context[{[LVBound 0]} ∖ {[LVBound 0]}] =>
		          replace ({[LVBound 0]} ∖ {[LVBound 0]} : lvset)
		            with (∅ : lvset) in Hz by set_solver
		      end.
			      rewrite ?lvars_at_depth_union, ?lvars_at_depth_empty,
			        ?lvars_at_depth_singleton_bound0_succ in Hz.
			      cbn [qual_vars qual_lvars] in Hz.
			      replace (∅ ∪ {[LVBound 0]} : lvset)
			        with ({[LVBound 0]} : lvset) in Hz by set_solver.
			      rewrite ?lvars_at_depth_union, ?lvars_at_depth_empty,
			        ?lvars_at_depth_singleton_bound0_succ in Hz.
			      rewrite ?lvars_fv_union, ?lvars_fv_empty,
			        ?lvars_fv_singleton_bound in Hz.
			      set_solver.
    + exists (∅ : aset). intros y _ F HFin HFout my Hext.
		      pose proof (res_extend_by_dom m F my Hext) as Hdom.
		      rewrite !formula_open_impl.
          rewrite formula_open_expr_result_formula_at_shift0.
          2:{ apply const_lc_lvars_shift_empty. }
          2:{
            rewrite const_lvars_shift_empty.
            intros Hy. unfold empty_lvset in Hy.
            rewrite lvars_fv_empty in Hy.
            rewrite elem_of_empty in Hy. contradiction.
          }
          2:{ constructor. constructor. }
          2:{ cbn [fv_tm fv_value]. set_solver. }
          rewrite formula_open_fibvars, formula_open_over.
          rewrite formula_open_atom.
          rewrite const_qual_open_eq.
		      eapply res_models_impl_intro_scoped.
		      * eapply const_expr_result_open_scoped.
		        rewrite Hdom. unfold ext_out in HFout. rewrite HFout.
		        set_solver.
		      * eapply const_open_fib_over_swapped_scoped.
		        rewrite Hdom. unfold ext_out in HFout. rewrite HFout.
		        set_solver.
	      * intros Hexpr.
	        replace
	          (set_swap (LVBound 0) (LVFree y)
	             (qual_vars (mk_q_eq (vbvar 0) (vconst c)) ∖ {[LVBound 0]}))
	          with
	          (qual_vars (mk_q_eq (vfvar y) (vconst c)) ∖
	          {[LVFree y]}).
	        2:{
	          rewrite const_qual_vars_bound, const_qual_open_vars.
	          replace ({[LVBound 0]} ∖ {[LVBound 0]} : lvset)
	            with (∅ : lvset)
	            by set_solver.
	          replace ({[LVFree y]} ∖ {[LVFree y]} : lvset)
	            with (∅ : lvset)
	            by set_solver.
	          rewrite set_swap_empty.
	          reflexivity.
          }
          change (my ⊨ expr_result_formula (tret (vconst c)) (LVFree y)) in Hexpr.
          exact (const_fib_over_from_expr c y my Hexpr).
Qed.

Lemma const_under_denotation_gas gas (Σ : gmap atom ty) c (m : WfWorldT) :
  m ⊨ ty_denote_gas gas (atom_env_to_lty_env Σ)
    (CTUnder (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
    (tret (vconst c)).
Proof.
  induction gas as [|gas IH]; cbn [ty_denote_gas].
  - rewrite relevant_env_const_under_atom_env_empty.
    eapply res_models_and_intro_from_models;
      [solve_const_under_guard | apply res_models_true].
  - rewrite relevant_env_const_under_atom_env_empty.
		    eapply res_models_and_intro_from_models; [solve_const_under_guard|].
		    eapply res_models_forall_intro.
		    + unfold formula_scoped_in_world.
		      intros z Hz.
		      unfold formula_fv, formula_lvars in Hz.
		      unfold expr_result_formula_at,
		        expr_result_qual, qual_vars, const_bound_removed_qual,
		        bound0_lvset, empty_lvset in Hz.
		      cbn [formula_lvars_at qual_lvars tm_shift value_shift
		        tm_lvars tm_lvars_at value_lvars_at lvar_value_keys] in Hz.
		      rewrite ?const_lvars_shift_empty in Hz.
		      rewrite ?const_qual_vars_bound in Hz.
		      repeat match type of Hz with
		      | context[∅ ∪ ?D] => rewrite (left_id ∅ union D) in Hz
		      | context[?D ∪ ∅] => rewrite (right_id ∅ union D) in Hz
		      | context[{[LVBound 0]} ∖ {[LVBound 0]}] =>
		          replace ({[LVBound 0]} ∖ {[LVBound 0]} : lvset)
		            with (∅ : lvset) in Hz by set_solver
		      end.
			      rewrite ?lvars_at_depth_union, ?lvars_at_depth_empty,
			        ?lvars_at_depth_singleton_bound0_succ in Hz.
			      cbn [qual_vars qual_lvars] in Hz.
			      replace (∅ ∪ {[LVBound 0]} : lvset)
			        with ({[LVBound 0]} : lvset) in Hz by set_solver.
			      rewrite ?lvars_at_depth_union, ?lvars_at_depth_empty,
			        ?lvars_at_depth_singleton_bound0_succ in Hz.
			      rewrite ?lvars_fv_union, ?lvars_fv_empty,
			        ?lvars_fv_singleton_bound in Hz.
			      change (z ∈ (∅ : aset)) in Hz.
			      rewrite elem_of_empty in Hz. contradiction.
    + exists (∅ : aset). intros y _ F HFin HFout my Hext.
		      pose proof (res_extend_by_dom m F my Hext) as Hdom.
		      rewrite !formula_open_impl.
          rewrite formula_open_expr_result_formula_at_shift0.
          2:{ apply const_lc_lvars_shift_empty. }
          2:{
            rewrite const_lvars_shift_empty.
            intros Hy. unfold empty_lvset in Hy.
            rewrite lvars_fv_empty in Hy.
            rewrite elem_of_empty in Hy. contradiction.
          }
          2:{ constructor. constructor. }
          2:{ cbn [fv_tm fv_value]. set_solver. }
          rewrite formula_open_fibvars, formula_open_under.
          rewrite formula_open_atom.
          rewrite const_qual_open_eq.
		      eapply res_models_impl_intro_scoped.
		      * eapply const_expr_result_open_scoped.
		        rewrite Hdom. unfold ext_out in HFout. rewrite HFout.
		        set_solver.
		      * eapply const_open_fib_under_swapped_scoped.
		        rewrite Hdom. unfold ext_out in HFout. rewrite HFout.
		        set_solver.
	      * intros Hexpr.
	        replace
	          (set_swap (LVBound 0) (LVFree y)
	             (qual_vars (mk_q_eq (vbvar 0) (vconst c)) ∖ {[LVBound 0]}))
	          with
	          (qual_vars (mk_q_eq (vfvar y) (vconst c)) ∖
	          {[LVFree y]}).
	        2:{
	          rewrite const_qual_vars_bound, const_qual_open_vars.
	          replace ({[LVBound 0]} ∖ {[LVBound 0]} : lvset)
	            with (∅ : lvset)
	            by set_solver.
	          replace ({[LVFree y]} ∖ {[LVFree y]} : lvset)
	            with (∅ : lvset)
	            by set_solver.
	          rewrite set_swap_empty.
	          reflexivity.
          }
          change (my ⊨ expr_result_formula (tret (vconst c)) (LVFree y)) in Hexpr.
          exact (const_fib_under_from_expr c y my Hexpr).
Qed.

Lemma const_direct_denotation_gas_in_ctx
    gas (Σ : gmap atom ty) c (m : WfWorldT) :
  m ⊨ ctx_denote_under Σ CtxEmpty ->
  ctx_erasure_under Σ CtxEmpty ⊢ₑ
    tret (vconst c) ⋮ erase_ty (const_precise_ty c) ->
  m ⊨ ty_denote_gas gas
    (atom_env_to_lty_env (ctx_erasure_under Σ CtxEmpty))
    (const_precise_ty c) (tret (vconst c)).
Proof.
  intros _ _.
  unfold const_precise_ty, precise_ty, over_ty, under_ty.
  destruct gas as [|gas'].
  - unfold ctx_erasure_under. cbn [ctx_fv erase_ctx].
    replace (store_restrict Σ (∅ : aset) ∪ (∅ : gmap atom ty))
      with (∅ : gmap atom ty)
      by (rewrite storeA_restrict_empty_set; symmetry; apply map_union_empty).
    cbn [ty_denote_gas].
    rewrite relevant_env_const_precise_atom_env_empty.
    eapply res_models_and_intro_from_models;
      [ eapply res_models_and_intro_from_models;
        [ exact (context_ty_wf_formula_const_precise_empty c m)
        | eapply res_models_and_intro_from_models;
          [ exact (basic_world_formula_empty m)
          | eapply res_models_and_intro_from_models;
            [ exact (expr_basic_typing_formula_ret_const_empty c m)
            | exact (expr_total_formula_ret_const c m) ] ] ]
      | exact (res_models_true m) ].
  - unfold ctx_erasure_under. cbn [ctx_fv erase_ctx].
    replace (store_restrict Σ (∅ : aset) ∪ (∅ : gmap atom ty))
      with (∅ : gmap atom ty)
      by (rewrite storeA_restrict_empty_set; symmetry; apply map_union_empty).
	    cbn [ty_denote_gas].
	    rewrite relevant_env_const_precise_atom_env_empty.
    eapply res_models_and_intro_from_models;
      [ eapply res_models_and_intro_from_models;
        [ exact (context_ty_wf_formula_const_precise_empty c m)
        | eapply res_models_and_intro_from_models;
          [ exact (basic_world_formula_empty m)
          | eapply res_models_and_intro_from_models;
            [ exact (expr_basic_typing_formula_ret_const_empty c m)
            | exact (expr_total_formula_ret_const c m) ] ] ]
      | eapply res_models_and_intro_from_models;
        [ exact (const_over_denotation_gas gas' ∅ c m)
        | exact (const_under_denotation_gas gas' ∅ c m) ] ].
Qed.

Lemma appop_intro_denotation
    gas (Σ : gmap atom ty) op x τarg τres (m : WfWorldT) :
  cty_depth ({0 ~> x} τres) <= gas ->
  basic_context_ty ∅ τarg ->
  wf_context_ty_at 1 ∅ τres ->
  Σ !! x = Some (erase_ty τarg) ->
  Σ ⊢ₑ
    tprim op (vfvar x) ⋮ erase_ty ({0 ~> x} τres) ->
  (ctx_denote (CtxBind x τarg) ⊫
    ty_denote (erase_ctx (CtxBind x τarg)) ({0 ~> x} τres)
      (tprim op (vfvar x))) ->
  m ⊨ ty_denote_gas (cty_depth τarg) (atom_env_to_lty_env Σ)
    τarg (tret (vfvar x)) ->
  m ⊨ ty_denote_gas gas
    (atom_env_to_lty_env Σ) ({0 ~> x} τres) (tprim op (vfvar x)).
Proof.
  intros Hgas Hbasic_arg Hbasic_res Hlookup _ Hop Harg.
  rewrite ty_denote_gas_saturate by exact Hgas.
  pose proof (res_models_ty_denote_gas_env_agree_on
    (cty_depth τarg)
    (atom_env_to_lty_env Σ)
    (atom_env_to_lty_env (<[x := erase_ty τarg]> (∅ : gmap atom ty)))
    τarg (tret (vfvar x)) ({[LVFree x]}) m
    (relevant_lvars_basic_ret_fvar_subset x τarg Hbasic_arg)
    (atom_env_restrict_singleton_lookup
      Σ x (erase_ty τarg) Hlookup)
    Harg) as Harg_single.
  assert (Harg_bind : m ⊨ ctx_denote (CtxBind x τarg)).
  {
    eapply ctx_denote_bind_from_arg_denotation; eauto.
  }
  pose proof (Hop m Harg_bind) as Hres_single.
  unfold ty_denote in Hres_single.
  change (erase_ctx (CtxBind x τarg))
    with (<[x := erase_ty τarg]> (∅ : gmap atom ty)) in Hres_single.
  eapply res_models_ty_denote_gas_env_agree_on
    with (Σ1 := atom_env_to_lty_env
        (<[x := erase_ty τarg]> (∅ : gmap atom ty)))
      (X := {[LVFree x]});
    [ apply relevant_lvars_basic_open_tprim_fvar_subset;
      exact Hbasic_res
    | symmetry;
      apply atom_env_restrict_singleton_lookup;
      exact Hlookup
    | exact Hres_single ].
Qed.
End ConstDenote.
