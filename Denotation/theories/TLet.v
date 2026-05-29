(** * Denotation.TLet

    The key [tlet] introduction shape for the new denotation route. *)

From Denotation Require Import Notation.
From Denotation Require Import ContextTypeDenotationSaturate TLetSupport.

Section TLetDenotation.
Lemma tlet_intro_denotation_gas_zero
    (Σ : lty_env) (T1 : ty) (e1 e2 : tm)
    (m mx : WfWorldT) (Fx : FiberExtensionT) (x : atom)
    (τ : context_ty) :
  lty_env_closed Σ ->
  lty_env_to_atom_env Σ ⊢ₑ e1 ⋮ T1 ->
  lty_env_to_atom_env Σ ⊢ₑ (tlete e1 e2) ⋮ erase_ty τ ->
  expr_result_extension_witness e1 x Fx ->
  m ⊨ expr_total_formula e1 ->
  m ⊨ basic_world_formula (denot_relevant_env Σ τ (tlete e1 e2)) ->
  LVFree x ∉ dom Σ ->
  LVFree x ∉ context_ty_lvars τ ->
  res_extend_by m Fx mx ->
  mx ⊨ denot_ty_lvar_gas 0
    (<[LVFree x := T1]> Σ) τ (e2 ^^ x) ->
  m ⊨ denot_ty_lvar_gas 0 Σ τ (tlete e1 e2).
Proof.
  apply tlet_intro_denotation_gas_zero_support.
Qed.

Ltac pose_tlet_guard_from_mx_guard_at Σ T1 e1 e2 m mx Fx x τ
    HΣ He1 Hlet HFx Htotal Hbase_world HxΣ Hxτ Hext Hmx_guard :=
  let Hzero := fresh "Hm_zero" in
  pose proof (tlet_intro_denotation_gas_zero
    Σ T1 e1 e2 m mx Fx x τ
    HΣ He1 Hlet HFx Htotal Hbase_world HxΣ Hxτ Hext
    ltac:(solve_denot_ty_lvar_gas_zero_from_guard Hmx_guard)) as Hzero;
  pose proof (denot_ty_lvar_gas_guard_of_zero _ _ _ _ Hzero) as Hguard_m.

(** [tlet_intro_ih_sigma] is the reusable induction-hypothesis shape that the
    structural cases, especially [CTArrow], should consume.  It says: if [e1]
    is total and well-typed in the base lvar context, and evaluating [e1]
    produces a fresh result extension [Fx] from [m] to [mx], then denotation of
    the opened body in the extended context implies denotation of the whole
    [tlete] in the original context. *)
Lemma tlet_intro_denotation
    (gas : nat) (Σ : lty_env) (T1 : ty) (e1 e2 : tm)
    (m mx : WfWorldT) (Fx : FiberExtensionT) (x : atom)
    (τ : context_ty) :
  lty_env_closed Σ ->
  lty_env_to_atom_env Σ ⊢ₑ e1 ⋮ T1 ->
	  lty_env_to_atom_env Σ ⊢ₑ (tlete e1 e2) ⋮ erase_ty τ ->
		  expr_result_extension_witness e1 x Fx ->
		  m ⊨ expr_total_formula e1 ->
		  m ⊨ basic_world_formula (denot_relevant_env Σ τ (tlete e1 e2)) ->
		  LVFree x ∉ dom Σ ∪ context_ty_lvars τ ->
		  res_extend_by m Fx mx ->
	  mx ⊨ denot_ty_lvar_gas gas
	    (<[LVFree x := T1]> Σ) τ (e2 ^^ x) ->
  m ⊨ denot_ty_lvar_gas gas Σ τ (tlete e1 e2).
Proof.
	  revert Σ T1 e1 e2 m mx Fx x τ.
	  induction gas as [|gas IH];
	    intros Σ T1 e1 e2 m mx Fx x τ
	      HΣ He1 Hlet HFx Htotal Hbase_world Hfresh Hext Hmx.
	  - cbn [denot_ty_lvar_gas] in Hmx |- *.
		    (* gas = 0: only the inlined guard remains.  This should follow from
		       [He1], [Htotal], [HΣ], [Hfresh], and the guard already present in
		       [Hmx]. *)
				    assert (HxΣ : LVFree x ∉ dom Σ) by tlet_support_solver.
				    assert (Hxτ : LVFree x ∉ context_ty_lvars τ) by tlet_support_solver.
				    eapply tlet_intro_denotation_gas_zero; eauto.
  - destruct τ as [b φ | b φ | τ1 τ2 | τ1 τ2 | τ1 τ2 | τx τr | τx τr];
      cbn [denot_ty_lvar_gas] in Hmx |- *.
	    + clear IH.
	      normalize_models_ands_in Hmx; normalize_models_ands_goal.
		      destruct Hmx as [Hmx_guard Hmx_over_body].
		      assert (HxΣ : LVFree x ∉ dom Σ) by tlet_support_solver.
		      assert (Hxτ : LVFree x ∉ context_ty_lvars (CTOver b φ))
		        by tlet_support_solver.
		      pose_tlet_guard_from_mx_guard_at Σ T1 e1 e2 m mx Fx x (CTOver b φ) HΣ He1 Hlet HFx Htotal Hbase_world HxΣ Hxτ Hext Hmx_guard.
		      assert (Hbody_scope_m :
		        formula_scoped_in_world m
		          (FForall
		            (FImpl
		              (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
		              (FImpl
		                (expr_result_formula
		                  (tm_shift 0 (tlete e1 e2)) (LVBound 0))
		                (FFibVars (qual_vars φ ∖ {[LVBound 0]})
		                  (FOver (type_qualifier_formula φ))))))).
		      { solve_denot_ty_lvar_body_scope_from_guard_at
		          (S gas) Σ (CTOver b φ) (tlete e1 e2) Hguard_m. }
			      split.
			      * solve_denot_guard_goal Hguard_m.
				      * refine (res_models_forall_ext_transport
				          m mx Fx _ _ Hbody_scope_m Hext _ Hmx_over_body).
				        exists (lvars_fv (dom Σ) ∪ fv_tm e1 ∪ fv_tm e2 ∪
				           qual_dom φ ∪ {[x]}).
				           intros y Hy my myx Hle Hdom_my HmyFx Hmyx_body.
			           normalize_formula_open_syntax.
		           pose_formula_scoped_forall_open_from_dom
		             m my y Hbody_scope_m Hle Hdom_my.
		           normalize_formula_open_syntax.
			           eapply res_models_impl_intro.
			           { exact Hopened_scope_my. }
			           intro Hmy_world.
			           use_models_impl Hmyx_body Hbody_after_outer.
		           {
		             eapply res_models_extend_mono; [exact HmyFx | exact Hmy_world].
		           }
		           eapply res_models_impl_intro.
		           { eapply formula_scoped_impl_r. exact Hopened_scope_my. }
		           intro Hmy_result.
	           use_models_impl Hbody_after_outer Hbody_after_inner.
	           {
	             eapply expr_result_formula_tlete_to_body_ext in Hmy_result; eauto.
	             - eapply typing_tm_lc; eauto.
	             - tlet_support_solver.
	             - assert (Hfv_tlet :
	                 fv_tm (tlete e1 e2) ⊆ lvars_fv (dom Σ)).
	               { eapply basic_typing_lty_env_to_atom_env_fv_subset; eauto. }
		               intros Hxe2. apply Hfresh. apply elem_of_union_l.
	               apply lvars_fv_elem. apply Hfv_tlet.
	               cbn [fv_tm]. set_solver.
	             - assert (Hmy_base_world :
	                 my ⊨ basic_world_formula
	                   (denot_relevant_env Σ (CTOver b φ) (tlete e1 e2))).
	               {
	                 eapply res_models_kripke; [exact Hle | exact Hbase_world].
	               }
	               eapply (basic_world_formula_wfworld_closed_on_atoms
	                 (denot_relevant_env Σ (CTOver b φ) (tlete e1 e2))).
	               + unfold denot_relevant_env, lty_env_restrict_lvars,
	                   denot_relevant_lvars.
	                 change (lvars_of_atoms (fv_tm (tlete e1 e2)) ⊆
	                   dom (storeA_restrict (Σ : gmap logic_var ty)
	                     (context_ty_lvars (CTOver b φ) ∪
	                      tm_lvars (tlete e1 e2)))).
	                 rewrite storeA_restrict_dom.
	                 intros v Hv.
	                 unfold lvars_of_atoms in Hv.
	                 apply elem_of_map in Hv as [a [-> Ha]].
	                 apply elem_of_intersection. split.
	                 * apply lvars_fv_elem.
	                   pose proof (basic_typing_lty_env_to_atom_env_fv_subset
	                     Σ (tlete e1 e2) (erase_ty (CTOver b φ)) Hlet) as Hfv_tlet.
	                   apply Hfv_tlet. exact Ha.
		                 * apply elem_of_union_r.
		                   apply lvars_fv_elem. rewrite tm_lvars_fv. exact Ha.
	               + exact Hmy_base_world.
	           }
		           eapply res_models_fuel_projection with (m := myx); eauto.
		           { symmetry. eapply res_restrict_le_eq.
		             - eapply res_extend_by_le; eauto.
	             - destruct HFx as [_ [_ HoutFx] _].
	               eapply formula_fv_in_base_dom_of_extend_scoped;
	                 [exact HmyFx | exact HoutFx | exact Hbody_after_inner |].
		               eapply tlet_over_fib_formula_fresh_x.
		               + intros Hbad. apply Hfresh. apply elem_of_union_r. exact Hbad.
		               + tlet_support_solver. }
		    + clear IH.
		      normalize_models_ands_in Hmx; normalize_models_ands_goal.
		      destruct Hmx as [Hmx_guard Hmx_under_body].
		      assert (HxΣ : LVFree x ∉ dom Σ) by tlet_support_solver.
		      assert (Hxτ : LVFree x ∉ context_ty_lvars (CTUnder b φ))
		        by tlet_support_solver.
		      pose_tlet_guard_from_mx_guard_at Σ T1 e1 e2 m mx Fx x (CTUnder b φ) HΣ He1 Hlet HFx Htotal Hbase_world HxΣ Hxτ Hext Hmx_guard.
		      assert (Hbody_scope_m :
		        formula_scoped_in_world m
		          (FForall
		            (FImpl
		              (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
		              (FImpl
		                (expr_result_formula
		                  (tm_shift 0 (tlete e1 e2)) (LVBound 0))
		                (FFibVars (qual_vars φ ∖ {[LVBound 0]})
		                  (FUnder (type_qualifier_formula φ))))))).
		      { solve_denot_ty_lvar_body_scope_from_guard_at
		          (S gas) Σ (CTUnder b φ) (tlete e1 e2) Hguard_m. }
		      split.
		      * solve_denot_guard_goal Hguard_m.
		      * refine (res_models_forall_ext_transport
		          m mx Fx _ _ Hbody_scope_m Hext _ Hmx_under_body).
		        exists (lvars_fv (dom Σ) ∪ fv_tm e1 ∪ fv_tm e2 ∪
		           qual_dom φ ∪ {[x]}).
		        intros y Hy my myx Hle Hdom_my HmyFx Hmyx_body.
		        normalize_formula_open_syntax.
		        pose_formula_scoped_forall_open_from_dom
		          m my y Hbody_scope_m Hle Hdom_my.
		        normalize_formula_open_syntax.
		        eapply res_models_impl_intro.
		        { exact Hopened_scope_my. }
		        intro Hmy_world.
		        use_models_impl Hmyx_body Hbody_after_outer.
		        {
		          eapply res_models_extend_mono; [exact HmyFx | exact Hmy_world].
		        }
		        eapply res_models_impl_intro.
		        { eapply formula_scoped_impl_r. exact Hopened_scope_my. }
		        intro Hmy_result.
		        use_models_impl Hbody_after_outer Hbody_after_inner.
		        {
		          eapply expr_result_formula_tlete_to_body_ext in Hmy_result; eauto.
		          - eapply typing_tm_lc; eauto.
		          - tlet_support_solver.
		          - assert (Hfv_tlet :
		              fv_tm (tlete e1 e2) ⊆ lvars_fv (dom Σ)).
		            { eapply basic_typing_lty_env_to_atom_env_fv_subset; eauto. }
		            intros Hxe2. apply Hfresh. apply elem_of_union_l.
		            apply lvars_fv_elem. apply Hfv_tlet.
		            cbn [fv_tm]. set_solver.
		          - assert (Hmy_base_world :
		              my ⊨ basic_world_formula
		                (denot_relevant_env Σ (CTUnder b φ) (tlete e1 e2))).
		            {
		              eapply res_models_kripke; [exact Hle | exact Hbase_world].
		            }
		            eapply (basic_world_formula_wfworld_closed_on_atoms
		              (denot_relevant_env Σ (CTUnder b φ) (tlete e1 e2))).
		            + unfold denot_relevant_env, lty_env_restrict_lvars,
		                denot_relevant_lvars.
		              change (lvars_of_atoms (fv_tm (tlete e1 e2)) ⊆
		                dom (storeA_restrict (Σ : gmap logic_var ty)
		                  (context_ty_lvars (CTUnder b φ) ∪
		                   tm_lvars (tlete e1 e2)))).
		              rewrite storeA_restrict_dom.
		              intros v Hv.
		              unfold lvars_of_atoms in Hv.
		              apply elem_of_map in Hv as [a [-> Ha]].
		              apply elem_of_intersection. split.
		              * apply lvars_fv_elem.
		                pose proof (basic_typing_lty_env_to_atom_env_fv_subset
		                  Σ (tlete e1 e2) (erase_ty (CTUnder b φ)) Hlet) as Hfv_tlet.
		                apply Hfv_tlet. exact Ha.
		              * apply elem_of_union_r.
		                apply lvars_fv_elem. rewrite tm_lvars_fv. exact Ha.
		            + exact Hmy_base_world.
		        }
		        eapply res_models_fuel_projection with (m := myx); eauto.
		        { symmetry. eapply res_restrict_le_eq.
		          - eapply res_extend_by_le; eauto.
		          - destruct HFx as [_ [_ HoutFx] _].
		            eapply formula_fv_in_base_dom_of_extend_scoped;
		              [exact HmyFx | exact HoutFx | exact Hbody_after_inner |].
		            eapply tlet_under_fib_formula_fresh_x.
		            + intros Hbad. apply Hfresh. apply elem_of_union_r. exact Hbad.
		            + tlet_support_solver. }
    + normalize_models_ands_in Hmx; normalize_models_ands_goal.
      destruct Hmx as [Hmx_guard Hmx_inter].
      assert (HxΣ : LVFree x ∉ dom Σ) by tlet_support_solver.
      assert (Hxτ : LVFree x ∉ context_ty_lvars (CTInter τ1 τ2))
        by tlet_support_solver.
      pose_tlet_guard_from_mx_guard_at Σ T1 e1 e2 m mx Fx x (CTInter τ1 τ2) HΣ He1 Hlet HFx Htotal Hbase_world HxΣ Hxτ Hext Hmx_guard.
      split.
      * solve_denot_guard_goal Hguard_m.
      * destruct Hmx_inter as [Hmx1 Hmx2].
        assert (Hm1 : m ⊨ denot_ty_lvar_gas gas Σ τ1 (tlete e1 e2)).
        {
          eapply IH with
            (Σ := Σ) (T1 := T1) (e1 := e1) (e2 := e2)
            (m := m) (mx := mx) (Fx := Fx) (x := x) (τ := τ1).
          - exact HΣ.
          - exact He1.
          - cbn [erase_ty] in Hlet. exact Hlet.
          - exact HFx.
          - exact Htotal.
          - eapply basic_world_formula_denot_relevant_mono_context;
              [|exact Hbase_world].
            cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
          - cbn [context_ty_lvars context_ty_lvars_at] in Hfresh |- *.
            set_solver.
          - exact Hext.
          - exact Hmx1.
        }
        assert (Hm2 : m ⊨ denot_ty_lvar_gas gas Σ τ2 (tlete e1 e2)).
        {
          eapply IH with
            (Σ := Σ) (T1 := T1) (e1 := e1) (e2 := e2)
            (m := m) (mx := mx) (Fx := Fx) (x := x) (τ := τ2).
          - exact HΣ.
          - exact He1.
          - assert (Herase : erase_ty τ1 = erase_ty τ2).
            {
              destruct Hmx_guard as [Hwf _].
              apply context_ty_wf_formula_basic_lvars in Hwf as [_ Hshape].
              cbn [context_ty_shape_ok] in Hshape. tauto.
            }
            cbn [erase_ty] in Hlet.
            rewrite <- Herase. exact Hlet.
          - exact HFx.
          - exact Htotal.
          - eapply basic_world_formula_denot_relevant_mono_context;
              [|exact Hbase_world].
            cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
          - cbn [context_ty_lvars context_ty_lvars_at] in Hfresh |- *.
            set_solver.
          - exact Hext.
          - exact Hmx2.
        }
        split; [exact Hm1 | exact Hm2].
    + normalize_models_ands_in Hmx; normalize_models_ands_goal.
      destruct Hmx as [Hmx_guard Hmx_union].
      assert (HxΣ : LVFree x ∉ dom Σ) by tlet_support_solver.
      assert (Hxτ : LVFree x ∉ context_ty_lvars (CTUnion τ1 τ2))
        by tlet_support_solver.
      pose_tlet_guard_from_mx_guard_at Σ T1 e1 e2 m mx Fx x (CTUnion τ1 τ2) HΣ He1 Hlet HFx Htotal Hbase_world HxΣ Hxτ Hext Hmx_guard.
      split.
      * solve_denot_guard_goal Hguard_m.
      * eapply (res_models_or_transport_between_worlds
          mx m
          (denot_ty_lvar_gas gas (<[LVFree x := T1]> Σ) τ1 (e2 ^^ x))
          (denot_ty_lvar_gas gas (<[LVFree x := T1]> Σ) τ2 (e2 ^^ x))
          (denot_ty_lvar_gas gas Σ τ1 (tlete e1 e2))
          (denot_ty_lvar_gas gas Σ τ2 (tlete e1 e2))).
        -- eapply formula_fv_denot_ty_lvar_gas_scope_from_guard;
             [|exact Hguard_m].
           cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
        -- eapply formula_fv_denot_ty_lvar_gas_scope_from_guard;
             [|exact Hguard_m].
           cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
        -- intros Hmx1.
           eapply IH with
             (Σ := Σ) (T1 := T1) (e1 := e1) (e2 := e2)
             (m := m) (mx := mx) (Fx := Fx) (x := x) (τ := τ1).
           ++ exact HΣ.
           ++ exact He1.
           ++ cbn [erase_ty] in Hlet. exact Hlet.
           ++ exact HFx.
           ++ exact Htotal.
           ++ eapply basic_world_formula_denot_relevant_mono_context;
                [|exact Hbase_world].
              cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
           ++ cbn [context_ty_lvars context_ty_lvars_at] in Hfresh |- *.
              set_solver.
           ++ exact Hext.
           ++ exact Hmx1.
        -- intros Hmx2.
           eapply IH with
             (Σ := Σ) (T1 := T1) (e1 := e1) (e2 := e2)
             (m := m) (mx := mx) (Fx := Fx) (x := x) (τ := τ2).
           ++ exact HΣ.
           ++ exact He1.
           ++ assert (Herase : erase_ty τ1 = erase_ty τ2).
              {
                destruct Hmx_guard as [Hwf _].
                apply context_ty_wf_formula_basic_lvars in Hwf as [_ Hshape].
                cbn [context_ty_shape_ok] in Hshape. tauto.
              }
              cbn [erase_ty] in Hlet.
              rewrite <- Herase. exact Hlet.
           ++ exact HFx.
           ++ exact Htotal.
           ++ eapply basic_world_formula_denot_relevant_mono_context;
                [|exact Hbase_world].
              cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
           ++ cbn [context_ty_lvars context_ty_lvars_at] in Hfresh |- *.
              set_solver.
           ++ exact Hext.
           ++ exact Hmx2.
        -- exact Hmx_union.
	    + normalize_models_ands_in Hmx; normalize_models_ands_goal.
	      destruct Hmx as [Hmx_guard Hmx_sum].
	      assert (HxΣ : LVFree x ∉ dom Σ) by tlet_support_solver.
	      assert (Hxτ : LVFree x ∉ context_ty_lvars (CTSum τ1 τ2))
	        by tlet_support_solver.
	      pose_tlet_guard_from_mx_guard_at Σ T1 e1 e2 m mx Fx x (CTSum τ1 τ2) HΣ He1 Hlet HFx Htotal Hbase_world HxΣ Hxτ Hext Hmx_guard.
	      split.
	      * solve_denot_guard_goal Hguard_m.
	      * eapply (res_models_plus_extend_pullback_agree_on
	          m Fx mx
	          (denot_ty_lvar_gas gas (<[LVFree x := T1]> Σ)
	            τ1 (e2 ^^ x))
	          (denot_ty_lvar_gas gas (<[LVFree x := T1]> Σ)
	            τ2 (e2 ^^ x))
	          (denot_ty_lvar_gas gas Σ τ1 (tlete e1 e2))
	          (denot_ty_lvar_gas gas Σ τ2 (tlete e1 e2))).
	        -- exact Hext.
	        -- exact Hmx_sum.
	        -- eapply expr_result_extension_functional_on; eauto.
	        -- intros m1 n1 Hdom_m1 Hsub_m1 Hext1 Hn1.
	           eapply IH with
	             (Σ := Σ) (T1 := T1) (e1 := e1) (e2 := e2)
	             (m := m1) (mx := n1) (Fx := Fx) (x := x)
	             (τ := τ1).
	           ++ exact HΣ.
	           ++ exact He1.
		           ++ cbn [erase_ty] in Hlet. exact Hlet.
		           ++ exact HFx.
		           ++ eapply expr_total_formula_res_subset; [exact Hsub_m1 | exact Htotal].
		           ++ eapply basic_world_formula_res_subset; [exact Hsub_m1 |].
		              eapply basic_world_formula_denot_relevant_mono_context;
		                [|exact Hbase_world].
		              cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
	           ++ cbn [context_ty_lvars context_ty_lvars_at] in Hfresh |- *.
	              set_solver.
	           ++ exact Hext1.
	           ++ exact Hn1.
	        -- intros m2 n2 Hdom_m2 Hsub_m2 Hext2 Hn2.
	           eapply IH with
	             (Σ := Σ) (T1 := T1) (e1 := e1) (e2 := e2)
	             (m := m2) (mx := n2) (Fx := Fx) (x := x)
	             (τ := τ2).
	           ++ exact HΣ.
	           ++ exact He1.
	           ++ assert (Herase : erase_ty τ1 = erase_ty τ2).
	              {
	                destruct Hmx_guard as [Hwf _].
	                apply context_ty_wf_formula_basic_lvars in Hwf as [_ Hshape].
	                cbn [context_ty_shape_ok] in Hshape. tauto.
	              }
	              cbn [erase_ty] in Hlet.
		              rewrite <- Herase. exact Hlet.
		           ++ exact HFx.
		           ++ eapply expr_total_formula_res_subset; [exact Hsub_m2 | exact Htotal].
		           ++ eapply basic_world_formula_res_subset; [exact Hsub_m2 |].
		              eapply basic_world_formula_denot_relevant_mono_context;
		                [|exact Hbase_world].
		              cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
	           ++ cbn [context_ty_lvars context_ty_lvars_at] in Hfresh |- *.
	              set_solver.
	           ++ exact Hext2.
	           ++ exact Hn2.
	    + normalize_models_ands_in Hmx; normalize_models_ands_goal.
	      destruct Hmx as [Hmx_guard Hmx_arrow_body].
	      pose proof Hmx_guard as Hmx_guard_parts.
	      destruct Hmx_guard_parts as
	        [Hmx_wf [Hmx_world [Hmx_basic_typing Hmx_total]]].
	      assert (HxΣ : LVFree x ∉ dom Σ) by tlet_support_solver.
	      assert (Hxτ : LVFree x ∉ context_ty_lvars (CTArrow τx τr))
	        by tlet_support_solver.
	      pose_tlet_guard_from_mx_guard_at Σ T1 e1 e2 m mx Fx x (CTArrow τx τr) HΣ He1 Hlet HFx Htotal Hbase_world HxΣ Hxτ Hext Hmx_guard.
	      assert (Hbody_scope_m :
	        formula_scoped_in_world m
	          (FForall
	            (FImpl
	              (basic_world_formula
	                (<[LVBound 0 := erase_ty τx]> ∅))
	              (FImpl
	                (denot_ty_lvar_gas gas
	                  (typed_lty_env_bind
	                    (denot_relevant_env Σ (CTArrow τx τr)
	                      (tlete e1 e2))
	                    (erase_ty τx))
	                  (cty_shift 0 τx) (tret (vbvar 0)))
	                (denot_ty_lvar_gas gas
	                  (typed_lty_env_bind
	                    (denot_relevant_env Σ (CTArrow τx τr)
	                      (tlete e1 e2))
	                    (erase_ty τx))
	                  τr
	                  (tapp_tm (tm_shift 0 (tlete e1 e2))
	                    (vbvar 0))))))).
	      { solve_denot_ty_lvar_body_scope_from_guard_at
	          (S gas) Σ (CTArrow τx τr) (tlete e1 e2) Hguard_m. }
	      split.
	      * solve_denot_guard_goal Hguard_m.
	      * refine (res_models_forall_ext_transport
	          m mx Fx _ _ Hbody_scope_m Hext _ Hmx_arrow_body).
	        exists (lvars_fv (dom Σ) ∪ fv_tm e1 ∪ fv_tm e2 ∪
	             fv_cty τx ∪ fv_cty τr ∪ {[x]}).
	        intros y Hy my myx Hle Hdom_my HmyFx Hmyx_body.
	        normalize_formula_open_syntax.
	        pose_formula_scoped_forall_open_from_dom
	          m my y Hbody_scope_m Hle Hdom_my.
	        normalize_formula_open_syntax.
	        eapply res_models_impl_intro.
	        { exact Hopened_scope_my. }
	        intro Hmy_world.
	        use_models_impl Hmyx_body Hbody_after_outer.
	        { eapply res_models_extend_mono; [exact HmyFx | exact Hmy_world]. }
	        eapply res_models_impl_intro.
	        { eapply formula_scoped_impl_r. exact Hopened_scope_my. }
	        intro Hmy_arg.
	        assert (Hy_source_rel : LVFree y ∉ dom
	          (denot_relevant_env (<[LVFree x := T1]> Σ)
	             (CTArrow τx τr) (e2 ^^ x))).
	        {
	          intros HyD.
	          assert (Hyfv : y ∈ lvars_fv (dom
	            (denot_relevant_env (<[LVFree x := T1]> Σ)
	               (CTArrow τx τr) (e2 ^^ x)))).
	          { apply lvars_fv_elem. exact HyD. }
	          pose proof (denot_relevant_env_fv_subset
	            (<[LVFree x := T1]> Σ) (CTArrow τx τr) (e2 ^^ x)) as Hrel.
	          pose proof (open_fv_tm e2 (vfvar x) 0) as Hopen.
	          cbn [fv_cty fv_value] in Hrel, Hopen.
	          assert (Hy_rel :
	            y ∈ fv_cty (CTArrow τx τr) ∪ fv_tm (e2 ^^ x)).
	          { apply Hrel. exact Hyfv. }
	          unfold fv_cty, context_ty_lvars in Hy_rel.
	          cbn [context_ty_lvars_at] in Hy_rel.
	          rewrite lvars_fv_union, !context_ty_lvars_fv_at in Hy_rel.
	          exfalso. apply Hy.
	          clear Hrel Hyfv HyD.
	          apply elem_of_union in Hy_rel as [Hycty|Hye2x].
	          - apply elem_of_union in Hycty as [Hyτx|Hyτr].
	            + clear - Hyτx. set_solver.
	            + clear - Hyτr. set_solver.
	          - pose proof (Hopen y Hye2x) as Hye2.
	            cbn [fv_value] in Hye2.
	            clear - Hye2. set_solver.
	        }
	        assert (Hclosed_source_rel : lty_env_closed
	          (denot_relevant_env (<[LVFree x := T1]> Σ)
	             (CTArrow τx τr) (e2 ^^ x))).
	        { apply denot_relevant_env_closed. apply lty_env_closed_insert_free. exact HΣ. }
	        transport_open_denot_in Hbody_after_outer.
	        assert (Hy_target_rel : LVFree y ∉ dom
	          (denot_relevant_env Σ (CTArrow τx τr) (tlete e1 e2))).
	        {
	          intros HyD.
	          assert (Hyfv : y ∈ lvars_fv (dom
	            (denot_relevant_env Σ (CTArrow τx τr) (tlete e1 e2)))).
	          { apply lvars_fv_elem. exact HyD. }
	          pose proof (denot_relevant_env_fv_subset
	            Σ (CTArrow τx τr) (tlete e1 e2)) as Hrel.
	          cbn [fv_cty fv_tm] in Hrel.
	          assert (Hy_rel :
	            y ∈ fv_cty (CTArrow τx τr) ∪ fv_tm (tlete e1 e2)).
	          { apply Hrel. exact Hyfv. }
	          unfold fv_cty, context_ty_lvars in Hy_rel.
	          cbn [context_ty_lvars_at fv_tm] in Hy_rel.
	          rewrite lvars_fv_union, !context_ty_lvars_fv_at in Hy_rel.
	          exfalso. apply Hy.
	          clear Hrel Hyfv HyD.
	          clear - Hy_rel. set_solver.
	        }
	        assert (Hclosed_target_rel : lty_env_closed
	          (denot_relevant_env Σ (CTArrow τx τr) (tlete e1 e2))).
	        { apply denot_relevant_env_closed. exact HΣ. }
	        use_models_impl Hbody_after_outer Hbody_after_inner.
	        {
	          assert (Hxy0 : x <> y) by tlet_support_solver.
	          assert (Hxτx : LVFree x ∉ context_ty_lvars τx).
	          {
	            cbn [context_ty_lvars context_ty_lvars_at] in Hfresh.
	            set_solver.
	          }
	          assert (Hmy_arg_source :
	            my ⊨ formula_open 0 y
	              (denot_ty_lvar_gas gas
	                (typed_lty_env_bind
	                  (denot_relevant_env (<[LVFree x := T1]> Σ)
	                    (CTArrow τx τr) (e2 ^^ x))
	                  (erase_ty τx))
	                (cty_shift 0 τx) (tret (vbvar 0)))).
	          {
	            pose proof (res_models_open_denot_ty_lvar_gas_to_open
	              y gas
	              (denot_relevant_env Σ (CTArrow τx τr) (tlete e1 e2))
	              (erase_ty τx) (cty_shift 0 τx) (tret (vbvar 0)) my
	              Hy_target_rel Hclosed_target_rel
	              ltac:(cbn [fv_tm fv_value]; set_solver)
	              ltac:(rewrite cty_shift_fv; tlet_support_solver)
	              Hmy_arg) as Harg_open.
	            eapply res_models_open_denot_ty_lvar_gas_from_open;
	              [ exact Hy_source_rel
	              | exact Hclosed_source_rel
	              | cbn [fv_tm fv_value]; set_solver
	              | rewrite cty_shift_fv; tlet_support_solver
	              | ].
	            eapply res_models_denot_ty_lvar_gas_env_agree_on
	              with (X := denot_relevant_lvars
	                (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y))).
	            - reflexivity.
	            - symmetry.
	              apply tlet_arrow_arg_relevant_env_agree; assumption.
	            - exact Harg_open.
	          }
	          eapply res_models_extend_mono; [exact HmyFx | exact Hmy_arg_source].
	        }
	        assert (Hy_e2x : y ∉ fv_tm (e2 ^^ x)).
	        {
	          pose proof (open_fv_tm e2 (vfvar x) 0 y) as Hopen.
	          cbn [fv_value] in Hopen.
	          intros Hybad.
	          pose proof (Hopen Hybad) as Hycases.
	          clear Hopen Hybad.
	          set_solver.
	        }
	        pose proof (res_models_open_denot_ty_lvar_gas_to_open
	          y gas
	          (denot_relevant_env (<[LVFree x := T1]> Σ)
	            (CTArrow τx τr) (e2 ^^ x))
	          (erase_ty τx) τr
	          (tapp_tm (tm_shift 0 (e2 ^^ x)) (vbvar 0)) myx
	          Hy_source_rel Hclosed_source_rel
	          ltac:(rewrite fv_tapp_tm, tm_shift_fv; cbn [fv_value]; set_solver)
	          ltac:(set_solver)
	          Hbody_after_inner) as Hbody_after_inner_open.
	        clear Hbody_after_inner.
	        rename Hbody_after_inner_open into Hbody_after_inner.
	        cbn [open_tm open_value value_shift] in Hbody_after_inner.
	        assert (Hret_body_open :
	          myx ⊨ denot_ty_lvar_gas gas
	            (<[LVFree x := T1]>
	              (<[LVFree y := erase_ty τx]> Σ))
	            (cty_open 0 y τr)
	            ((tapp_tm e2 (vfvar y)) ^^ x)).
	        {
	          assert (Hbody_full :
	            myx ⊨ denot_ty_lvar_gas gas
	              (<[LVFree y := erase_ty τx]>
	                (<[LVFree x := T1]> Σ))
	              (cty_open 0 y τr)
	              (tapp_tm (e2 ^^ x) (vfvar y))).
	          {
	            eapply res_models_denot_ty_lvar_gas_env_agree_on
	              with (X := denot_relevant_lvars (cty_open 0 y τr)
	                (tapp_tm (e2 ^^ x) (vfvar y))).
	            - reflexivity.
	            - apply arrow_body_relevant_env_agree_from_basic_context_ty.
	              + apply lty_env_closed_insert_free. exact HΣ.
	              + change (LVFree y ∉ dom
	                  ((<[LVFree x := T1]> (Σ : gmap logic_var ty))
	                    : gmap logic_var ty)).
	                rewrite dom_insert_L. tlet_support_solver.
	              + pose proof (context_ty_wf_formula_basic_lvars _ _ _ Hmx_wf)
	                  as Hbasic_src_rel.
	                eapply basic_context_ty_lvars_mono;
	                  [|exact Hbasic_src_rel].
	                intros v Hv.
	                change (v ∈ dom
	                  (denot_relevant_env (<[LVFree x := T1]> Σ)
	                    (CTArrow τx τr) (e2 ^^ x) : lty_env)) in Hv.
			                change (v ∈ dom
			                  ((denot_relevant_env (<[LVFree x := T1]> Σ)
			                    (CTArrow τx τr) (e2 ^^ x) : lty_env)
			                    : gmap logic_var ty)) in Hv.
			                apply elem_of_dom in Hv as [Tv Hlook].
			                unfold denot_relevant_env, lty_env_restrict_lvars in Hlook.
			                change ((storeA_restrict
			                  (<[LVFree x := T1]> Σ)
			                  (denot_relevant_lvars (CTArrow τx τr) (e2 ^^ x))
			                  : gmap logic_var ty) !! v = Some Tv) in Hlook.
			                apply storeA_restrict_lookup_some in Hlook as [_ Hlook].
			                eapply elem_of_dom_2. exact Hlook.
		              + apply tm_lvars_tapp_tm_fvar_without_arg.
		            - change (myx ⊨ denot_ty_lvar_gas gas
		                (<[LVFree y := erase_ty τx]>
		                  (denot_relevant_env (<[LVFree x := T1]> Σ)
	                    (CTArrow τx τr) (e2 ^^ x)))
	                (cty_open 0 y τr)
	                (tlete (open_tm 0 (vfvar y) (tm_shift 0 (e2 ^^ x)))
	                  (tapp (vbvar 0) (vfvar y)))) in Hbody_after_inner.
	              rewrite open_tm_shift0_lc in Hbody_after_inner by tlet_lc_solver.
	              change (tlete (e2 ^^ x) (tapp (vbvar 0) (vfvar y)))
	                with (tapp_tm (e2 ^^ x) (vfvar y)) in Hbody_after_inner.
	              exact Hbody_after_inner.
	          }
	          eapply denot_ty_lvar_gas_insert_commute_tapp_open;
	            [ tlet_support_solver | exact Hbody_full ].
	        }
	        rewrite ?open_tapp_tm_fvar_lc_arg.
	        assert (HxΣ0 : LVFree x ∉
	          dom (<[LVFree y := erase_ty τx]> Σ)).
	        {
	          change (LVFree x ∉ dom
	            ((<[LVFree y := erase_ty τx]> (Σ : gmap logic_var ty))
	              : gmap logic_var ty)).
	          rewrite dom_insert_L. tlet_support_solver.
	        }
	        assert (HIH_result :
	          my ⊨ denot_ty_lvar_gas gas
	            (<[LVFree y := erase_ty τx]> Σ)
	            (cty_open 0 y τr)
	            (tlete e1 (tapp_tm e2 (vfvar y)))).
	        {
	          eapply IH with
	            (Σ := <[LVFree y := erase_ty τx]> Σ)
	            (T1 := T1)
	            (e1 := e1)
	            (e2 := tapp_tm e2 (vfvar y))
	            (m := my)
	            (mx := myx)
	            (Fx := Fx)
		            (x := x)
		            (τ := cty_open 0 y τr).
		          - apply lty_env_closed_insert_free. exact HΣ.
		          - apply basic_typing_lty_env_insert_free_away;
		              [tlet_support_solver|exact He1].
			          - rewrite cty_open_preserves_erasure.
			            inversion Hlet; subst.
			            assert (T0 = T1) by (eapply basic_typing_unique_tm; eauto).
			            subst T0.
			            eapply TT_Let with (L := L ∪ {[y]} ∪ fv_tm e2 ∪ dom (lty_env_to_atom_env Σ)).
			            + apply basic_typing_lty_env_insert_free_away;
			                [tlet_support_solver|exact He1].
		            + intros z Hz.
		              change ((tapp_tm e2 (vfvar y)) ^^ z) with
		                (open_tm 0 (vfvar z) (tapp_tm e2 (vfvar y))).
		              rewrite open_tapp_tm_lc_arg by constructor.
		              eapply basic_typing_tapp_tm.
		              * match goal with
		                | Hbody : forall a : atom, a ∉ ?L ->
		                    _ ⊢ₑ e2 ^^ a ⋮ _ |- _ =>
		                    eapply basic_typing_env_agree_tm;
		                    [eapply Hbody; tlet_support_solver|]
		                end.
		                intros w Hw.
		                assert (Hy_e2z : y ∉ fv_tm (e2 ^^ z)).
		                {
		                  intros Hybad.
		                  pose proof (open_fv_tm e2 (vfvar z) 0 y) as Hopen.
			                  cbn [fv_value] in Hopen.
			                  pose proof (Hopen Hybad) as Hcases.
			                  clear Hopen Hybad.
			                  clear - Hy Hz Hcases.
			                  tlet_normalize_freshness.
			                  set_solver.
			                }
			                assert (Hwy : w <> y) by (intros ->; exact (Hy_e2z Hw)).
				                rewrite (lvar_store_to_atom_store_insert_free (V:=ty)).
			                change ((((<[z := T1]> (<[y := erase_ty τx]>
			                  (lty_env_to_atom_env Σ))) : gmap atom ty) !! w) =
				                  (((<[z := T1]> (lty_env_to_atom_env Σ))
				                  : gmap atom ty) !! w)).
			                destruct (decide (w = z)) as [Hwz_eq|Hwz].
			                -- subst w.
			                   change (((<[z := T1]> (<[y := erase_ty τx]>
			                     (lty_env_to_atom_env Σ))) : gmap atom ty) !! z =
			                     (((<[z := T1]> (lty_env_to_atom_env Σ))
			                     : gmap atom ty) !! z)).
			                   transitivity (Some T1).
			                   ++ apply lookup_insert_eq.
			                   ++ symmetry. apply lookup_insert_eq.
			                -- transitivity (((<[y := erase_ty τx]>
			                     (lty_env_to_atom_env Σ)) : gmap atom ty) !! w).
			                   ++ apply lookup_insert_ne. congruence.
			                   ++ transitivity ((lty_env_to_atom_env Σ) !! w).
			                      ** apply lookup_insert_ne. congruence.
			                      ** symmetry. apply lookup_insert_ne. congruence.
		              * apply VT_FVar.
		                rewrite lookup_insert_ne by tlet_support_solver.
			                rewrite (lvar_store_to_atom_store_insert_free (V:=ty)).
		                apply lookup_insert_eq.
	          - exact HFx.
	          - eapply res_models_kripke; [exact Hle | exact Htotal].
	          - assert (Hmy_world_y :
	              my ⊨ basic_world_formula
	                ((<[LVFree y := erase_ty τx]>
	                    (∅ : gmap logic_var ty)) : lty_env)).
	            {
	              change (my ⊨ basic_world_formula
	                (lty_env_open_one 0 y
	                  ((<[LVBound 0 := erase_ty τx]>
	                      (∅ : gmap logic_var ty)) : lty_env))) in Hmy_world.
	              rewrite lty_env_open_one_bound0_singleton in Hmy_world.
	              exact Hmy_world.
	            }
	            assert (Htarget_world_my :
	              my ⊨ basic_world_formula
	                (denot_relevant_env Σ (CTArrow τx τr) (tlete e1 e2))).
	            {
	              eapply res_models_kripke; [exact Hle|].
	              pose proof Hguard_m as Hguard_parts.
	              repeat rewrite res_models_and_iff in Hguard_parts.
	              destruct Hguard_parts as [_ [Hworld _]].
	              exact Hworld.
	            }
	            assert (Hbasic_arrow_Σ :
	              basic_context_ty_lvars
	                (dom (Σ : gmap logic_var ty) : gset logic_var)
	                (CTArrow τx τr)).
	            {
	              pose proof Hguard_m as Hguard_parts.
	              repeat rewrite res_models_and_iff in Hguard_parts.
	              destruct Hguard_parts as [Hwf _].
	              pose proof (context_ty_wf_formula_basic_lvars _ _ _ Hwf)
	                as Hbasic_rel.
	              eapply basic_context_ty_lvars_mono; [|exact Hbasic_rel].
	              apply denot_relevant_env_dom_subset_direct.
	            }
	            eapply basic_world_formula_arrow_body_from_source_and_arg.
	            + exact HΣ.
	            + tlet_support_solver.
	            + exact Hbasic_arrow_Σ.
	            + apply tm_lvars_tlet_tapp_tm_fvar_without_arg.
	            + exact Htarget_world_my.
	            + exact Hmy_world_y.
	          - change (LVFree x ∉ dom
	              ((<[LVFree y := erase_ty τx]> (Σ : gmap logic_var ty))
	                : gmap logic_var ty) ∪
	              context_ty_lvars (cty_open 0 y τr)).
	            rewrite dom_insert_L.
	            assert (Hxτr_open :
	              LVFree x ∉ context_ty_lvars (cty_open 0 y τr)).
	            {
	              intros Hbad.
	              apply lvars_fv_elem in Hbad.
	              pose proof (cty_open_fv_subset 0 y τr x Hbad) as Hfvbad.
	              cbn [fv_value] in Hfvbad.
	              cbn [context_ty_lvars context_ty_lvars_at] in Hfresh.
	              apply elem_of_union in Hfvbad as [Hxτr|Hxy].
	              - apply Hfresh.
	                apply elem_of_union_r. apply elem_of_union_r.
	                apply lvars_fv_elem.
	                rewrite context_ty_lvars_fv_at. exact Hxτr.
	              - assert (x <> y) by tlet_support_solver.
	                set_solver.
	            }
	            set_solver.
		          - exact HmyFx.
		          - exact Hret_body_open.
		        }
		        assert (Hassoc_result :
		          my ⊨ denot_ty_lvar_gas gas
		            (<[LVFree y := erase_ty τx]> Σ)
		            (cty_open 0 y τr)
		            (tapp_tm (tlete e1 e2) (vfvar y))).
				        {
				          eapply denot_ty_lvar_gas_tapp_tlete_assoc.
				          - apply lty_env_closed_insert_free. exact HΣ.
				          - tlet_lc_solver.
				          - exact HIH_result.
				        }
		        eapply res_models_open_denot_ty_lvar_gas_from_open;
		          [ exact Hy_target_rel
		          | exact Hclosed_target_rel
		          | rewrite fv_tapp_tm, tm_shift_fv; cbn [fv_value];
		            tlet_support_solver
		          | tlet_support_solver
		          | ].
		        rewrite open_tapp_tm_shift_bvar0_lc by tlet_lc_solver.
		        assert (Hbasic_arrow_Σ_final :
		          basic_context_ty_lvars
		            (dom (Σ : gmap logic_var ty) : gset logic_var)
		            (CTArrow τx τr)).
		        {
		          pose proof Hguard_m as Hguard_parts.
		          repeat rewrite res_models_and_iff in Hguard_parts.
		          destruct Hguard_parts as [Hwf _].
		          pose proof (context_ty_wf_formula_basic_lvars _ _ _ Hwf)
		            as Hbasic_rel.
		          eapply basic_context_ty_lvars_mono; [|exact Hbasic_rel].
		          apply denot_relevant_env_dom_subset_direct.
		        }
		        eapply res_models_denot_ty_lvar_gas_env_agree_on
		          with (X := denot_relevant_lvars
		            (cty_open 0 y τr)
		            (tapp_tm (tlete e1 e2) (vfvar y)));
		          [ reflexivity
		          | symmetry;
		            apply arrow_body_relevant_env_agree_from_basic_context_ty;
		            [ exact HΣ
		            | tlet_support_solver
			            | exact Hbasic_arrow_Σ_final
			            | apply tm_lvars_tapp_tm_fvar_without_arg ]
			          | exact Hassoc_result ].
    + change (m ⊨ denot_ty_lvar_gas (S gas) Σ
          (CTWand τx τr) (tlete e1 e2)).
      change (mx ⊨ denot_ty_lvar_gas (S gas)
          (<[LVFree x := T1]> Σ) (CTWand τx τr) (e2 ^^ x)) in Hmx.
      eapply tlet_intro_denotation_wand_case; eauto.
Qed.

End TLetDenotation.
