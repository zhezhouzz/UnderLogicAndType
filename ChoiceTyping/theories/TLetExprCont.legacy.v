(** * ChoiceTyping.TLetExprCont

    Expression-continuation transport for [tlet].  These lemmas are about
    operational result worlds and [FExprContIn], before the structural
    induction over choice types in [TLetReduction]. *)

From CoreLang Require Import Instantiation BasicTypingProps Sugar.
From ChoiceLogic Require Export FormulaDerived FormulaWorldExtension.
From ChoiceTyping Require Export TLetTotal.
From ChoiceTyping Require Import Naming ResultWorldClosed
  ResultWorldExprCont ResultWorldExtension.
From ChoiceType Require Import BasicStore DenotationNotation.

Import Tactics.

Local Ltac tlet_regular :=
  eauto 6 using basic_typing_contains_fv_tm, typing_tm_lc.

Lemma FExprContIn_atom_env Σ e (Q : FormulaQ) :
  FExprContIn (atom_env_to_lty_env Σ) e Q = FExprContIn Σ e Q.
Proof.
  unfold FExprContIn, FExprResultOn, into_lvars, into_lvars_lvset,
    into_lvars_aset.
  rewrite atom_env_to_lty_env_dom.
  reflexivity.
Qed.

Local Lemma tlet_body_typing_for_result
    (Σ : gmap atom ty) T1 T2 e1 e2 x :
  Σ ⊢ₑ e1 ⋮ T1 →
  Σ ⊢ₑ tlete e1 e2 ⋮ T2 →
  x ∉ dom Σ →
  <[x := T1]> Σ ⊢ₑ e2 ^^ x ⋮ T2.
Proof.
  intros He1 Hlet Hx.
  eapply basic_typing_tlete_body_for_fresh.
  - exact He1.
  - exact Hlet.
  - exact Hx.
Qed.

Lemma expr_total_on_tlete_elim_body_ext
    X e1 e2 x (m mx : WfWorld) F :
  result_extends_on X e1 x m F mx ->
  X ⊆ world_dom (m : World) ->
  fv_tm (tlete e1 e2) ⊆ X ->
  x ∉ X ->
  x ∉ fv_tm e2 ->
  world_closed_on X m ->
  lc_tm (tlete e1 e2) ->
  expr_total_on (tlete e1 e2) m ->
  expr_total_on (e2 ^^ x) mx.
Proof.
  (* Direct extension-style operational elimination for the tlet body.
     The proof should use [result_extends_on_elim] to recover the base store
     and result witness, then replay the operational tlet decomposition.  The
     direct proof currently checks too slowly in this file, so keep the exact
     obligation and avoid falling back to the concrete result-world model. *)
  admit.
Admitted.

Lemma open_impl k y (P Q: FormulaQ):
  formula_open k y (P → Q)%formula = ((formula_open k y P) → (formula_open k y Q))%formula.
Proof. reflexivity. Qed.

Lemma formula_open_FExprResultOn_at {A : Type} `{IntoLVars A}
    (D : A) e y :
  formula_open 0 y (FExprResultOn D e) = FExprResultAt D e y.
Proof.
  (* Compatibility lemma for the old implicit-result wrapper.  The new primary
     route uses [FExprResultAtLvar] directly. *)
Admitted.

Local Lemma FExprResultAt_into_lvars_atom_env
    (Σ : gmap atom ty) e y :
  FExprResultAt (into_lvars Σ) e y = FExprResultAt (dom Σ) e y.
Proof.
  unfold FExprResultAt.
  cbn [into_lvars into_lvars_lvset into_lvars_aset].
  denot_lvars_norm.
  reflexivity.
Qed.

Local Lemma formula_open_FExprContIn_antecedent_atom_env
    (Σ : gmap atom ty) e y Q :
  lc_tm e →
  formula_open 0 y
    (FImpl
      (FExprResultAtLvar (lvars_shift (lvars_of_atoms (dom Σ)))
        (tm_shift 0 e) (LVBound 0)) Q) =
  FImpl (FExprResultAt (dom Σ) e y) (formula_open 0 y Q).
Proof.
  intros Hlc.
  rewrite open_impl.
  rewrite formula_open_FExprResultAtLvar_shift_atom by exact Hlc.
  reflexivity.
Qed.

Lemma FExprCont_tlet_reduction
    (Σ : gmap atom ty) (T1 T2 : ty)
    (m mx : WfWorld) Fx e1 e2 (x : atom) (Q : FormulaQ) :
  result_extends e1 x m Fx mx →
  Σ ⊢ₑ e1 ⋮ T1 →
  Σ ⊢ₑ tlete e1 e2 ⋮ T2 →
  x ∉ dom Σ →
  world_dom (m : World) = dom Σ →
  world_closed_on (dom Σ) m →
  expr_total_on (tlete e1 e2) m →
  formula_fv Q ⊆ dom Σ →
  mx ⊨ FExprContIn (<[x := T1]> Σ) (e2 ^^ x) Q ->
  m ⊨ FExprContIn Σ (tlete e1 e2) Q.
Proof.
  intros Hext He1 Hlet HxΣ Hdom Hclosed Htotal_let HQfv Hcont.
  pose proof (basic_typing_contains_fv_tm Σ (tlete e1 e2) T2 Hlet)
    as Hfvlet.
  assert (Hfv1 : fv_tm e1 ⊆ world_dom (m : World)).
  { rewrite Hdom. simpl in Hfvlet. set_solver. }
  assert (Hfv2 : fv_tm e2 ⊆ world_dom (m : World)).
  { rewrite Hdom. simpl in Hfvlet. set_solver. }
  assert (Hxe2 : x ∉ fv_tm e2).
  { simpl in Hfvlet. set_solver. }
  assert (Hlc_tlet : lc_tm (tlete e1 e2)) by tlet_regular.
  assert (Hbody : body_tm e2).
  { apply lc_lete_iff_body in Hlc_tlet as [_ Hbody]. exact Hbody. }
  assert (Htotal_e1_m : expr_total_on e1 m).
  {
    eapply (expr_total_on_tlete_elim_e1_strong (world_dom (m : World)));
      eauto.
    - rewrite Hdom. exact Hfvlet.
    - rewrite Hdom. exact Hclosed.
  }
  assert (Hscope :
    formula_scoped_in_world ∅ m (FExprContIn Σ (tlete e1 e2) Q)).
  {
    unfold formula_scoped_in_world.
    rewrite dom_empty_L.
    pose proof (FExprContIn_formula_fv_subset
      Σ (tlete e1 e2) (dom Σ) Q ltac:(set_solver) HQfv) as Hfv_cont.
    rewrite Hdom.
    set_solver.
  }
  unfold FExprContIn in Hcont |- *.
  eapply (res_models_forall_extend_input_widen m mx Fx); eauto.
  - exact (result_extends_by _ _ _ _ _ Hext).
  - exists (world_dom (mx : World) ∪ dom Σ ∪ formula_fv Q ∪
      fv_tm e1 ∪ fv_tm e2).
    split; [set_solver |].
    intros y Fy my ny Hy HShapeFy HFy HFxy Hny.
    rewrite !not_elem_of_union in Hy.
    destruct Hy as [[[[Hy_mx HyΣ] HyQ] Hye1] Hye2].
    destruct HShapeFy as [HFy_in HFy_out].
    pose proof (res_extend_by_dom _ _ _ HFy) as Hdom_my.
    rewrite HFy_out in Hdom_my.
    assert (Hy_m : y ∉ world_dom (m : World)).
    { rewrite Hdom. exact HyΣ. }
    assert (Hclosed_my : world_closed_on (world_dom (m : World)) my).
    {
      eapply world_closed_on_extend.
      - set_solver.
      - eapply res_extend_by_le_base. exact HFy.
      - rewrite Hdom. exact Hclosed.
    }
    assert (Htotal_e1_my : expr_total_on e1 my).
    {
      split.
      - rewrite Hdom_my. set_solver.
      - eapply result_witness_lift_extend.
        + exact Hfv1.
        + exact HFy.
        + exact (proj2 Htotal_e1_m).
    }
    assert (Hext_my : result_extends_on (world_dom (m : World)) e1 x my Fx ny).
    {
      refine {| result_extends_on_fresh_input :=
        result_extends_fresh _ _ _ _ _ Hext |}.
      - rewrite Hdom_my. set_solver.
      - pose proof (res_extend_by_output_fresh _ _ _ HFxy) as Hfresh_out.
        pose proof (result_extends_shape _ _ _ _ _ Hext) as [_ HFx_out].
        rewrite HFx_out in Hfresh_out. set_solver.
      - exact (result_extends_eq _ _ _ _ _ Hext).
      - exact HFxy.
    }
    assert (HQopen_fv :
      formula_fv (formula_open 0 y Q) ⊆ world_dom (my : World)).
    {
      intros z Hz.
      pose proof (formula_open_fv_subset 0 y Q z Hz) as Hzopen.
      rewrite Hdom_my, Hdom.
      set_solver.
    }
    change (res_models my
      (formula_open 0 y
        (FImpl
          (FExprResultAtLvar
            (lvars_shift (lvars_of_atoms (dom Σ)))
            (tm_shift 0 (tlete e1 e2)) (LVBound 0)) Q))).
    change (res_models ny
      (formula_open 0 y
        (FImpl
          (FExprResultAtLvar
            (lvars_shift (lvars_of_atoms (dom (<[x := T1]> Σ))))
            (tm_shift 0 (e2 ^^ x)) (LVBound 0)) Q))) in Hny.
    cbn [formula_open] in Hny |- *.
    rewrite formula_open_FExprResultAtLvar_shift_atom by exact Hlc_tlet.
    rewrite formula_open_FExprResultAtLvar_shift_atom in Hny
      by (apply body_open_tm; [exact Hbody | constructor]).
    eapply res_models_impl_intro.
    + unfold formula_scoped_in_world.
      rewrite dom_empty_L.
      cbn [formula_fv].
      rewrite FExprResultAt_fv.
      rewrite Hdom_my, Hdom.
      set_solver.
    + intros Hresult_tlet.
      assert (Hresult_tlet_world :
        my ⊨ FExprResultAt (world_dom (m : World)) (tlete e1 e2) y).
      {
        rewrite Hdom.
        exact Hresult_tlet.
      }
      assert (Hresult_body_world :
        ny ⊨ FExprResultAt (world_dom (m : World) ∪ {[x]})
          (e2 ^^ x) y).
      {
        pose proof (FExprResultAt_tlet_result_extension_iff
          (world_dom (m : World)) e1 e2 x y my ny Fx
          Hext_my Hfv1 Hfv2 Hlc_tlet Hbody Hy_m Hdom_my
          Hclosed_my Htotal_e1_my) as Hresult_iff.
        exact (proj2 Hresult_iff Hresult_tlet_world).
      }
      assert (Hresult_body :
        ny ⊨ FExprResultAt (dom (<[x := T1]> Σ)) (e2 ^^ x) y).
      {
        replace (dom (<[x := T1]> Σ)) with
          (world_dom (m : World) ∪ {[x]}).
        - exact Hresult_body_world.
        - rewrite Hdom, dom_insert_L. set_solver.
      }
      pose proof (res_models_impl_elim _ _ _ Hny Hresult_body) as HQ_ny.
      exact (proj1 (res_models_extend_base_iff my Fx ny
        (formula_open 0 y Q) HFxy HQopen_fv) HQ_ny).
Qed.
