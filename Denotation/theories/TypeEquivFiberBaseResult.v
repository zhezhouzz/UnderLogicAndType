(** * Denotation.TypeEquivFiberBaseResult

    Result-formula and fiber witness support for projected transport. *)

From Denotation Require Import Notation TypeDenote TypeEquivCore TypeEquivTerm
  DenotationSetMapFacts TypeEquivFiberBaseCore.
From ContextBasicDenotation Require Import StoreTyping TermEval.
From CoreLang Require Import StrongNormalization InstantiationProps.

Section TypeDenote.

Lemma res_fiber_stores_agree_on_sub
    (m mfib : WfWorldT) X σ X0 τ1 τ2 :
  X0 ⊆ X ->
  X0 ⊆ world_dom (mfib : WorldT) ->
  res_fiber_from_projection m X σ mfib ->
  (mfib : WorldT) τ1 ->
  (mfib : WorldT) τ2 ->
  store_restrict τ1 X0 = store_restrict τ2 X0.
Proof.
  intros HX0X HX0dom Hproj Hτ1 Hτ2.
  pose proof (res_subset_fiber_source m mfib X σ Hproj)
    as [Hdom_fib _].
  assert (HX0σ : X0 ⊆ dom (σ : StoreT)).
  {
    intros a Ha.
    destruct Hproj as [Hproj_src _].
    pose proof (wfworld_store_dom (res_restrict m X) σ Hproj_src)
      as Hσdom.
    change (dom (σ : StoreT) = world_dom (res_restrict m X : WorldT))
      in Hσdom.
    rewrite Hσdom.
    change (a ∈ world_dom (res_restrict m X : WorldT)).
    rewrite res_restrict_dom.
    change (a ∈ world_dom (m : WorldT) ∩ X).
    apply elem_of_intersection. split.
    - assert (Hamfib : a ∈ world_dom (mfib : WorldT)).
      { exact (HX0dom a Ha). }
      change (world_dom (mfib : WorldT) = world_dom (m : WorldT))
        in Hdom_fib.
      rewrite Hdom_fib in Hamfib. exact Hamfib.
    - exact (HX0X a Ha).
  }
  pose proof (res_fiber_from_projection_store_restrict m mfib X σ τ1
    Hproj Hτ1) as Hτ1σ.
  pose proof (res_fiber_from_projection_store_restrict m mfib X σ τ2
    Hproj Hτ2) as Hτ2σ.
  transitivity (store_restrict σ X0).
  - rewrite <- Hτ1σ.
    rewrite storeA_restrict_restrict.
    replace (dom (σ : StoreT) ∩ X0) with X0 by set_solver.
    reflexivity.
  - rewrite <- Hτ2σ.
    rewrite storeA_restrict_restrict.
    replace (dom (σ : StoreT) ∩ X0) with X0 by set_solver.
    reflexivity.
Qed.

Lemma expr_result_formula_transport_fiber
    (m mfib : WfWorldT) X σ e1 e2 y :
  lc_tm e1 ->
  LVFree y ∉ tm_lvars e1 ->
  fv_tm e1 ⊆ X ->
  fv_tm e1 ⊆ world_dom (mfib : WorldT) ->
  tm_fiber_equiv_on m X e1 e2 ->
  res_fiber_from_projection m X σ mfib ->
  mfib ⊨ expr_result_formula e2 (LVFree y) ->
  mfib ⊨ expr_result_formula e1 (LVFree y).
Proof.
  intros Hlc1 Hyfresh HfvX HfvWorld Heq Hproj Hres2.
  pose proof (expr_result_formula_models_elim e2 (LVFree y) mfib Hres2)
    as [_ [_ Hstore2]].
  apply expr_result_atom_world_to_formula.
  - split; [exact Hyfresh|]. split.
    + intros z Hz.
      apply elem_of_union in Hz as [Hz|Hz].
      * destruct z as [k|a].
        -- exfalso. exact ((tm_lvars_lc e1 Hlc1) (LVBound k) Hz).
        -- rewrite res_lift_free_dom. unfold lvars_of_atoms.
           apply elem_of_map. exists a. split; [reflexivity|].
           apply HfvWorld. rewrite <- tm_lvars_fv.
           apply lvars_fv_elem. exact Hz.
      * apply elem_of_singleton in Hz as ->.
        pose proof (expr_result_formula_to_atom_world e2 (LVFree y) mfib Hres2)
          as [Hy2 [Hdom2 _]].
        specialize (Hdom2 (LVFree y) ltac:(apply elem_of_union_r; set_solver)).
        rewrite res_lift_free_dom in Hdom2 |- *.
        exact Hdom2.
    + intros τL HτL.
      destruct HτL as [τ [Hτ ->]].
      pose proof (Hstore2 τ Hτ) as [_ [v [Hylookup Heval2]]].
      pose proof (tm_fiber_equiv_result_pullback m X e1 e2 τ v Heq
        ltac:(eapply res_fiber_from_projection_store_source; eauto)
        Heval2) as [τ1 [Hτ1m [Hτ1X Heval1τ1]]].
      assert (Hτ1fib : (mfib : WorldT) τ1).
      {
        pose proof Hproj as [_ Hfib_eq].
        change ((mfib : WorldT) = raw_fiber (m : WorldT) σ) in Hfib_eq.
        rewrite Hfib_eq. split; [exact Hτ1m|].
        pose proof (res_fiber_from_projection_store_restrict m mfib X σ τ
          Hproj Hτ) as Hτproj.
        transitivity (store_restrict τ (dom (σ : StoreT))); [|exact Hτproj].
        eapply storeA_restrict_eq_mono; [|exact Hτ1X].
        intros a Ha.
        pose proof (res_fiber_from_projection_store_dom_subset m mfib X σ Hproj)
          as Hσdom.
        exact (Hσdom a Ha).
      }
      split; [exact Hyfresh|].
      exists v. split; [exact Hylookup|].
      eapply tm_eval_in_store_agree_on_fv; [|exact Heval1τ1].
      eapply (res_fiber_stores_agree_on_sub m mfib X σ (fv_tm e1) τ τ1).
      * exact HfvX.
      * exact HfvWorld.
      * exact Hproj.
      * exact Hτ.
      * exact Hτ1fib.
  - intros z τ v Hz Hτ Heval1.
    inversion Hz. subst z.
    assert (Hτm : (m : WorldT) τ).
    { eapply res_fiber_from_projection_store_source; eauto. }
    assert (Heval1_full : tm_eval_in_store τ e1 v).
    {
      apply (proj1 (tm_eval_in_store_restrict_fv_exact τ e1 v)).
      exact Heval1.
    }
    pose proof (Heq (store_restrict τ X)
      ltac:(exists τ; split; [exact Hτm|reflexivity]) v) as [H12 _].
    destruct (H12 ltac:(exists τ; split; [exact Hτm|split; [reflexivity|exact Heval1_full]]))
      as [τ2 [Hτ2m [Hτ2X Heval2]]].
    assert (Hτ2fib : (mfib : WorldT) τ2).
    {
      pose proof Hproj as [_ Hfib_eq].
      change ((mfib : WorldT) = raw_fiber (m : WorldT) σ) in Hfib_eq.
      rewrite Hfib_eq. split; [exact Hτ2m|].
      pose proof (res_fiber_from_projection_store_restrict m mfib X σ τ
        Hproj Hτ) as Hτproj.
      transitivity (store_restrict τ (dom (σ : StoreT))); [|exact Hτproj].
      eapply storeA_restrict_eq_mono; [|exact Hτ2X].
      intros a Ha.
      pose proof (res_fiber_from_projection_store_dom_subset m mfib X σ Hproj)
        as Hσdom.
      exact (Hσdom a Ha).
    }
    pose proof (expr_result_formula_fiber_witness e2 y mfib Hres2
      τ2 v Hτ2fib
      ltac:(apply (proj2 (tm_eval_in_store_restrict_fv_exact τ2 e2 v));
        exact Heval2))
      as [τv [Hτv [Hτv_e2 Hylookup]]].
    exists τv. split; [exact Hτv|]. split; [|exact Hylookup].
    rewrite tm_lvars_fv.
    symmetry.
    eapply (res_fiber_stores_agree_on_sub m mfib X σ (fv_tm e1) τ τv).
    + exact HfvX.
    + exact HfvWorld.
    + exact Hproj.
    + exact Hτ.
    + exact Hτv.
Qed.


Lemma res_models_transport_singleton_fv
    (m n : WfWorldT) x (P : FormulaT) :
  formula_fv P ⊆ {[x]} ->
  res_restrict m ({[x]} : aset) =
    res_restrict n ({[x]} : aset) ->
  m ⊨ P ->
  n ⊨ P.
Proof.
  intros Hfv Hproj HP.
  eapply res_models_projection; [|exact HP].
  eapply res_restrict_eq_subset; [exact Hfv|exact Hproj].
Qed.

Lemma formula_fv_msubst_open_over_result_only σ y φ :
  lvars_fv (lvars_open 0 y (qual_vars φ ∖ {[LVBound 0]})) ⊆
    dom (σ : StoreT) ->
  formula_fv
    (formula_msubst_store σ
      (formula_open 0 y (FOver (FAtom φ)))) ⊆ {[y]}.
Proof.
  intros Hdom.
  rewrite formula_msubst_store_fv.
  rewrite formula_open_over, formula_fv_over.
  rewrite formula_open_atom, formula_fv_atom.
  unfold qual_dom.
  intros x Hx.
  rewrite elem_of_difference in Hx.
  destruct Hx as [Hx Hxσ].
  apply lvars_fv_elem in Hx.
  rewrite qual_open_atom_vars in Hx.
  destruct (decide (x = y)) as [->|Hxy]; [set_solver|].
  exfalso. apply Hxσ.
  apply Hdom.
  rewrite lvars_fv_elem.
  rewrite elem_of_set_swap in Hx.
  apply elem_of_set_swap.
  destruct (decide (swap (LVBound 0) (LVFree y) (LVFree x) = LVBound 0))
    as [Hbad|Hnot_bound].
  - unfold swap in Hbad.
    repeat destruct decide; try congruence.
  - apply elem_of_difference. split.
    + exact Hx.
    + intros Hzero.
      apply elem_of_singleton in Hzero.
      exact (Hnot_bound Hzero).
Qed.

Lemma formula_fv_msubst_open_under_result_only σ y φ :
  lvars_fv (lvars_open 0 y (qual_vars φ ∖ {[LVBound 0]})) ⊆
    dom (σ : StoreT) ->
  formula_fv
    (formula_msubst_store σ
      (formula_open 0 y (FUnder (FAtom φ)))) ⊆ {[y]}.
Proof.
  intros Hdom.
  rewrite formula_msubst_store_fv.
  rewrite formula_open_under, formula_fv_under.
  rewrite formula_open_atom, formula_fv_atom.
  unfold qual_dom.
  intros x Hx.
  rewrite elem_of_difference in Hx.
  destruct Hx as [Hx Hxσ].
  apply lvars_fv_elem in Hx.
  rewrite qual_open_atom_vars in Hx.
  destruct (decide (x = y)) as [->|Hxy]; [set_solver|].
  exfalso. apply Hxσ.
  apply Hdom.
  rewrite lvars_fv_elem.
  rewrite elem_of_set_swap in Hx.
  apply elem_of_set_swap.
  destruct (decide (swap (LVBound 0) (LVFree y) (LVFree x) = LVBound 0))
    as [Hbad|Hnot_bound].
  - unfold swap in Hbad.
    repeat destruct decide; try congruence.
  - apply elem_of_difference. split.
    + exact Hx.
    + intros Hzero.
      apply elem_of_singleton in Hzero.
      exact (Hnot_bound Hzero).
Qed.

Lemma res_models_FFibVars_transport_result_only
    (ms mt : WfWorldT) D P y :
  formula_scoped_in_world mt (FFibVars D P) ->
  (forall σ,
    lvars_fv D ⊆ dom (σ : StoreT) ->
    formula_fv (formula_msubst_store σ P) ⊆ {[y]}) ->
  (forall σ mtfib,
    res_fiber_from_projection mt (lvars_fv D) σ mtfib ->
    exists msfib,
      res_fiber_from_projection ms (lvars_fv D) σ msfib /\
      res_restrict msfib ({[y]} : aset) =
        res_restrict mtfib ({[y]} : aset)) ->
  ms ⊨ FFibVars D P ->
  mt ⊨ FFibVars D P.
Proof.
  intros Hscope_t HfvP Hfiber Hsrc.
  apply res_models_FFibVars_iff in Hsrc as [_ [HlcD Hsrc_fib]].
  eapply res_models_FFibVars_intro; [exact Hscope_t|exact HlcD|].
  intros σ mtfib Hproj_t.
  destruct (Hfiber σ mtfib Hproj_t) as [msfib [Hproj_s Hys]].
  eapply res_models_transport_singleton_fv.
  - apply HfvP.
    assert (Hσdom :
        dom (σ : StoreT) =
        world_dom (res_restrict mt (lvars_fv D) : WorldT)).
    {
      destruct Hproj_t as [Hσ _].
      exact (wfworld_store_dom (res_restrict mt (lvars_fv D)) σ Hσ).
    }
    rewrite Hσdom, res_restrict_dom.
    apply (proj1 (formula_scoped_fibvars_iff mt D P)) in Hscope_t
      as [HD _].
    set_solver.
  - exact Hys.
  - exact (Hsrc_fib σ msfib Hproj_s).
Qed.

Lemma expr_result_residual_singleton_on D e y (σ : StoreT) :
  lc_lvars D ->
  tm_lvars e ⊆ D ->
  LVFree y ∉ D ->
  dom (σ : StoreT) = lvars_fv D ->
  (tm_lvars e ∪ {[LVFree y]}) ∖
    dom (atom_store_to_lvar_store σ : LStoreT) =
  ({[LVFree y]} : lvset).
Proof.
  intros HlcD HeD HyD Hdom.
  apply set_eq. intros v.
  rewrite elem_of_difference, elem_of_union, elem_of_singleton.
  rewrite atom_store_to_lvar_store_dom.
  split.
  - intros [[HvE|HvY] Hnot].
    + exfalso. apply Hnot.
      pose proof (HeD _ HvE) as HvD.
      destruct v as [k|a].
      * exfalso. exact (HlcD (LVBound k) HvD).
      * unfold lvars_of_atoms.
        apply elem_of_map. exists a. split; [reflexivity|].
        assert (HaD : a ∈ lvars_fv D)
          by (apply lvars_fv_elem; exact HvD).
        rewrite <- Hdom in HaD. exact HaD.
    + subst v. reflexivity.
  - intros ->. split; [right; reflexivity|].
    intros Hbad. apply HyD.
    unfold lvars_of_atoms in Hbad.
    apply elem_of_map in Hbad as [a [Heq Ha]].
    change (a ∈ dom (σ : StoreT)) in Ha.
    inversion Heq. subst a.
    apply lvars_fv_elem.
    rewrite Hdom in Ha. exact Ha.
Qed.

Lemma expr_result_msubst_back_input_restrict_agree e y
    (σproj σ : StoreT)
    (s : LStoreOn (V := value)
      ((tm_lvars e ∪ {[LVFree y]}) ∖
        dom (atom_store_to_lvar_store σproj : LStoreT))) :
  lc_lvars (tm_lvars e) ->
  lvars_fv (tm_lvars e) ⊆ dom (σ : StoreT) ->
  store_restrict σproj (lvars_fv (tm_lvars e)) =
    store_restrict σ (lvars_fv (tm_lvars e)) ->
  storeA_restrict
    (lso_store (lstore_on_mlsubst_back
      (tm_lvars e ∪ {[LVFree y]})
      (atom_store_to_lvar_store σproj) s))
    (tm_lvars e) =
  storeA_restrict (lstore_lift_free σ : LStoreT) (tm_lvars e).
Proof.
  intros Hlc Hsubσ Hagree.
  apply storeA_map_eq. intros z.
  destruct (decide (z ∈ tm_lvars e)) as [Hz|Hz].
  2:{
    transitivity (@None value).
    - apply storeA_restrict_lookup_none_r. exact Hz.
    - symmetry. apply storeA_restrict_lookup_none_r. exact Hz.
  }
  rewrite !storeA_restrict_lookup.
  destruct (decide (z ∈ tm_lvars e)) as [_|Hbad]; [|contradiction].
  destruct z as [k|a].
  - exfalso. exact (Hlc (LVBound k) Hz).
  - unfold lstore_on_mlsubst_back. cbn [lso_store storeAO_store].
    assert (Ha_fv : a ∈ lvars_fv (tm_lvars e)).
    { apply lvars_fv_elem. exact Hz. }
    rewrite lookup_union_r.
    2:{
      apply not_elem_of_dom.
      change (LVFree a ∉ dom (lso_store s : LStoreT)).
      rewrite (lso_dom s).
      intros Hrem.
      apply elem_of_difference in Hrem as [_ Hnot].
      apply Hnot.
      rewrite atom_store_to_lvar_store_dom.
      unfold lvars_of_atoms.
      apply elem_of_map. exists a. split; [reflexivity|].
      change (a ∈ dom (σproj : StoreT)).
      assert (Ha_proj : a ∈ dom (store_restrict σproj
        (lvars_fv (tm_lvars e)) : StoreT)).
      {
        rewrite Hagree.
        change (a ∈ dom (store_restrict σ (lvars_fv (tm_lvars e)) :
          gmap atom value)).
        rewrite storeA_restrict_dom.
        apply elem_of_intersection. split; [apply Hsubσ|]; exact Ha_fv.
      }
      change (a ∈ dom (store_restrict σproj
        (lvars_fv (tm_lvars e)) : gmap atom value)) in Ha_proj.
      rewrite storeA_restrict_dom in Ha_proj.
      set_solver.
    }
    rewrite atom_store_to_lvar_store_lookup_free.
    rewrite storeA_restrict_lookup.
    destruct (decide (LVFree a ∈ tm_lvars e)) as [_|Hnot_in];
      [|contradiction].
    rewrite lstore_lift_free_lookup_free.
    destruct (decide (LVFree a ∈ tm_lvars e ∪ {[LVFree y]})) as [_|HbadQ].
    2:{ exfalso. apply HbadQ. apply elem_of_union_l. exact Hz. }
    pose proof (Hsubσ a Ha_fv) as Ha_dom.
    change (a ∈ dom (σ : gmap atom value)) in Ha_dom.
    apply elem_of_dom in Ha_dom as [va Hσa].
    replace ((σ : StoreT) !! a) with (Some va) by (symmetry; exact Hσa).
    assert (Hproj_lookup :
        ((store_restrict σproj (lvars_fv (tm_lvars e)) : StoreT) : gmap atom value)
          !! a = Some va).
    {
      rewrite Hagree.
      change (((storeA_restrict σ (lvars_fv (tm_lvars e)) : gmap atom value)
        !! a) = Some va).
      apply storeA_restrict_lookup_some_2; [exact Hσa|exact Ha_fv].
    }
    change (((storeA_restrict σproj (lvars_fv (tm_lvars e)) : gmap atom value)
      !! a) = Some va) in Hproj_lookup.
    apply storeA_restrict_lookup_some in Hproj_lookup as [_ Hσproj_a].
    exact Hσproj_a.
Qed.

Lemma expr_result_msubst_back_lift_store_eq_agree e y
    (σproj σ : StoreT)
    (HlcQ : lc_lvars (tm_lvars e ∪ {[LVFree y]}))
    (HsubQ : lvars_fv (tm_lvars e ∪ {[LVFree y]}) ⊆ dom (σ : StoreT))
    (HlcR :
      lc_lvars ((tm_lvars e ∪ {[LVFree y]}) ∖
        dom (atom_store_to_lvar_store σproj : LStoreT)))
    (HsubR :
      lvars_fv ((tm_lvars e ∪ {[LVFree y]}) ∖
        dom (atom_store_to_lvar_store σproj : LStoreT)) ⊆ dom (σ : StoreT)) :
  store_restrict σproj (lvars_fv (tm_lvars e)) =
    store_restrict σ (lvars_fv (tm_lvars e)) ->
  y ∉ dom (σproj : StoreT) ->
  lstore_on_mlsubst_back (tm_lvars e ∪ {[LVFree y]})
    (atom_store_to_lvar_store σproj)
    (lstore_on_lift_store
      ((tm_lvars e ∪ {[LVFree y]}) ∖
        dom (atom_store_to_lvar_store σproj : LStoreT))
      σ HlcR HsubR) =
  lstore_on_lift_store (tm_lvars e ∪ {[LVFree y]}) σ HlcQ HsubQ.
Proof.
  intros Hagree Hyproj.
  apply lstore_on_mlsubst_back_lift_store.
  apply storeA_map_eq. intros v.
  destruct (decide (v ∈ tm_lvars e ∪ {[LVFree y]})) as [HvQ|HvQ].
  2:{
    transitivity (@None value).
    - apply storeA_restrict_lookup_none_r. exact HvQ.
    - symmetry. apply storeA_restrict_lookup_none_r.
      intros Hvbad. apply elem_of_intersection in Hvbad as [Hvbad _].
      exact (HvQ Hvbad).
  }
  destruct (decide (v ∈ dom (atom_store_to_lvar_store σproj : LStoreT)))
    as [Hvρ|Hvρ].
  2:{
    transitivity (@None value).
    - apply storeA_restrict_lookup_none_l.
      apply not_elem_of_dom. exact Hvρ.
    - symmetry. apply storeA_restrict_lookup_none_r.
      intros Hvbad. apply elem_of_intersection in Hvbad as [_ Hvbad].
      exact (Hvρ Hvbad).
  }
  rewrite !storeA_restrict_lookup.
  destruct (decide (v ∈ tm_lvars e ∪ {[LVFree y]})) as [_|Hbad];
    [|contradiction].
  destruct (decide (v ∈ (tm_lvars e ∪ {[LVFree y]}) ∩
      dom (atom_store_to_lvar_store σproj : LStoreT))) as [_|Hbad].
  2:{ exfalso. apply Hbad. apply elem_of_intersection. split; assumption. }
  rewrite atom_store_to_lvar_store_dom in Hvρ.
  unfold lvars_of_atoms in Hvρ.
  apply elem_of_map in Hvρ as [a [-> Ha]].
  rewrite atom_store_to_lvar_store_lookup_free.
  rewrite lstore_lift_free_lookup_free.
  assert (Ha_fv : a ∈ lvars_fv (tm_lvars e)).
  {
    apply elem_of_union in HvQ as [HvQ|HvQ].
    - apply lvars_fv_elem. exact HvQ.
    - apply elem_of_singleton in HvQ. inversion HvQ. subst a.
      exfalso. exact (Hyproj Ha).
  }
  assert (Hlookup_eq : (σproj : StoreT) !! a = (σ : StoreT) !! a).
  {
  destruct ((σ : StoreT) !! a) as [va|] eqn:Hσa.
  - assert (Hproj_lookup :
        ((store_restrict σproj (lvars_fv (tm_lvars e)) : StoreT)
          : gmap atom value) !! a = Some va).
    {
      rewrite Hagree.
      change (((storeA_restrict σ (lvars_fv (tm_lvars e)) :
        gmap atom value) !! a) = Some va).
      apply storeA_restrict_lookup_some_2; [exact Hσa|exact Ha_fv].
    }
    apply storeA_restrict_lookup_some in Hproj_lookup as [_ Hσproj_a].
    first [
      exact Hσproj_a
    | replace (σ !! a) with (Some va) by exact Hσa; exact Hσproj_a
    ].
  - change (σproj !! a = None).
    assert (Ha_not_proj : a ∉ dom (σproj : StoreT)).
    {
      intros Haσproj.
      assert (Hproj_dom_a :
          a ∈ dom (store_restrict σproj (lvars_fv (tm_lvars e)) : StoreT)).
      {
        change (a ∈ dom (storeA_restrict σproj (lvars_fv (tm_lvars e)) :
          gmap atom value)).
        rewrite storeA_restrict_dom.
        apply elem_of_intersection. split; [exact Haσproj|exact Ha_fv].
      }
      rewrite Hagree in Hproj_dom_a.
      change (a ∈ dom (storeA_restrict σ (lvars_fv (tm_lvars e)) :
        gmap atom value)) in Hproj_dom_a.
      rewrite storeA_restrict_dom in Hproj_dom_a.
      apply elem_of_intersection in Hproj_dom_a as [Haσ _].
      apply elem_of_dom in Haσ as [v Hv].
      change ((σ : StoreT) !! a = Some v) in Hv.
      rewrite Hσa in Hv. discriminate.
    }
    destruct (σproj !! a) as [vproj|] eqn:Hσproj_a; [|reflexivity].
    exfalso. apply Ha_not_proj.
    exact Ha.
  }
  rewrite decide_True by (
    apply elem_of_intersection; split;
    [ exact HvQ
    | rewrite atom_store_to_lvar_store_dom;
      unfold lvars_of_atoms; apply elem_of_map;
      exists a; split; [reflexivity|exact Ha] ]).
  exact Hlookup_eq.
Qed.

Lemma expr_result_msubst_back_lift_store_eq_agree_all e y
    (σproj σ : StoreT)
    (HlcQ : lc_lvars (tm_lvars e ∪ {[LVFree y]}))
    (HsubQ : lvars_fv (tm_lvars e ∪ {[LVFree y]}) ⊆ dom (σ : StoreT))
    (HlcR :
      lc_lvars ((tm_lvars e ∪ {[LVFree y]}) ∖
        dom (atom_store_to_lvar_store σproj : LStoreT)))
    (HsubR :
      lvars_fv ((tm_lvars e ∪ {[LVFree y]}) ∖
        dom (atom_store_to_lvar_store σproj : LStoreT)) ⊆ dom (σ : StoreT)) :
  store_restrict σproj (lvars_fv (tm_lvars e ∪ {[LVFree y]})) =
    store_restrict σ (lvars_fv (tm_lvars e ∪ {[LVFree y]})) ->
  lstore_on_mlsubst_back (tm_lvars e ∪ {[LVFree y]})
    (atom_store_to_lvar_store σproj)
    (lstore_on_lift_store
      ((tm_lvars e ∪ {[LVFree y]}) ∖
        dom (atom_store_to_lvar_store σproj : LStoreT))
      σ HlcR HsubR) =
  lstore_on_lift_store (tm_lvars e ∪ {[LVFree y]}) σ HlcQ HsubQ.
Proof.
  intros Hagree.
  apply lstore_on_mlsubst_back_lift_store.
  apply storeA_map_eq. intros v.
  rewrite !storeA_restrict_lookup.
  destruct (decide (v ∈ tm_lvars e ∪ {[LVFree y]})) as [HvQ|HvQ].
  2:{
    rewrite decide_False.
    - reflexivity.
    - intros HvBoth.
      apply elem_of_intersection in HvBoth as [HvQ' _]. contradiction.
  }
  destruct (decide (v ∈ (tm_lvars e ∪ {[LVFree y]}) ∩
      dom (atom_store_to_lvar_store σproj : LStoreT))) as [HvBoth|HvBoth].
  - apply elem_of_intersection in HvBoth as [_ Hvρ].
    rewrite atom_store_to_lvar_store_dom in Hvρ.
    unfold lvars_of_atoms in Hvρ.
    apply elem_of_map in Hvρ as [a [-> Haρ]].
    rewrite atom_store_to_lvar_store_lookup_free.
    rewrite lstore_lift_free_lookup_free.
    assert (HaQ : a ∈ lvars_fv (tm_lvars e ∪ {[LVFree y]})).
    { apply lvars_fv_elem. exact HvQ. }
    pose proof (f_equal (fun st : StoreT => st !! a) Hagree) as Hlook.
    change ((store_restrict σproj (lvars_fv (tm_lvars e ∪ {[LVFree y]}))
      : StoreT) !! a =
      (store_restrict σ (lvars_fv (tm_lvars e ∪ {[LVFree y]}))
      : StoreT) !! a) in Hlook.
    destruct (σproj !! a) as [vp|] eqn:Hσproj_a.
    2:{
      exfalso.
      apply elem_of_dom in Haρ as [vp Hvp].
      change (((σproj : StoreT) : gmap atom value) !! a = Some vp) in Hvp.
      change (((σproj : StoreT) : gmap atom value) !! a = None) in Hσproj_a.
      rewrite Hσproj_a in Hvp. discriminate.
    }
    assert (Hleft :
        (store_restrict σproj (lvars_fv (tm_lvars e ∪ {[LVFree y]}))
          : StoreT) !! a = Some vp).
    { apply storeA_restrict_lookup_some_2; [exact Hσproj_a|exact HaQ]. }
    rewrite Hleft in Hlook.
    destruct (σ !! a) as [vs|] eqn:Hσ_a.
    + assert (Hright :
	          (store_restrict σ (lvars_fv (tm_lvars e ∪ {[LVFree y]}))
	            : StoreT) !! a = Some vs).
	      { apply storeA_restrict_lookup_some_2; [exact Hσ_a|exact HaQ]. }
      rewrite Hright in Hlook. inversion Hlook. subst vs.
      rewrite decide_True.
      * change (((σproj : StoreT) : gmap atom value) !! a =
          ((σ : StoreT) : gmap atom value) !! a).
        transitivity (Some vp).
        -- exact Hσproj_a.
        -- symmetry. exact Hσ_a.
      * apply elem_of_intersection. split.
        -- exact HvQ.
        -- rewrite atom_store_to_lvar_store_dom.
           unfold lvars_of_atoms. apply elem_of_map.
           exists a. split; [reflexivity|exact Haρ].
	    + assert (Hright :
	          (store_restrict σ (lvars_fv (tm_lvars e ∪ {[LVFree y]}))
	            : StoreT) !! a = None).
	      {
        change (((store_restrict σ
          (lvars_fv (tm_lvars e ∪ {[LVFree y]})) : StoreT)
          : gmap atom value) !! a = None).
        apply storeA_restrict_lookup_none_l.
        change (((σ : StoreT) : gmap atom value) !! a = None) in Hσ_a.
        exact Hσ_a.
	      }
      rewrite Hright in Hlook. discriminate.
  - destruct (decide (v ∈ dom (atom_store_to_lvar_store σproj : LStoreT)))
      as [Hvρ|Hvρ].
    + exfalso. apply HvBoth.
      apply elem_of_intersection. split; assumption.
    + rewrite decide_False by exact HvBoth.
      apply not_elem_of_dom_1. exact Hvρ.
Qed.

Lemma expr_result_formula_at_fiber_witness
    D e y (m : WfWorldT) :
  tm_lvars e ⊆ D ->
  LVFree y ∉ D ->
  m ⊨ expr_result_formula_at D e (LVFree y) ->
  forall σ v,
    (m : WorldT) σ ->
    tm_eval_in_store (store_restrict σ (fv_tm e)) e v ->
    exists σv,
      (m : WorldT) σv /\
      store_restrict σv (lvars_fv D) =
        store_restrict σ (lvars_fv D) /\
      σv !! y = Some v.
Proof.
  intros HeD HyD Hmodels σ v Hσ Heval.
  unfold expr_result_formula_at in Hmodels.
  apply res_models_FFibVars_iff in Hmodels.
  destruct Hmodels as [Hscope [HlcD Hfib]].
  assert (HDm : lvars_fv D ⊆ world_dom (m : WorldT)).
  {
    apply (proj1 (formula_scoped_fibvars_iff m D
      (FAtom (expr_result_qual e (LVFree y))))) in Hscope as [HDm _].
    exact HDm.
  }
  destruct (res_fiber_from_projection_of_store m
    (lvars_fv D) σ HDm Hσ)
    as [mfib [Hproj Hσfib]].
  set (σproj := store_restrict σ (lvars_fv D)).
  pose proof (Hfib σproj mfib Hproj) as Hatom.
  pose proof Hatom as Hatom_model.
  unfold formula_msubst_store in Hatom. cbn [formula_mlsubst] in Hatom.
  unfold res_models in Hatom.
  cbn [formula_measure res_models_fuel qualifier_exact_denote
    expr_result_qual qual_msubst_store qual_mlsubst] in Hatom.
  destruct Hatom as [_ [HlcR [HsubR Hiff]]].
  assert (HlcQ : lc_lvars (tm_lvars e ∪ {[LVFree y]})).
  {
    intros z Hz. apply elem_of_union in Hz as [Hz|Hz].
    - exact (HlcD z (HeD _ Hz)).
    - apply elem_of_singleton in Hz as ->. exact I.
  }
  destruct Hproj as [Hproj_src Hfib_eq].
  assert (Hproj_dom : dom (σproj : StoreT) = lvars_fv D).
  {
    subst σproj.
	    change (dom ((store_restrict σ (lvars_fv D) : StoreT)
	      : gmap atom value) = lvars_fv D).
	    rewrite storeA_restrict_dom.
	    rewrite (wfworld_store_dom m σ Hσ).
	    apply set_eq. intros a. rewrite elem_of_intersection.
	    split.
	    - intros [_ Ha]. exact Ha.
	    - intros Ha. split; [exact (HDm a Ha)|exact Ha].
  }
  pose proof (expr_result_residual_singleton_on D e y σproj
    HlcD HeD HyD Hproj_dom) as HR_single.
  set (R := (tm_lvars e ∪ {[LVFree y]}) ∖
    dom (atom_store_to_lvar_store σproj : LStoreT)).
  assert (HlcR' : lc_lvars R).
  {
    subst R. intros z Hz.
    apply elem_of_difference in Hz as [Hz _].
    exact (HlcQ z Hz).
  }
  assert (Hsub_store : lvars_fv R ⊆ dom (({[y := v]} : StoreT))).
  {
    subst R. rewrite HR_single, lvars_fv_singleton_free.
    intros a Ha. apply elem_of_singleton in Ha as ->.
    change (y ∈ dom (({[y := v]} : StoreT) : gmap atom value)).
    eapply elem_of_dom_2. apply map_lookup_insert.
  }
  set (s := lstore_on_lift_store R ({[y := v]} : StoreT)
    HlcR' Hsub_store).
  assert (Hs_y : (lso_store s : LStoreT) !! LVFree y = Some v).
  {
    subst s.
    cbn [lstore_on_lift_store storeAO_store].
    change ((storeA_restrict (lstore_lift_free ({[y := v]} : StoreT)) R
      : LStoreT) !! LVFree y = Some v).
    apply storeA_restrict_lookup_some_2.
    - rewrite lstore_lift_free_lookup_free. apply map_lookup_insert.
    - subst R. rewrite HR_single. apply elem_of_singleton. reflexivity.
  }
  assert (Hinput_eq :
    storeA_restrict
      (lso_store (lstore_on_mlsubst_back (tm_lvars e ∪ {[LVFree y]})
        (atom_store_to_lvar_store σproj) s)) (tm_lvars e) =
    storeA_restrict (lstore_lift_free σ : LStoreT) (tm_lvars e)).
  {
    eapply expr_result_msubst_back_input_restrict_agree.
    - intros z Hz. exact (HlcD z (HeD _ Hz)).
    - intros a Ha.
      change (a ∈ dom (σ : gmap atom value)).
      rewrite (wfworld_store_dom m σ Hσ).
      apply HDm.
      apply lvars_fv_elem.
      apply HeD.
      apply lvars_fv_elem. exact Ha.
    - subst σproj.
	      rewrite storeA_restrict_restrict.
	      replace (lvars_fv D ∩ lvars_fv (tm_lvars e))
	        with (lvars_fv (tm_lvars e)).
	      + reflexivity.
	      + apply set_eq. intros a.
	        split.
	        * intros Ha.
	          apply elem_of_intersection. split; [|exact Ha].
	          apply lvars_fv_elem. apply HeD.
	          apply lvars_fv_elem. exact Ha.
	        * intros Ha.
	          apply elem_of_intersection in Ha as [_ Ha]. exact Ha.
  }
  assert (Hprop : expr_result_at_store e (LVFree y)
    (lso_store (lstore_on_mlsubst_back (tm_lvars e ∪ {[LVFree y]})
      (atom_store_to_lvar_store σproj) s))).
  {
    split.
    - intros HyE. apply HyD. apply HeD. exact HyE.
    - exists v. split.
      + unfold lstore_on_mlsubst_back.
      cbn [lso_store storeAO_store].
      change (((lso_store s : gmap logic_var value) ∪
        (storeA_restrict (atom_store_to_lvar_store σproj)
          (tm_lvars e ∪ {[LVFree y]}) : gmap logic_var value))
        !! LVFree y = Some v).
      rewrite lookup_union_l; [exact Hs_y|].
      apply storeA_restrict_lookup_none_l.
      rewrite atom_store_to_lvar_store_lookup_free.
      apply not_elem_of_dom.
      change (y ∉ dom (σproj : StoreT)).
      rewrite Hproj_dom.
      intros Hyfv. apply HyD. apply lvars_fv_elem. exact Hyfv.
      + apply (proj1 (expr_eval_in_store_restrict_lvars e
        (lso_store (lstore_on_mlsubst_back (tm_lvars e ∪ {[LVFree y]})
          (atom_store_to_lvar_store σproj) s))
        (tm_lvars e) v ltac:(intros z Hz; exact Hz))).
      rewrite Hinput_eq.
      apply (proj2 (expr_eval_in_store_restrict_lvars e
        (lstore_lift_free σ : LStoreT) (tm_lvars e) v
        ltac:(intros z Hz; exact Hz))).
      change (tm_eval_in_store σ e v).
      apply (proj1 (tm_eval_in_store_restrict_fv_exact σ e v)).
      exact Heval.
  }
  destruct (Hiff s) as [Hto_mem _].
  pose proof (Hto_mem Hprop) as Hmem.
  pose proof (lstore_in_lworld_on_singleton_free_lookup y R mfib
    HlcR' HsubR s ltac:(subst R; exact HR_single) Hmem)
    as [σv [Hσv_fib Hsy_eq]].
  change ((mfib : WorldT) = rawA_fiber (m : WorldT) σproj) in Hfib_eq.
  rewrite Hfib_eq in Hσv_fib.
  destruct Hσv_fib as [Hσv Hσv_proj].
  exists σv. split; [exact Hσv|]. split.
  - change (store_restrict σv (lvars_fv D) =
      store_restrict σ (lvars_fv D)).
    transitivity σproj.
    + replace (lvars_fv D) with (dom σproj) by exact Hproj_dom.
      exact Hσv_proj.
    + subst σproj. reflexivity.
  - transitivity ((lso_store s : LStoreT) !! LVFree y).
    + symmetry. exact Hsy_eq.
    + exact Hs_y.
Qed.

Lemma expr_result_formula_at_models_elim
    D e y (m : WfWorldT) :
  tm_lvars e ⊆ D ->
  LVFree y ∉ D ->
  m ⊨ expr_result_formula_at D e (LVFree y) ->
  forall σ, (m : WorldT) σ ->
    expr_result_at_store e (LVFree y) (lstore_lift_free σ).
Proof.
  intros HeD HyD Hmodels σ Hσ.
  unfold expr_result_formula_at in Hmodels.
  apply res_models_FFibVars_iff in Hmodels.
  destruct Hmodels as [Hscope [HlcD Hfib]].
  assert (HDm : lvars_fv D ⊆ world_dom (m : WorldT)).
  {
    apply (proj1 (formula_scoped_fibvars_iff m D
      (FAtom (expr_result_qual e (LVFree y))))) in Hscope as [HDm _].
    exact HDm.
  }
  destruct (res_fiber_from_projection_of_store m
    (lvars_fv D) σ HDm Hσ) as [mfib [Hproj Hσfib]].
  pose proof (Hfib (store_restrict σ (lvars_fv D)) mfib Hproj)
    as Hatom.
  pose proof (res_models_FAtom_store_holds _ _ Hatom σ Hσfib)
    as Hhold.
  unfold qualifier_holds_store, expr_result_qual,
    qual_msubst_store, qual_mlsubst in Hhold.
  cbn [qual_lvars qual_prop] in Hhold.
  destruct Hhold as [HlcR [HsubR Hres]].
  assert (Hproj_dom :
      dom (store_restrict σ (lvars_fv D) : StoreT) = lvars_fv D).
  {
    change (dom (store_restrict σ (lvars_fv D) : gmap atom value) =
      lvars_fv D).
	    rewrite storeA_restrict_dom.
	    rewrite (wfworld_store_dom m σ Hσ).
	    apply set_eq. intros a. rewrite elem_of_intersection.
	    split.
	    - intros [_ Ha]. exact Ha.
	    - intros Ha. split; [exact (HDm a Ha)|exact Ha].
	  }
  assert (HlcQ : lc_lvars (tm_lvars e ∪ {[LVFree y]})).
  {
    intros v Hv. apply elem_of_union in Hv as [Hv|Hv].
    - exact (HlcD v (HeD _ Hv)).
    - apply elem_of_singleton in Hv as ->.
      exact I.
  }
  assert (HsubQ : lvars_fv (tm_lvars e ∪ {[LVFree y]}) ⊆ dom (σ : StoreT)).
  {
    intros a Ha.
    change (a ∈ dom (σ : gmap atom value)).
    rewrite (wfworld_store_dom m σ Hσ).
	    unfold formula_scoped_in_world in Hscope.
	    apply Hscope.
	    rewrite formula_fv_fibvars, formula_fv_atom.
	    unfold expr_result_qual, qual_dom, qual_vars.
	    apply elem_of_union_r. exact Ha.
	  }
  assert (Hagree :
      store_restrict (store_restrict σ (lvars_fv D))
        (lvars_fv (tm_lvars e)) =
      store_restrict σ (lvars_fv (tm_lvars e))).
  {
    rewrite storeA_restrict_restrict.
    replace (lvars_fv D ∩ lvars_fv (tm_lvars e))
      with (lvars_fv (tm_lvars e)).
    + reflexivity.
    + apply set_eq. intros a. split.
      * intros Ha. apply elem_of_intersection. split; [|exact Ha].
        apply lvars_fv_elem. apply HeD. apply lvars_fv_elem. exact Ha.
      * intros Ha. apply elem_of_intersection in Ha as [_ Ha]. exact Ha.
  }
  assert (Hyproj : y ∉ dom (store_restrict σ (lvars_fv D) : StoreT)).
  {
    rewrite Hproj_dom. intros Hyfv. apply HyD.
    apply lvars_fv_elem. exact Hyfv.
  }
  pose proof (expr_result_msubst_back_lift_store_eq_agree e y
    (store_restrict σ (lvars_fv D)) σ
    HlcQ HsubQ HlcR HsubR Hagree Hyproj) as Heq.
  pose proof (f_equal lso_store Heq) as Heq_store.
  cbn [lstore_on_lift_store storeAO_store] in Heq_store.
  change (expr_result_at_store e (LVFree y)
    (lso_store (lstore_on_mlsubst_back
      (tm_lvars e ∪ {[LVFree y]})
      (atom_store_to_lvar_store
        (store_restrict σ (lvars_fv D)))
      (lstore_on_lift_store
        ((tm_lvars e ∪ {[LVFree y]}) ∖
          dom (atom_store_to_lvar_store
            (store_restrict σ (lvars_fv D) : StoreT)
            : LStoreT))
        σ HlcR HsubR)))) in Hres.
  rewrite Heq_store in Hres.
  destruct Hres as [Hyfresh [v [Hlookup Heval]]].
  split; [exact Hyfresh|].
  exists v. split.
  - apply storeA_restrict_lookup_some in Hlookup as [_ Hlookup].
    exact Hlookup.
	  - apply (proj1 (expr_eval_in_store_restrict_lvars e
	      (lstore_lift_free σ : LStoreT) (tm_lvars e ∪ {[LVFree y]})
	      v ltac:(intros a Ha; apply elem_of_union_l; exact Ha))).
	    exact Heval.
Qed.

Lemma expr_result_formula_at_ret_value_closed_result
    D v y (my : WfWorldT) :
  tm_lvars (tret v) ⊆ D ->
  LVFree y ∉ D ->
  fv_value v ⊆ world_dom (my : WorldT) ->
  wfworld_closed_on (fv_value v) my ->
  lc_value v ->
  my ⊨ expr_result_formula_at D (tret v) (LVFree y) ->
  wfworld_closed_on ({[y]} : aset) my.
Proof.
  intros HvD HyD Hvdom Hclosed_v Hv Hres σ Hσ.
  pose proof (expr_result_formula_at_models_elim
    D (tret v) y my HvD HyD Hres σ Hσ) as Hstore.
  destruct Hstore as [_ [vy [Hylook Heval]]].
  assert (Hylook_free : σ !! y = Some vy).
  {
    change (((lstore_lift_free σ : LStoreT) : gmap logic_var value)
      !! LVFree y = Some vy) in Hylook.
    rewrite lstore_lift_free_lookup_free in Hylook.
    exact Hylook.
  }
  change (tm_eval_in_store σ (tret v) vy) in Heval.
  pose proof (proj2 (tm_eval_in_store_restrict_fv_subset
    σ (tret v) vy (fv_value v) ltac:(cbn [fv_tm]; set_solver)) Heval)
    as Heval_restrict.
  assert (Hclosed_restrict : store_closed (store_restrict σ (fv_value v))).
  { eapply wfworld_closed_on_store_restrict_closed; eauto. }
  pose proof (tm_eval_in_store_ret_value_inv
    (store_restrict σ (fv_value v)) v vy
    Hclosed_restrict Hv Heval_restrict) as Hvy_eq.
  assert (Hdom_restrict :
      dom (store_restrict σ (fv_value v) : StoreT) = fv_value v).
  {
    change (dom (storeA_restrict σ (fv_value v) : gmap atom value) =
      fv_value v).
    rewrite storeA_restrict_dom.
    rewrite (wfworld_store_dom my σ Hσ).
    apply set_eq. intros a. set_solver.
  }
  split.
  - unfold closed_env. apply map_Forall_lookup_2.
    intros a va Hlook.
    apply storeA_restrict_lookup_some in Hlook as [Hay Hlook].
    replace a with y in Hlook by set_solver.
    assert (Hsome : Some va = Some vy).
    { transitivity (σ !! y); [symmetry; exact Hlook|exact Hylook_free]. }
    inversion Hsome. subst va.
    rewrite Hvy_eq.
    pose proof (msubst_fv_delete_value
      (store_restrict σ (fv_value v)) v (proj1 Hclosed_restrict))
      as Hfv.
    apply set_eq. intros x. split; [|set_solver].
    intros Hx.
    pose proof (Hfv x Hx) as Hx'.
    assert (Hxdom : x ∈ dom (store_restrict σ (fv_value v) : StoreT)).
    { rewrite Hdom_restrict. set_solver. }
    set_solver.
  - unfold lc_env. apply map_Forall_lookup_2.
    intros a va Hlook.
    apply storeA_restrict_lookup_some in Hlook as [Hay Hlook].
    replace a with y in Hlook by set_solver.
    assert (Hsome : Some va = Some vy).
    { transitivity (σ !! y); [symmetry; exact Hlook|exact Hylook_free]. }
    inversion Hsome. subst va.
    rewrite Hvy_eq.
    apply msubst_lc; [exact (proj2 Hclosed_restrict)|exact Hv].
Qed.

Lemma expr_result_formula_at_models_elim_covered
    D e y (m : WfWorldT) :
  tm_lvars e ∪ {[LVFree y]} ⊆ D ->
  m ⊨ expr_result_formula_at D e (LVFree y) ->
  forall σ, (m : WorldT) σ ->
    expr_result_at_store e (LVFree y) (lstore_lift_free σ).
Proof.
  intros HQD Hmodels σ Hσ.
  unfold expr_result_formula_at in Hmodels.
  apply res_models_FFibVars_iff in Hmodels.
  destruct Hmodels as [Hscope [HlcD Hfib]].
  assert (HDm : lvars_fv D ⊆ world_dom (m : WorldT)).
  {
    apply (proj1 (formula_scoped_fibvars_iff m D
      (FAtom (expr_result_qual e (LVFree y))))) in Hscope as [HDm _].
    exact HDm.
  }
  destruct (res_fiber_from_projection_of_store m
    (lvars_fv D) σ HDm Hσ) as [mfib [Hproj Hσfib]].
  pose proof (Hfib (store_restrict σ (lvars_fv D)) mfib Hproj)
    as Hatom.
  pose proof (res_models_FAtom_store_holds _ _ Hatom σ Hσfib)
    as Hhold.
  unfold qualifier_holds_store, expr_result_qual,
    qual_msubst_store, qual_mlsubst in Hhold.
  cbn [qual_lvars qual_prop] in Hhold.
  destruct Hhold as [HlcR [HsubR Hres]].
  assert (Hproj_dom :
      dom (store_restrict σ (lvars_fv D) : StoreT) = lvars_fv D).
  {
    change (dom (store_restrict σ (lvars_fv D) : gmap atom value) =
      lvars_fv D).
    rewrite storeA_restrict_dom.
    rewrite (wfworld_store_dom m σ Hσ).
    apply set_eq. intros a. rewrite elem_of_intersection.
    split.
    - intros [_ Ha]. exact Ha.
    - intros Ha. split; [exact (HDm a Ha)|exact Ha].
  }
  assert (HlcQ : lc_lvars (tm_lvars e ∪ {[LVFree y]})).
  { intros v Hv. exact (HlcD v (HQD _ Hv)). }
  assert (HsubQ : lvars_fv (tm_lvars e ∪ {[LVFree y]}) ⊆ dom (σ : StoreT)).
  {
    intros a Ha.
    change (a ∈ dom (σ : gmap atom value)).
    rewrite (wfworld_store_dom m σ Hσ).
    apply HDm. apply lvars_fv_elem.
    apply HQD. apply lvars_fv_elem. exact Ha.
  }
  assert (Hagree :
      store_restrict (store_restrict σ (lvars_fv D))
        (lvars_fv (tm_lvars e ∪ {[LVFree y]})) =
      store_restrict σ (lvars_fv (tm_lvars e ∪ {[LVFree y]}))).
  {
    rewrite storeA_restrict_restrict.
    replace (lvars_fv D ∩ lvars_fv (tm_lvars e ∪ {[LVFree y]}))
      with (lvars_fv (tm_lvars e ∪ {[LVFree y]})).
    - reflexivity.
    - apply set_eq. intros a. split.
      + intros Ha. apply elem_of_intersection. split; [|exact Ha].
        apply lvars_fv_elem. apply HQD. apply lvars_fv_elem. exact Ha.
      + intros Ha. apply elem_of_intersection in Ha as [_ Ha]. exact Ha.
  }
  pose proof (expr_result_msubst_back_lift_store_eq_agree_all e y
    (store_restrict σ (lvars_fv D)) σ
    HlcQ HsubQ HlcR HsubR Hagree) as Heq.
  pose proof (f_equal lso_store Heq) as Heq_store.
  cbn [lstore_on_lift_store storeAO_store] in Heq_store.
  change (expr_result_at_store e (LVFree y)
    (lso_store (lstore_on_mlsubst_back
      (tm_lvars e ∪ {[LVFree y]})
      (atom_store_to_lvar_store
        (store_restrict σ (lvars_fv D)))
      (lstore_on_lift_store
        ((tm_lvars e ∪ {[LVFree y]}) ∖
          dom (atom_store_to_lvar_store
            (store_restrict σ (lvars_fv D) : StoreT)
            : LStoreT))
        σ HlcR HsubR)))) in Hres.
  rewrite Heq_store in Hres.
  destruct Hres as [Hyfresh [v [Hlookup Heval]]].
  split; [exact Hyfresh|].
  exists v. split.
  - apply storeA_restrict_lookup_some in Hlookup as [_ Hlookup].
    exact Hlookup.
	  - apply (proj1 (expr_eval_in_store_restrict_lvars e
	      (lstore_lift_free σ : LStoreT) (tm_lvars e ∪ {[LVFree y]})
	      v ltac:(intros a Ha; apply elem_of_union_l; exact Ha))).
	    exact Heval.
Qed.

Lemma expr_result_formula_at_intro
    D e y (m : WfWorldT) :
  lc_lvars D ->
  tm_lvars e ⊆ D ->
  LVFree y ∉ D ->
  formula_scoped_in_world m (expr_result_formula_at D e (LVFree y)) ->
  (forall σ, (m : WorldT) σ ->
    expr_result_at_store e (LVFree y) (lstore_lift_free σ)) ->
  (forall σ v,
    (m : WorldT) σ ->
    tm_eval_in_store (store_restrict σ (fv_tm e)) e v ->
    exists σv,
      (m : WorldT) σv /\
      store_restrict σv (lvars_fv D) =
        store_restrict σ (lvars_fv D) /\
      σv !! y = Some v) ->
  m ⊨ expr_result_formula_at D e (LVFree y).
Proof.
  intros HlcD HeD HyD Hscope Hstores Hcomplete.
  unfold expr_result_formula_at.
  eapply res_models_FFibVars_intro; [exact Hscope|exact HlcD|].
  intros σproj mfib Hproj.
  unfold formula_msubst_store. cbn [formula_mlsubst].
  unfold res_models. cbn [formula_measure res_models_fuel].
  assert (Hproj_dom :
      dom (σproj : StoreT) = lvars_fv D).
  {
    destruct Hproj as [Hσproj _].
    pose proof (wfworld_store_dom (res_restrict m (lvars_fv D)) σproj
      Hσproj) as Hdom.
    change (dom (σproj : StoreT) =
      world_dom (res_restrict m (lvars_fv D) : WorldT)) in Hdom.
    rewrite Hdom, res_restrict_dom.
    apply (proj1 (formula_scoped_fibvars_iff m D
      (FAtom (expr_result_qual e (LVFree y))))) in Hscope as [HDm _].
    apply set_eq. intros a. rewrite elem_of_intersection. split.
    - intros [_ Ha]. exact Ha.
    - intros Ha. split; [exact (HDm a Ha)|exact Ha].
  }
  assert (HlcQ : lc_lvars (tm_lvars e ∪ {[LVFree y]})).
  {
    intros z Hz. apply elem_of_union in Hz as [Hz|Hz].
    - exact (HlcD z (HeD _ Hz)).
    - apply elem_of_singleton in Hz as ->. exact I.
  }
  pose proof (expr_result_residual_singleton_on D e y σproj
    HlcD HeD HyD Hproj_dom) as HR_single.
  set (R := (tm_lvars e ∪ {[LVFree y]}) ∖
    dom (atom_store_to_lvar_store σproj : LStoreT)).
  assert (HlcR : lc_lvars R).
  {
    subst R. intros z Hz.
    apply elem_of_difference in Hz as [Hz _].
    exact (HlcQ z Hz).
  }
  assert (HsubR : lvars_fv R ⊆ world_dom (mfib : WorldT)).
  {
    subst R. rewrite HR_single, lvars_fv_singleton_free.
    intros a Ha. apply elem_of_singleton in Ha as ->.
    pose proof Hproj as [_ Hfib_eq].
    change ((mfib : WorldT) = rawA_fiber (m : WorldT) σproj)
      in Hfib_eq.
    pose proof (f_equal world_dom Hfib_eq) as Hdom_fib.
    cbn [raw_world raw_worldA rawA_fiber world_dom] in Hdom_fib.
    rewrite Hdom_fib.
    unfold formula_scoped_in_world in Hscope.
    rewrite formula_fv_expr_result_formula_at in Hscope.
    apply Hscope. apply elem_of_union_r.
    apply lvars_fv_elem. apply elem_of_union_r.
    apply elem_of_singleton. reflexivity.
  }
  split.
  - unfold formula_scoped_in_world. rewrite formula_fv_atom.
    unfold expr_result_qual, qual_dom, qual_vars, qual_msubst_store,
      qual_mlsubst.
    cbn [qual_lvars].
    exact HsubR.
  - exists HlcR, HsubR. intros s.
    split.
    + intros Hprop.
      unfold qualifier_holds_store, expr_result_qual,
        qual_msubst_store, qual_mlsubst in Hprop.
      cbn [qual_lvars qual_prop] in Hprop.
      destruct Hprop as [_ [v [Hs_y Heval_back]]].
      destruct (wfA_ne _ (worldA_wf mfib)) as [τ Hτ].
      assert (Hinput_eq :
        storeA_restrict
          (lso_store (lstore_on_mlsubst_back (tm_lvars e ∪ {[LVFree y]})
            (atom_store_to_lvar_store σproj) s)) (tm_lvars e) =
        storeA_restrict (lstore_lift_free τ : LStoreT) (tm_lvars e)).
      {
        pose proof Hproj as [_ Hfib_eq].
        pose proof (res_fiber_from_projection_store_restrict m mfib
          (lvars_fv D) σproj τ Hproj Hτ) as Hτproj.
        eapply expr_result_msubst_back_input_restrict_agree.
        - intros z Hz. exact (HlcD z (HeD _ Hz)).
        - intros a Ha.
          change (a ∈ dom (τ : StoreT)).
          pose proof (wfworld_store_dom mfib τ Hτ) as Hτdom.
          change (dom (τ : StoreT) = world_dom (mfib : WorldT)) in Hτdom.
          rewrite Hτdom.
          apply (proj1 (formula_scoped_fibvars_iff m D
            (FAtom (expr_result_qual e (LVFree y))))) in Hscope as [HDm _].
          pose proof Hproj as [_ Hfib_eq'].
          change ((mfib : WorldT) = rawA_fiber (m : WorldT) σproj)
            in Hfib_eq'.
          pose proof (f_equal world_dom Hfib_eq') as Hdom_fib.
          cbn [raw_world raw_worldA rawA_fiber world_dom] in Hdom_fib.
          rewrite Hdom_fib.
          apply HDm. apply lvars_fv_elem. apply HeD.
          apply lvars_fv_elem. exact Ha.
        - rewrite <- Hτproj.
          rewrite storeA_restrict_restrict.
          replace (dom (σproj : StoreT) ∩ lvars_fv (tm_lvars e))
            with (lvars_fv (tm_lvars e)).
          + reflexivity.
          + rewrite Hproj_dom. apply set_eq. intros a. split.
            * intros Ha. apply elem_of_intersection. split; [|exact Ha].
              apply lvars_fv_elem. apply HeD.
              apply lvars_fv_elem. exact Ha.
            * intros Ha. apply elem_of_intersection in Ha as [_ Ha].
              exact Ha.
      }
      assert (Hevalτ :
          tm_eval_in_store (store_restrict τ (fv_tm e)) e v).
      {
        apply (proj2 (tm_eval_in_store_restrict_fv_exact τ e v)).
        change (expr_eval_in_store (lstore_lift_free τ) e v).
        apply (proj1 (expr_eval_in_store_restrict_lvars e
          (lstore_lift_free τ : LStoreT) (tm_lvars e) v
          ltac:(intros z Hz; exact Hz))).
        rewrite <- Hinput_eq.
        apply (proj2 (expr_eval_in_store_restrict_lvars e
          (lso_store (lstore_on_mlsubst_back
            (tm_lvars e ∪ {[LVFree y]})
            (atom_store_to_lvar_store σproj) s))
          (tm_lvars e) v ltac:(intros z Hz; exact Hz))).
        exact Heval_back.
      }
      assert (Hτm : (m : WorldT) τ).
      { eapply res_fiber_from_projection_store_source; eauto. }
      pose proof (Hcomplete τ v Hτm Hevalτ)
        as [σv [Hσv [HσvD Hσvy]]].
      assert (Hσv_fib : (mfib : WorldT) σv).
      {
        pose proof Hproj as [_ Hfib_eq].
        change ((mfib : WorldT) = rawA_fiber (m : WorldT) σproj)
          in Hfib_eq.
        rewrite Hfib_eq. split; [exact Hσv|].
        transitivity (store_restrict τ (lvars_fv D)).
        - replace (dom (σproj : StoreT)) with (lvars_fv D)
            by (symmetry; exact Hproj_dom).
          exact HσvD.
        - replace (lvars_fv D) with (dom (σproj : StoreT))
            by exact Hproj_dom.
          exact (res_fiber_from_projection_store_restrict
            m mfib (lvars_fv D) σproj τ Hproj Hτ).
      }
      assert (Hsub_store : lvars_fv R ⊆ dom (σv : StoreT)).
      {
        subst R. rewrite HR_single, lvars_fv_singleton_free.
        intros a Ha. apply elem_of_singleton in Ha as ->.
        change (y ∈ dom (σv : gmap atom value)).
        eapply elem_of_dom_2. exact Hσvy.
      }
      set (sv := lstore_on_lift_store R σv HlcR Hsub_store).
      assert (Hs_y_s : (lso_store s : LStoreT) !! LVFree y = Some v).
      {
        unfold lstore_on_mlsubst_back in Hs_y.
        cbn [lso_store storeAO_store] in Hs_y.
        change (((lso_store s : gmap logic_var value) ∪
          (storeA_restrict (atom_store_to_lvar_store σproj)
            (tm_lvars e ∪ {[LVFree y]}) : gmap logic_var value))
          !! LVFree y = Some v) in Hs_y.
        rewrite lookup_union_l in Hs_y; [exact Hs_y|].
        apply storeA_restrict_lookup_none_l.
        rewrite atom_store_to_lvar_store_lookup_free.
        apply not_elem_of_dom.
        intros Hyfv. apply HyD. apply lvars_fv_elem.
        change (y ∈ dom (σproj : StoreT)) in Hyfv.
        rewrite Hproj_dom in Hyfv. exact Hyfv.
      }
      assert (Hsv_eq : sv = s).
      {
        apply lstore_on_ext. apply storeA_map_eq. intros z.
        destruct (decide (z ∈ R)) as [HzR|HzR].
        - assert (HzEq : z = LVFree y).
          {
            subst R. rewrite HR_single in HzR.
            apply elem_of_singleton in HzR. exact HzR.
          }
          subst z.
          cbn [lstore_on_lift_store storeAO_store].
          transitivity (Some v).
          + apply storeA_restrict_lookup_some_2.
            * rewrite lstore_lift_free_lookup_free. exact Hσvy.
            * exact HzR.
          + symmetry. exact Hs_y_s.
        - transitivity (@None value).
          + cbn [lstore_on_lift_store storeAO_store].
            apply storeA_restrict_lookup_none_r. exact HzR.
          + symmetry.
            apply not_elem_of_dom_1.
            rewrite lso_dom. exact HzR.
      }
      rewrite <- Hsv_eq.
      exact (lstore_in_lworld_on_lift_store_of_world
        R mfib HlcR HsubR σv Hsub_store Hσv_fib).
    + intros Hmem.
      pose proof (lstore_in_lworld_on_singleton_free_lookup y R mfib
        HlcR HsubR s ltac:(subst R; exact HR_single) Hmem)
        as [τ [Hτ Hs_y]].
      assert (Hτm : (m : WorldT) τ).
      { eapply res_fiber_from_projection_store_source; eauto. }
      pose proof (Hstores τ Hτm) as Hτres.
      destruct Hτres as [Hyfresh [v [Hτy Hevalτ]]].
      split.
      * intros HyE. apply HyD. apply HeD. exact HyE.
      * exists v. split.
        -- unfold lstore_on_mlsubst_back.
           cbn [lso_store storeAO_store].
           change (((lso_store s : gmap logic_var value) ∪
             (storeA_restrict (atom_store_to_lvar_store σproj)
               (tm_lvars e ∪ {[LVFree y]}) : gmap logic_var value))
             !! LVFree y = Some v).
           rewrite lookup_union_l.
           ++ transitivity (τ !! y); [exact Hs_y|].
              rewrite lstore_lift_free_lookup_free in Hτy.
              exact Hτy.
           ++ apply storeA_restrict_lookup_none_l.
              rewrite atom_store_to_lvar_store_lookup_free.
              apply not_elem_of_dom.
              intros Hyfv. apply HyD. apply lvars_fv_elem.
              change (y ∈ dom (σproj : StoreT)) in Hyfv.
              rewrite Hproj_dom in Hyfv. exact Hyfv.
        -- apply (proj1 (expr_eval_in_store_restrict_lvars e
             (lso_store (lstore_on_mlsubst_back (tm_lvars e ∪ {[LVFree y]})
               (atom_store_to_lvar_store σproj) s))
             (tm_lvars e) v ltac:(intros z Hz; exact Hz))).
           assert (Hinput_eq :
             storeA_restrict
               (lso_store (lstore_on_mlsubst_back (tm_lvars e ∪ {[LVFree y]})
                 (atom_store_to_lvar_store σproj) s)) (tm_lvars e) =
             storeA_restrict (lstore_lift_free τ : LStoreT) (tm_lvars e)).
           {
             eapply expr_result_msubst_back_input_restrict_agree.
             - intros z Hz. exact (HlcD z (HeD _ Hz)).
             - intros a Ha.
               change (a ∈ dom (τ : StoreT)).
               pose proof (wfworld_store_dom mfib τ Hτ) as Hτdom.
               change (dom (τ : StoreT) = world_dom (mfib : WorldT)) in Hτdom.
               rewrite Hτdom.
               pose proof Hproj as [_ Hfib_eq].
               change ((mfib : WorldT) = rawA_fiber (m : WorldT) σproj)
                 in Hfib_eq.
               pose proof (f_equal world_dom Hfib_eq) as Hdom_fib.
               cbn [raw_world raw_worldA rawA_fiber world_dom] in Hdom_fib.
               rewrite Hdom_fib.
               apply (proj1 (formula_scoped_fibvars_iff m D
                 (FAtom (expr_result_qual e (LVFree y))))) in Hscope as [HDm _].
               apply HDm. apply lvars_fv_elem. apply HeD.
               apply lvars_fv_elem. exact Ha.
	             - pose proof (res_fiber_from_projection_store_restrict
                 m mfib (lvars_fv D) σproj τ Hproj Hτ) as Hτproj.
               rewrite <- Hτproj.
               rewrite storeA_restrict_restrict.
               replace (dom (σproj : StoreT) ∩ lvars_fv (tm_lvars e))
                 with (lvars_fv (tm_lvars e)).
	               + reflexivity.
	               + rewrite Hproj_dom. apply set_eq. intros a. split.
	                 * intros Ha. apply elem_of_intersection. split; [|exact Ha].
	                   apply lvars_fv_elem. apply HeD.
	                   apply lvars_fv_elem. exact Ha.
	                 * intros Ha. apply elem_of_intersection in Ha as [_ Ha].
	                   exact Ha.
	           }
           rewrite Hinput_eq.
           apply (proj2 (expr_eval_in_store_restrict_lvars e
             (lstore_lift_free τ : LStoreT) (tm_lvars e) v
             ltac:(intros z Hz; exact Hz))).
           change (tm_eval_in_store τ e v).
           exact Hevalτ.
Unshelve.
all: try assumption.
all: try typeclasses eauto.
Qed.

Lemma expr_result_formula_at_fiber_stable
    X D e y (m mfib : WfWorldT) σX :
  X ⊆ lvars_fv D ->
  tm_lvars e ⊆ D ->
  LVFree y ∉ D ->
  res_fiber_from_projection m X σX mfib ->
  m ⊨ expr_result_formula_at D e (LVFree y) ->
  mfib ⊨ expr_result_formula_at D e (LVFree y).
Proof.
  intros HXD HeD HyD Hproj Hres.
  pose proof Hres as Hres_scope.
  unfold expr_result_formula_at in Hres_scope.
  apply res_models_FFibVars_iff in Hres_scope as [Hscope [HlcD _]].
  assert (Hdom_fib : world_dom (mfib : WorldT) = world_dom (m : WorldT)).
  {
    destruct Hproj as [_ Hfib_eq].
    pose proof (f_equal world_dom Hfib_eq) as Hdom.
    cbn [raw_fiber rawA_fiber world_dom worldA_dom] in Hdom.
    exact Hdom.
  }
  eapply expr_result_formula_at_intro.
  - exact HlcD.
  - exact HeD.
  - exact HyD.
  - unfold formula_scoped_in_world in *.
    intros a Ha. rewrite Hdom_fib. exact (Hscope a Ha).
  - intros τ Hτ.
    eapply expr_result_formula_at_models_elim; eauto.
    eapply res_fiber_from_projection_store_source; eauto.
  - intros τ v Hτ Heval.
    assert (Hτm : (m : WorldT) τ).
    { eapply res_fiber_from_projection_store_source; eauto. }
    destruct (expr_result_formula_at_fiber_witness
      D e y m HeD HyD Hres τ v Hτm Heval)
      as [τv [Hτv_m [HτvD Hyv]]].
    exists τv. split.
    + pose proof Hproj as [_ Hfib_eq].
      change ((mfib : WorldT) = raw_fiber (m : WorldT) σX) in Hfib_eq.
      rewrite Hfib_eq. split; [exact Hτv_m|].
      pose proof (res_fiber_from_projection_store_restrict
        m mfib X σX τ Hproj Hτ) as HτX.
      transitivity (store_restrict τ (dom (σX : StoreT))); [|exact HτX].
      eapply storeA_restrict_eq_mono; [|exact HτvD].
      intros a Ha.
      apply HXD.
      eapply res_fiber_from_projection_store_dom_subset; eauto.
    + split; [exact HτvD|exact Hyv].
Qed.

Lemma expr_result_formula_at_of_result_extends_on
    D e x F (m mx : WfWorldT) :
  lc_lvars D ->
  tm_lvars e ⊆ D ->
  LVFree x ∉ D ->
  lvars_fv D ⊆ world_dom (m : WorldT) ->
  expr_result_extension_witness_on (lvars_fv D) e x F ->
  res_extend_by m F mx ->
  expr_total_on_atom_world e m ->
  mx ⊨ expr_result_formula_at D e (LVFree x).
Proof.
  intros HlcD HeD HxD HDm HF Hext Htotal.
  destruct HF as [HfvX HxX [Hin Hout] Hrel].
  assert (HxX' : x ∉ lvars_fv D).
  {
    intros Hx.
    apply HxD. apply lvars_fv_elem. exact Hx.
  }
  assert (HfvD : fv_tm e ⊆ lvars_fv D).
  {
    intros a Ha.
    apply (proj2 (lvars_fv_elem D a)).
    apply HeD.
    apply (proj1 (lvars_fv_elem (tm_lvars e) a)).
    rewrite tm_lvars_fv. exact Ha.
  }
  eapply expr_result_formula_at_intro; eauto.
  - unfold formula_scoped_in_world.
    rewrite formula_fv_expr_result_formula_at.
    intros a Ha.
    denotation_regular_res_extend_dom.
    change (world_dom (mx : WorldT) =
      world_dom (m : WorldT) ∪ ext_out F) in Hdom_ext.
    rewrite Hdom_ext, Hout.
    apply elem_of_union in Ha as [HaD|HaQ].
    + apply elem_of_union_l. exact (HDm a HaD).
    + apply lvars_fv_elem in HaQ.
      apply elem_of_union in HaQ as [HaE|Hax].
      * apply elem_of_union_l. apply HDm.
        apply lvars_fv_elem. apply HeD. exact HaE.
      * apply elem_of_singleton in Hax. inversion Hax. subst a.
        apply elem_of_union_r. apply elem_of_singleton. reflexivity.
  - intros σ Hσmx.
    apply (proj1 (resA_extend_by_store_iff m F mx σ Hext)) in Hσmx.
    destruct Hσmx as [σm [we [σe [Hσm [HFrel [Hσe ->]]]]]].
    assert (Hσe_dom : dom (σe : StoreT) = {[x]}).
    {
      pose proof (res_extend_rel_store_dom m mx F σm we σe
        Hext Hσm
        ltac:(change (store_restrict σm (extA_in F)) with
          (store_restrict σm (ext_in F)); exact HFrel)
        Hσe) as Hdom.
      change (extA_out F) with (ext_out F) in Hdom.
      rewrite Hout in Hdom. exact Hdom.
    }
    assert (Hinput_dom :
        dom (store_restrict σm (ext_in F) : StoreT) = ext_in F).
    {
      eapply extA_projection_dom.
      - apply resA_extend_by_applicable in Hext. exact Hext.
      - exact Hσm.
    }
    assert (Htotal_base :
        exists u, tm_eval_in_store (store_restrict σm (lvars_fv D)) e u).
    {
      unfold expr_total_on_atom_world, expr_total_on in Htotal.
      destruct Htotal as [_ Htotal_eval].
      specialize (Htotal_eval (lstore_lift_free σm)
        ltac:(exists σm; split; [exact Hσm|reflexivity])).
      apply must_terminating_reaches_result in Htotal_eval as [u Hu].
      exists u.
      apply (proj2 (tm_eval_in_store_restrict_fv_subset
        σm e u (lvars_fv D) HfvD)).
      exact Hu.
    }
    pose proof (expr_result_extension_apply_total_iff_on
      (lvars_fv D) e x F (store_restrict σm (ext_in F)) we
      {| expr_result_extension_witness_on_fv := HfvX;
         expr_result_extension_witness_on_fresh := HxX;
         expr_result_extension_witness_on_shape := conj Hin Hout;
         expr_result_extension_witness_on_rel := Hrel |}
      (eq_trans Hinput_dom Hin)
      HFrel
      ltac:(rewrite Hin; exact Htotal_base)
      σe) as Hσe_iff.
    apply Hσe_iff in Hσe as [u [Heval_u ->]].
    split.
    + intros Hxin.
      apply HxD. apply HeD. exact Hxin.
	    + exists u. split.
      * change (((lstore_lift_free
          (σm ∪ ({[x := u]} : StoreT)) : LStoreT) : gmap logic_var value)
          !! LVFree x = Some u).
	        rewrite lstore_lift_free_lookup_free.
	        change ((((σm : StoreT) ∪ ({[x := u]} : StoreT)) : gmap atom value)
	          !! x = Some u).
        apply map_lookup_union_Some_raw. right.
        split.
        -- apply not_elem_of_dom.
           exact (res_extend_by_singleton_output_notin_base_store
             m mx F x σm Hext Hout Hσm).
        -- apply map_lookup_insert.
      * change (tm_eval_in_store (σm ∪ ({[x := u]} : StoreT)) e u).
        assert (Hrestrict_u :
            store_restrict ((σm : StoreT) ∪ ({[x := u]} : StoreT))
              (lvars_fv D) =
            store_restrict σm (lvars_fv D)).
        {
          apply storeA_restrict_union_ignore_r.
          change (dom (({[x := u]} : StoreT) : gmap atom value) ##
            lvars_fv D).
          pose proof (dom_singleton_L (M:=gmap atom) x u) as Hdom_single.
          change (dom (({[x := u]} : StoreT) : gmap atom value) = {[x]})
            in Hdom_single.
          rewrite Hdom_single. set_solver.
        }
	        apply (proj1 (tm_eval_in_store_restrict_fv_subset
	          ((σm : StoreT) ∪ ({[x := u]} : StoreT)) e u
	          (lvars_fv D) HfvD)).
        rewrite Hrestrict_u.
        rewrite <- Hin. exact Heval_u.
  - intros σ v Hσmx Heval.
    apply (proj1 (resA_extend_by_store_iff m F mx σ Hext)) in Hσmx.
    destruct Hσmx as [σm [we [σe [Hσm [HFrel [Hσe ->]]]]]].
    assert (Hσe_dom : dom (σe : StoreT) = {[x]}).
    {
      pose proof (res_extend_rel_store_dom m mx F σm we σe
        Hext Hσm
        ltac:(change (store_restrict σm (extA_in F)) with
          (store_restrict σm (ext_in F)); exact HFrel)
        Hσe) as Hdom.
      change (extA_out F) with (ext_out F) in Hdom.
      rewrite Hout in Hdom. exact Hdom.
    }
    assert (Hinput_dom :
        dom (store_restrict σm (ext_in F) : StoreT) = ext_in F).
    {
      eapply extA_projection_dom.
      - apply resA_extend_by_applicable in Hext. exact Hext.
      - exact Hσm.
    }
    assert (Heval_input :
        tm_eval_in_store (store_restrict σm (lvars_fv D)) e v).
    {
      assert (Hrestrict :
          store_restrict ((σm : StoreT) ∪ σe) (fv_tm e) =
          store_restrict σm (fv_tm e)).
      {
        apply storeA_restrict_union_ignore_r.
	        change (dom (σe : StoreT) ## fv_tm e).
	        rewrite Hσe_dom. set_solver.
	      }
      change (tm_eval_in_store
        (store_restrict ((σm : StoreT) ∪ σe) (fv_tm e)) e v) in Heval.
      rewrite Hrestrict in Heval.
      apply (proj2 (tm_eval_in_store_restrict_fv_subset
        σm e v (lvars_fv D) HfvD)).
      apply (proj1 (tm_eval_in_store_restrict_fv_subset
        σm e v (fv_tm e) ltac:(set_solver))).
      exact Heval.
    }
    assert (Hσm_dom_fv :
        dom (store_restrict σm (ext_in F) : StoreT) = lvars_fv D).
    { exact (eq_trans Hinput_dom Hin). }
    assert (Hwe_v : (we : WorldT) ({[x := v]} : StoreT)).
    {
      eapply expr_result_extension_apply_total_store_on.
      - exact {| expr_result_extension_witness_on_fv := HfvX;
                 expr_result_extension_witness_on_fresh := HxX;
                 expr_result_extension_witness_on_shape := conj Hin Hout;
                 expr_result_extension_witness_on_rel := Hrel |}.
	      - exact Hσm_dom_fv.
	      - exact HFrel.
      - change (tm_eval_in_store (store_restrict σm (ext_in F)) e v).
        rewrite Hin. exact Heval_input.
	    }
    set (σv := (σm : StoreT) ∪ ({[x := v]} : StoreT)).
    exists σv. split.
    + apply (proj2 (resA_extend_by_store_iff m F mx σv Hext)).
      exists σm, we, ({[x := v]} : StoreT).
      split; [exact Hσm|]. split; [exact HFrel|].
      split; [exact Hwe_v|reflexivity].
	    + split.
      * transitivity (store_restrict σm (lvars_fv D)).
        -- subst σv. apply storeA_restrict_union_ignore_r.
           change (dom (({[x := v]} : StoreT) : gmap atom value) ##
             lvars_fv D).
           pose proof (dom_singleton_L (M:=gmap atom) x v) as Hdom_single.
           change (dom (({[x := v]} : StoreT) : gmap atom value) = {[x]})
             in Hdom_single.
           rewrite Hdom_single. set_solver.
        -- symmetry. apply storeA_restrict_union_ignore_r.
           change (dom (σe : StoreT) ## lvars_fv D).
           rewrite Hσe_dom. set_solver.
      * change ((((σm : StoreT) ∪ ({[x := v]} : StoreT)) : gmap atom value)
          !! x = Some v).
        apply map_lookup_union_Some_raw. right.
        split.
        -- apply not_elem_of_dom.
           exact (res_extend_by_singleton_output_notin_base_store
             m mx F x σm Hext Hout Hσm).
	        -- apply map_lookup_insert.
	Qed.

Lemma expr_result_formula_at_coarsen_domain
    Dsmall Dbig e y (m : WfWorldT) :
  Dsmall ⊆ Dbig ->
  tm_lvars e ⊆ Dsmall ->
  LVFree y ∉ Dbig ->
  m ⊨ expr_result_formula_at Dbig e (LVFree y) ->
  m ⊨ expr_result_formula_at Dsmall e (LVFree y).
Proof.
  intros Hsmall_big He_small Hy_big Hbig.
  assert (Hy_small : LVFree y ∉ Dsmall) by set_solver.
  assert (He_big : tm_lvars e ⊆ Dbig) by set_solver.
  pose proof Hbig as Hbig_scope.
  unfold expr_result_formula_at in Hbig_scope.
  apply res_models_FFibVars_iff in Hbig_scope
    as [Hscope_big [Hlc_big _]].
  assert (Hlc_small : lc_lvars Dsmall).
  { intros z Hz. exact (Hlc_big z (Hsmall_big _ Hz)). }
  eapply expr_result_formula_at_intro; eauto.
  - unfold formula_scoped_in_world.
    rewrite formula_fv_expr_result_formula_at.
    intros a Ha.
    unfold formula_scoped_in_world in Hscope_big.
    rewrite formula_fv_fibvars, formula_fv_atom in Hscope_big.
    unfold expr_result_qual, qual_dom, qual_vars in Hscope_big.
    apply Hscope_big.
    apply elem_of_union in Ha as [Ha|Ha].
    + apply elem_of_union_l.
      apply lvars_fv_elem.
      apply Hsmall_big.
      apply lvars_fv_elem. exact Ha.
    + apply elem_of_union_r. exact Ha.
  - intros σ Hσ.
    eapply expr_result_formula_at_models_elim; eauto.
  - intros σ v Hσ Heval.
    destruct (expr_result_formula_at_fiber_witness
      Dbig e y m He_big Hy_big Hbig σ v Hσ Heval)
      as [σv [Hσv [Hσv_big Hyv]]].
    exists σv. split; [exact Hσv|]. split; [|exact Hyv].
    eapply storeA_restrict_eq_mono; [|exact Hσv_big].
    intros a Ha.
    apply lvars_fv_elem.
    apply Hsmall_big.
    apply lvars_fv_elem. exact Ha.
Qed.

Lemma expr_result_formula_at_of_result_extends_on_coarsen
    Dsmall X e x F (m mx : WfWorldT) :
  lc_lvars Dsmall ->
  tm_lvars e ⊆ Dsmall ->
  Dsmall ⊆ lvars_of_atoms X ->
  LVFree x ∉ lvars_of_atoms X ->
  X ⊆ world_dom (m : WorldT) ->
  expr_result_extension_witness_on X e x F ->
  res_extend_by m F mx ->
  expr_total_on_atom_world e m ->
  mx ⊨ expr_result_formula_at Dsmall e (LVFree x).
Proof.
  intros Hlc_small He_small Hsmall_big Hx_big HXm HF Hext Htotal.
  eapply expr_result_formula_at_coarsen_domain.
  - exact Hsmall_big.
  - exact He_small.
  - exact Hx_big.
  - eapply expr_result_formula_at_of_result_extends_on.
    + intros v Hv.
      destruct v as [k|a]; [|exact I].
      unfold lvars_of_atoms in Hv.
      apply elem_of_map in Hv as [a [Ha _]]. discriminate.
    + intros v Hv. exact (Hsmall_big _ (He_small _ Hv)).
    + exact Hx_big.
    + rewrite lvars_fv_of_atoms. exact HXm.
    + rewrite lvars_fv_of_atoms. exact HF.
    + exact Hext.
    + exact Htotal.
Qed.


End TypeDenote.
