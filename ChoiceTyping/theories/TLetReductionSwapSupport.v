(** * ChoiceTyping.TLetReductionSwapSupport

    Fuel-level and model-level reduction lemmas for the [tlet] soundness case.
    The final semantic wrappers stay in [TLetDenotation]. *)

From CoreLang Require Import Instantiation InstantiationProps OperationalProps BasicTypingProps
  LocallyNamelessProps StrongNormalization Sugar.
From ChoiceTyping Require Import TLetReductionFuelSupport
  Naming ResultWorldBridge ResultWorldExprContFamily.
From ChoiceType Require Import BasicStore LocallyNamelessProps DenotationRefinement.

Import Tactics.

(** Swap and substitution helpers for the [tlet] reduction proof. *)
(** Swap, support, and family-rename helpers for the [tlet] reduction proof. *)
Lemma msubst_tapp_tm σ ef vx :
  m{σ} (tapp_tm ef vx) = tapp_tm (m{σ} ef) (m{σ} vx).
Proof.
  induction ef; simpl.
  - rewrite msubst_tapp, msubst_ret. reflexivity.
  - rewrite !msubst_lete. rewrite IHef2. reflexivity.
  - rewrite msubst_lete, msubst_tprim.
    rewrite msubst_tapp.
    rewrite (msubst_fresh σ (vbvar 0)) by set_solver.
    cbn [tapp_tm].
    rewrite msubst_tprim.
    reflexivity.
  - rewrite msubst_lete, msubst_tapp.
    rewrite msubst_tapp.
    rewrite (msubst_fresh σ (vbvar 0)) by set_solver.
    cbn [tapp_tm].
    rewrite msubst_tapp.
    reflexivity.
  - rewrite msubst_lete, msubst_tmatch.
    rewrite msubst_tapp.
    rewrite (msubst_fresh σ (vbvar 0)) by set_solver.
    cbn [tapp_tm].
    rewrite msubst_tmatch.
    reflexivity.
Qed.

Lemma msubst_fvar_store_swap_lookup σ x y v :
  closed_env σ →
  σ !! y = Some v →
  m{store_swap x y σ} (vfvar x) = m{σ} (vfvar y).
Proof.
  intros Hclosed Hlookup.
  rewrite (msubst_fvar_lookup_closed σ y v Hclosed Hlookup).
  rewrite (msubst_fvar_lookup_closed (store_swap x y σ) x v).
  - reflexivity.
  - apply closed_env_store_swap. exact Hclosed.
  - change (store_swap x y σ !! x = Some v).
    rewrite store_swap_lookup_inv.
    replace (atom_swap x y x) with y
      by (unfold atom_swap; repeat destruct decide; congruence).
    exact Hlookup.
Qed.

Lemma msubst_tret_fvar_store_swap_lookup σ x y v :
  closed_env σ →
  σ !! y = Some v →
  m{store_swap x y σ} (tret (vfvar x)) = m{σ} (tret (vfvar y)).
Proof.
  intros Hclosed Hlookup.
  rewrite !msubst_ret.
  rewrite (msubst_fvar_store_swap_lookup σ x y v Hclosed Hlookup).
  reflexivity.
Qed.

Lemma msubst_tapp_tm_fvar_store_swap_lookup σ e x y v :
  closed_env σ →
  σ !! y = Some v →
  x ∉ fv_tm e →
  y ∉ fv_tm e →
  m{store_swap x y σ} (tapp_tm e (vfvar x)) =
  m{σ} (tapp_tm e (vfvar y)).
Proof.
  intros Hclosed Hlookup Hx Hy.
  rewrite !msubst_tapp_tm.
  rewrite (msubst_store_swap_fresh tm x y σ e) by assumption.
  rewrite (msubst_fvar_store_swap_lookup σ x y v Hclosed Hlookup).
  reflexivity.
Qed.

Lemma aset_swap_fresh_union_singleton x y D :
  x ∉ D →
  y ∉ D →
  aset_swap x y (D ∪ {[y]}) = D ∪ {[x]}.
Proof.
  intros Hx Hy. apply set_eq. intros z.
  rewrite elem_of_aset_swap, !elem_of_union, !elem_of_singleton.
  unfold atom_swap.
  repeat destruct decide; set_solver.
Qed.

Lemma store_restrict_swap_fresh_union_singleton (σ : Store) x y D :
  x ∉ D →
  y ∉ D →
  store_restrict (store_swap x y σ) (D ∪ {[x]}) =
  store_swap x y (store_restrict σ (D ∪ {[y]})).
Proof.
  intros Hx Hy.
  rewrite <- (aset_swap_fresh_union_singleton x y D Hx Hy).
  apply store_restrict_swap.
Qed.

Lemma store_swap_insert_fresh (σ : gmap atom value) x y z v :
  z ≠ x →
  z ≠ y →
  store_swap (V:=value) x y (<[z := v]> σ : gmap atom value) =
  (<[z := v]> (store_swap (V:=value) x y σ) : gmap atom value).
Proof.
  intros Hzx Hzy.
  unfold store_swap.
  rewrite kmap_insert.
  - rewrite atom_swap_fresh by congruence. reflexivity.
  - apply atom_swap_inj.
Qed.

Lemma let_result_world_on_tret_fvar_swap
    D x y ν (m : WfWorld)
    Hfresh_src Hresult_src Hfresh_tgt Hresult_tgt :
  x ∉ D →
  y ∉ D →
  ν ∉ D ∪ {[x]} ∪ {[y]} →
  world_dom (m : World) = D ∪ {[y]} →
  world_closed_on (D ∪ {[y]}) m →
  let_result_world_on (tret (vfvar x)) ν (res_swap x y m)
    Hfresh_src Hresult_src =
  res_swap x y
    (let_result_world_on (tret (vfvar y)) ν m
      Hfresh_tgt Hresult_tgt).
Proof.
  intros Hx Hy Hν Hdom Hclosed.
  assert (Hνx : ν ≠ x) by set_solver.
  assert (Hνy : ν ≠ y) by set_solver.
  apply wfworld_ext. apply world_ext.
  - simpl. rewrite Hdom, !aset_swap_union, !aset_swap_singleton.
    replace (atom_swap x y y) with x
      by (unfold atom_swap; repeat destruct decide; congruence).
    rewrite aset_swap_fresh by set_solver.
    rewrite atom_swap_fresh by set_solver.
    set_solver.
  - intros σ. simpl. split.
    + intros [σ0 [vx [Hσ0 [Hsteps ->]]]].
      destruct Hσ0 as [σm [Hσm Hswap]]. subst σ0.
      assert (Hy_dom : y ∈ dom σm).
      { rewrite (wfworld_store_dom m σm Hσm), Hdom. set_solver. }
      apply elem_of_dom in Hy_dom as [vy Hlookup_y].
      assert (Hclosed_y : closed_env (store_restrict σm {[y]})).
      {
        replace (store_restrict σm {[y]}) with
          (store_restrict (store_restrict σm (D ∪ {[y]})) {[y]}).
        - apply closed_env_restrict. exact (proj1 (Hclosed σm Hσm)).
        - store_norm. replace ((D ∪ {[y]}) ∩ {[y]}) with ({[y]} : aset) by set_solver.
          reflexivity.
      }
      assert (Hlookup_y_restrict :
        store_restrict σm {[y]} !! y = Some vy).
      { rewrite store_restrict_lookup, decide_True by set_solver. exact Hlookup_y. }
      assert (Hclosed_x : closed_env
        (store_restrict (store_swap x y σm) {[x]})).
      {
        replace ({[x]} : aset) with ((∅ : aset) ∪ {[x]}) by set_solver.
        rewrite store_restrict_swap_fresh_union_singleton with (D := ∅)
          by (try apply not_elem_of_empty).
        replace ((∅ : aset) ∪ {[y]}) with ({[y]} : aset) by set_solver.
        apply closed_env_store_swap. exact Hclosed_y.
      }
      assert (Hlookup_x_restrict :
        store_restrict (store_swap x y σm) {[x]} !! x = Some vy).
      {
        rewrite store_restrict_lookup, decide_True by set_solver.
        rewrite store_swap_lookup_inv.
        replace (atom_swap x y x) with y
          by (unfold atom_swap; repeat destruct decide; congruence).
        exact Hlookup_y.
      }
      change (m{store_restrict (store_swap x y σm) {[x]}} (tret (vfvar x)) →*
        tret vx) in Hsteps.
      rewrite (msubst_ret_fvar_lookup_closed _ x vy Hclosed_x Hlookup_x_restrict) in Hsteps.
      pose proof (value_steps_self vy (tret vx) Hsteps) as Heq.
      inversion Heq. subst vx.
      exists (<[ν := vy]> σm). split.
      * exists σm, vy. repeat split; eauto.
        change (m{store_restrict σm {[y]}} (tret (vfvar y)) →* tret vy).
        rewrite (msubst_ret_fvar_lookup_closed _ y vy Hclosed_y Hlookup_y_restrict).
        exact Hsteps.
      * rewrite store_swap_insert_fresh by congruence.
        reflexivity.
    + intros [σtgt [[σm [vx [Hσm [Hsteps ->]]]] Hswap]].
      subst σ.
      assert (Hy_dom : y ∈ dom σm).
      { rewrite (wfworld_store_dom m σm Hσm), Hdom. set_solver. }
      apply elem_of_dom in Hy_dom as [vy Hlookup_y].
      assert (Hclosed_y : closed_env (store_restrict σm {[y]})).
      {
        replace (store_restrict σm {[y]}) with
          (store_restrict (store_restrict σm (D ∪ {[y]})) {[y]}).
        - apply closed_env_restrict. exact (proj1 (Hclosed σm Hσm)).
        - store_norm. replace ((D ∪ {[y]}) ∩ {[y]}) with ({[y]} : aset) by set_solver.
          reflexivity.
      }
      assert (Hlookup_y_restrict :
        store_restrict σm {[y]} !! y = Some vy).
      { rewrite store_restrict_lookup, decide_True by set_solver. exact Hlookup_y. }
      change (m{store_restrict σm {[y]}} (tret (vfvar y)) →*
        tret vx) in Hsteps.
      rewrite (msubst_ret_fvar_lookup_closed _ y vy Hclosed_y Hlookup_y_restrict) in Hsteps.
      pose proof (value_steps_self vy (tret vx) Hsteps) as Heq.
      inversion Heq. subst vx.
      assert (Hclosed_x : closed_env
        (store_restrict (store_swap x y σm) {[x]})).
      {
        replace ({[x]} : aset) with ((∅ : aset) ∪ {[x]}) by set_solver.
        rewrite store_restrict_swap_fresh_union_singleton with (D := ∅)
          by (try apply not_elem_of_empty).
        replace ((∅ : aset) ∪ {[y]}) with ({[y]} : aset) by set_solver.
        apply closed_env_store_swap. exact Hclosed_y.
      }
      assert (Hlookup_x_restrict :
        store_restrict (store_swap x y σm) {[x]} !! x = Some vy).
      {
        rewrite store_restrict_lookup, decide_True by set_solver.
        rewrite store_swap_lookup_inv.
        replace (atom_swap x y x) with y
          by (unfold atom_swap; repeat destruct decide; congruence).
        exact Hlookup_y.
      }
      exists (store_swap x y σm), vy.
      repeat split.
      * exists σm. split; [exact Hσm | reflexivity].
      * change (m{store_restrict (store_swap x y σm) {[x]}} (tret (vfvar x)) →*
          tret vy).
        rewrite (msubst_ret_fvar_lookup_closed _ x vy Hclosed_x Hlookup_x_restrict).
        exact Hsteps.
      * rewrite store_swap_insert_fresh by congruence.
        reflexivity.
Qed.

Lemma world_closed_on_swap_fresh_union_singleton_iff D x y (m : WfWorld) :
  x ∉ D →
  y ∉ D →
  world_closed_on (D ∪ {[x]}) (res_swap x y m) ↔
  world_closed_on (D ∪ {[y]}) m.
Proof.
  intros Hx Hy. split; intros Hclosed.
  - pose proof (world_closed_on_swap x y (D ∪ {[x]}) (res_swap x y m)
      Hclosed) as Hswap.
    rewrite res_swap_involutive in Hswap.
    replace (aset_swap x y (D ∪ {[x]})) with (D ∪ {[y]}) in Hswap;
      [exact Hswap |].
    apply set_eq. intros z.
    rewrite elem_of_aset_swap, !elem_of_union, !elem_of_singleton.
    unfold atom_swap.
    repeat destruct decide; set_solver.
  - pose proof (world_closed_on_swap x y (D ∪ {[y]}) m Hclosed) as Hswap.
    replace (aset_swap x y (D ∪ {[y]})) with (D ∪ {[x]}) in Hswap;
      [exact Hswap |].
    symmetry. apply aset_swap_fresh_union_singleton; assumption.
Qed.

Lemma world_store_closed_on_swap_fresh_union_singleton_iff D x y (m : WfWorld) :
  x ∉ D →
  y ∉ D →
  world_store_closed_on (D ∪ {[x]}) (res_swap x y m) ↔
  world_store_closed_on (D ∪ {[y]}) m.
Proof.
  intros Hx Hy. split; intros Hclosed.
  - pose proof (world_store_closed_on_swap x y (D ∪ {[x]}) (res_swap x y m)
      Hclosed) as Hswap.
    rewrite res_swap_involutive in Hswap.
    replace (aset_swap x y (D ∪ {[x]})) with (D ∪ {[y]}) in Hswap;
      [exact Hswap |].
    apply set_eq. intros z.
    rewrite elem_of_aset_swap, !elem_of_union, !elem_of_singleton.
    unfold atom_swap.
    repeat destruct decide; set_solver.
  - pose proof (world_store_closed_on_swap x y (D ∪ {[y]}) m Hclosed) as Hswap.
    replace (aset_swap x y (D ∪ {[y]})) with (D ∪ {[x]}) in Hswap;
      [exact Hswap |].
    symmetry. apply aset_swap_fresh_union_singleton; assumption.
Qed.

Lemma expr_total_with_store_empty_tret_fvar_swap_exact
    D x y (m : WfWorld) :
  x ∉ D →
  y ∉ D →
  world_dom (m : World) = D ∪ {[y]} →
  world_store_closed_on (D ∪ {[y]}) m →
  expr_total_with_store (D ∪ {[y]}) (tret (vfvar y)) ∅ m →
  expr_total_with_store (D ∪ {[x]}) (tret (vfvar x)) ∅ (res_swap x y m).
Proof.
  intros Hx Hy Hdom Hclosed [_ Htotal].
  split.
  - intros σx Hσx.
    simpl in Hσx.
    destruct Hσx as [σy [Hσy Hσx]]. subst σx.
    rewrite map_empty_union.
    rewrite store_restrict_swap_fresh_union_singleton by assumption.
    apply store_closed_store_swap.
    apply Hclosed. exact Hσy.
  - intros σx Hσx.
  simpl in Hσx.
  destruct Hσx as [σy [Hσy Hσx]]. subst σx.
  rewrite map_empty_union.
  rewrite store_restrict_swap_fresh_union_singleton by assumption.
  pose proof (Hclosed σy Hσy) as [Hclosed_y _].
  assert (Hy_dom : y ∈ dom σy).
  { rewrite (wfworld_store_dom m σy Hσy), Hdom. set_solver. }
  apply elem_of_dom in Hy_dom as [vy Hlookup].
  assert (Hlookup_restrict :
    store_restrict σy (D ∪ {[y]}) !! y = Some vy).
  { apply store_restrict_lookup_some_2; [exact Hlookup | set_solver]. }
  destruct (Htotal σy Hσy) as [vout Hsteps].
  exists vout.
  change (m{store_swap x y (store_restrict σy (D ∪ {[y]}))}
    (tret (vfvar x)) →* tret vout).
  rewrite (msubst_tret_fvar_store_swap_lookup
    (store_restrict σy (D ∪ {[y]})) x y vy
    Hclosed_y Hlookup_restrict).
  replace (store_restrict σy (D ∪ {[y]}))
    with (store_restrict (∅ ∪ σy) (D ∪ {[y]}))
    by (rewrite map_empty_union; reflexivity).
  exact Hsteps.
Qed.

Lemma expr_total_with_store_empty_tapp_tm_fvar_swap_exact
    D e x y (m : WfWorld) :
  x ∉ D ∪ fv_tm e →
  y ∉ D ∪ fv_tm e →
  world_dom (m : World) = D ∪ {[y]} →
  world_store_closed_on (D ∪ {[y]}) m →
  expr_total_with_store (D ∪ {[y]}) (tapp_tm e (vfvar y)) ∅ m →
  expr_total_with_store (D ∪ {[x]}) (tapp_tm e (vfvar x)) ∅ (res_swap x y m).
Proof.
  intros Hx Hy Hdom Hclosed [_ Htotal].
  split.
  - intros σx Hσx.
    simpl in Hσx.
    destruct Hσx as [σy [Hσy Hσx]]. subst σx.
    rewrite map_empty_union.
    rewrite store_restrict_swap_fresh_union_singleton by set_solver.
    apply store_closed_store_swap.
    apply Hclosed. exact Hσy.
  - intros σx Hσx.
  simpl in Hσx.
  destruct Hσx as [σy [Hσy Hσx]]. subst σx.
  rewrite map_empty_union.
  rewrite store_restrict_swap_fresh_union_singleton by set_solver.
  pose proof (Hclosed σy Hσy) as [Hclosed_y _].
  assert (Hy_dom : y ∈ dom σy).
  { rewrite (wfworld_store_dom m σy Hσy), Hdom. set_solver. }
  apply elem_of_dom in Hy_dom as [vy Hlookup].
  assert (Hlookup_restrict :
    store_restrict σy (D ∪ {[y]}) !! y = Some vy).
  { apply store_restrict_lookup_some_2; [exact Hlookup | set_solver]. }
  destruct (Htotal σy Hσy) as [vout Hsteps].
  exists vout.
  change (m{store_swap x y (store_restrict σy (D ∪ {[y]}))}
    (tapp_tm e (vfvar x)) →* tret vout).
  rewrite (msubst_tapp_tm_fvar_store_swap_lookup
    (store_restrict σy (D ∪ {[y]})) e x y vy
    Hclosed_y Hlookup_restrict ltac:(set_solver) ltac:(set_solver)).
  replace (store_restrict σy (D ∪ {[y]}))
    with (store_restrict (∅ ∪ σy) (D ∪ {[y]}))
    by (rewrite map_empty_union; reflexivity).
  exact Hsteps.
Qed.

Lemma expr_total_on_tret_fvar_swap_iff D x y (m : WfWorld) :
  x ∉ D →
  y ∉ D →
  D ∪ {[y]} ⊆ world_dom (m : World) →
  world_closed_on (D ∪ {[y]}) m →
  expr_total_on (D ∪ {[x]}) (tret (vfvar x)) (res_swap x y m) ↔
  expr_total_on (D ∪ {[y]}) (tret (vfvar y)) m.
Proof.
  intros Hx Hy Hdom Hclosed. split.
  - intros [_ Htotal]. split; [set_solver |].
    intros σ Hσ.
    pose proof (Hclosed σ Hσ) as Hclosedσ.
    assert (Hy_dom : y ∈ dom σ).
    { rewrite (wfworld_store_dom m σ Hσ). apply Hdom. set_solver. }
    apply elem_of_dom in Hy_dom as [vy Hlookup].
    assert (Hlookup_restrict :
      store_restrict σ (D ∪ {[y]}) !! y = Some vy).
    { apply store_restrict_lookup_some_2; [exact Hlookup | set_solver]. }
    pose proof (Htotal (store_swap x y σ)) as Hsteps_total.
    assert ((res_swap x y m : World) (store_swap x y σ)) as Hσswap.
    { simpl. exists σ. split; [exact Hσ | reflexivity]. }
    specialize (Hsteps_total Hσswap) as [vout Hsteps].
    exists vout.
    rewrite store_restrict_swap_fresh_union_singleton in Hsteps by assumption.
    change (m{store_restrict σ (D ∪ {[y]})} (tret (vfvar y)) →* tret vout).
    rewrite <- (msubst_tret_fvar_store_swap_lookup
      (store_restrict σ (D ∪ {[y]})) x y vy
      (proj1 Hclosedσ) Hlookup_restrict).
    exact Hsteps.
  - intros [_ Htotal]. split; [set_solver |].
    intros σx Hσx.
    simpl in Hσx.
    destruct Hσx as [σy [Hσy Hσx]]. subst σx.
    rewrite store_restrict_swap_fresh_union_singleton by assumption.
    pose proof (Hclosed σy Hσy) as Hclosedσ.
    assert (Hy_dom : y ∈ dom σy).
    { rewrite (wfworld_store_dom m σy Hσy). apply Hdom. set_solver. }
    apply elem_of_dom in Hy_dom as [vy Hlookup].
    assert (Hlookup_restrict :
      store_restrict σy (D ∪ {[y]}) !! y = Some vy).
    { apply store_restrict_lookup_some_2; [exact Hlookup | set_solver]. }
    destruct (Htotal σy Hσy) as [vout Hsteps].
    exists vout.
    change (m{store_swap x y (store_restrict σy (D ∪ {[y]}))}
      (tret (vfvar x)) →* tret vout).
    rewrite (msubst_tret_fvar_store_swap_lookup
      (store_restrict σy (D ∪ {[y]})) x y vy
      (proj1 Hclosedσ) Hlookup_restrict).
    exact Hsteps.
Qed.

Lemma expr_total_on_tapp_tm_fvar_swap_iff D e x y (m : WfWorld) :
  x ∉ D ∪ fv_tm e →
  y ∉ D ∪ fv_tm e →
  fv_tm e ⊆ D →
  D ∪ {[y]} ⊆ world_dom (m : World) →
  world_closed_on (D ∪ {[y]}) m →
  expr_total_on (D ∪ {[x]}) (tapp_tm e (vfvar x)) (res_swap x y m) ↔
  expr_total_on (D ∪ {[y]}) (tapp_tm e (vfvar y)) m.
Proof.
  intros Hx Hy Hfve Hdom Hclosed. split.
  - intros [_ Htotal]. split.
    { rewrite fv_tapp_tm. simpl. set_solver. }
    intros σ Hσ.
    pose proof (Hclosed σ Hσ) as Hclosedσ.
    assert (Hy_dom : y ∈ dom σ).
    { rewrite (wfworld_store_dom m σ Hσ). apply Hdom. set_solver. }
    apply elem_of_dom in Hy_dom as [vy Hlookup].
    assert (Hlookup_restrict :
      store_restrict σ (D ∪ {[y]}) !! y = Some vy).
    { apply store_restrict_lookup_some_2; [exact Hlookup | set_solver]. }
    pose proof (Htotal (store_swap x y σ)) as Hsteps_total.
    assert ((res_swap x y m : World) (store_swap x y σ)) as Hσswap.
    { simpl. exists σ. split; [exact Hσ | reflexivity]. }
    specialize (Hsteps_total Hσswap) as [vout Hsteps].
    exists vout.
    rewrite store_restrict_swap_fresh_union_singleton in Hsteps by set_solver.
    change (m{store_restrict σ (D ∪ {[y]})} (tapp_tm e (vfvar y)) →* tret vout).
    rewrite <- (msubst_tapp_tm_fvar_store_swap_lookup
      (store_restrict σ (D ∪ {[y]})) e x y vy
      (proj1 Hclosedσ) Hlookup_restrict ltac:(set_solver) ltac:(set_solver)).
    exact Hsteps.
  - intros [_ Htotal]. split.
    { rewrite fv_tapp_tm. simpl. set_solver. }
    intros σx Hσx.
    simpl in Hσx.
    destruct Hσx as [σy [Hσy Hσx]]. subst σx.
    rewrite store_restrict_swap_fresh_union_singleton by set_solver.
    pose proof (Hclosed σy Hσy) as Hclosedσ.
    assert (Hy_dom : y ∈ dom σy).
    { rewrite (wfworld_store_dom m σy Hσy). apply Hdom. set_solver. }
    apply elem_of_dom in Hy_dom as [vy Hlookup].
    assert (Hlookup_restrict :
      store_restrict σy (D ∪ {[y]}) !! y = Some vy).
    { apply store_restrict_lookup_some_2; [exact Hlookup | set_solver]. }
    destruct (Htotal σy Hσy) as [vout Hsteps].
    exists vout.
    change (m{store_swap x y (store_restrict σy (D ∪ {[y]}))}
      (tapp_tm e (vfvar x)) →* tret vout).
    rewrite (msubst_tapp_tm_fvar_store_swap_lookup
      (store_restrict σy (D ∪ {[y]})) e x y vy
      (proj1 Hclosedσ) Hlookup_restrict ltac:(set_solver) ltac:(set_solver)).
    exact Hsteps.
Qed.

Lemma swap_scoped_insert_dom x y D (m : WfWorld) :
  x ∉ D →
  y ∉ D →
  D ∪ {[x]} ⊆ world_dom (res_swap x y m : World) →
  D ∪ {[y]} ⊆ world_dom (m : World).
Proof.
  intros Hx Hy Hscope z Hz.
  assert (Hzswap : atom_swap x y z ∈ D ∪ {[x]}).
  {
    rewrite !elem_of_union, !elem_of_singleton in Hz |- *.
    unfold atom_swap in *.
    repeat destruct decide; set_solver.
  }
  specialize (Hscope (atom_swap x y z) Hzswap).
  simpl in Hscope.
  rewrite elem_of_aset_swap in Hscope.
  rewrite atom_swap_involutive in Hscope.
  exact Hscope.
Qed.

Lemma denot_ty_fuel_rebuild_fresh_tret_from_body gas
    (Σ : gmap atom ty) τx x y (m : WfWorld) :
  cty_measure τx <= gas →
  x ∉ dom Σ →
  y ∉ dom Σ →
  basic_choice_ty (dom Σ) τx →
  res_swap x y m ⊨ denot_ty_fuel gas (<[x := erase_ty τx]> Σ)
    τx (tret (vfvar x)) →
  m ⊨ denot_ty_fuel_body gas (<[y := erase_ty τx]> Σ)
    τx (tret (vfvar y)) →
  m ⊨ denot_ty_fuel gas (<[y := erase_ty τx]> Σ)
    τx (tret (vfvar y)).
Proof.
  intros Hgas Hx Hy Hbasic Hsrc Hbody.
  pose proof (res_models_with_store_fuel_scoped _ ∅ (res_swap x y m)
    (denot_ty_fuel gas (<[x := erase_ty τx]> Σ) τx (tret (vfvar x)))
    Hsrc) as Hscope_src.
  assert (Hscope_y :
    dom (<[y := erase_ty τx]> Σ) ⊆ world_dom (m : World)).
  {
    replace (dom (<[y:=erase_ty τx]> Σ)) with (dom Σ ∪ {[y]})
      by (rewrite dom_insert_L; set_solver).
    eapply swap_scoped_insert_dom; [exact Hx | exact Hy |].
    replace (dom Σ ∪ {[x]}) with (dom (<[x:=erase_ty τx]> Σ))
      by (rewrite dom_insert_L; set_solver).
    etransitivity.
    - eapply (denot_ty_fuel_env_fv_subset
        gas (<[x:=erase_ty τx]> Σ) τx (tret (vfvar x))).
      exact Hgas.
    - unfold formula_scoped_in_world in Hscope_src.
      rewrite dom_empty_L in Hscope_src.
      intros z Hz. apply Hscope_src. apply elem_of_union. right. exact Hz.
  }
  eapply denot_ty_fuel_intro.
  - eapply basic_choice_ty_mono; [| exact Hbasic].
    rewrite dom_insert_L. set_solver.
  - apply basic_typing_tret_fvar_insert.
	  - pose proof (denot_ty_fuel_world_closed_on_of_formula _ _ _ _ _ Hsrc)
	      as Hclosed_src.
	    rewrite dom_insert_L in Hclosed_src.
	    rewrite dom_insert_L.
	    replace ({[y]} ∪ dom Σ) with (dom Σ ∪ {[y]}) by set_solver.
	    replace ({[x]} ∪ dom Σ) with (dom Σ ∪ {[x]}) in Hclosed_src by set_solver.
	    apply (proj1 (world_closed_on_swap_fresh_union_singleton_iff
	      (dom Σ) x y m Hx Hy)).
	    exact Hclosed_src.
  - pose proof (denot_ty_fuel_expr_total_on_of_formula _ _ _ _ _ Hsrc)
      as Htotal_src.
	    rewrite dom_insert_L in Htotal_src.
	    rewrite dom_insert_L.
	    replace ({[y]} ∪ dom Σ) with (dom Σ ∪ {[y]}) by set_solver.
	    replace ({[x]} ∪ dom Σ) with (dom Σ ∪ {[x]}) in Htotal_src by set_solver.
	    assert (Hclosed_y : world_closed_on (dom Σ ∪ {[y]}) m).
	    {
	      pose proof (denot_ty_fuel_world_closed_on_of_formula _ _ _ _ _ Hsrc)
	        as Hclosed_src.
	      rewrite dom_insert_L in Hclosed_src.
	      replace ({[x]} ∪ dom Σ) with (dom Σ ∪ {[x]}) in Hclosed_src by set_solver.
	      apply (proj1 (world_closed_on_swap_fresh_union_singleton_iff
	        (dom Σ) x y m Hx Hy)).
	      exact Hclosed_src.
	    }
	    apply (proj1 (expr_total_on_tret_fvar_swap_iff
	      (dom Σ) x y m Hx Hy
	      ltac:(rewrite dom_insert_L in Hscope_y;
	            intros z Hz; apply Hscope_y; set_solver)
	      Hclosed_y)).
	    exact Htotal_src.
  - exact Hbody.
  - exact Hscope_y.
Qed.

Lemma denot_ty_fuel_rebuild_fresh_tapp_from_body gas
    (Σ : gmap atom ty) τx τ e x y (m : WfWorld) :
  cty_measure ({0 ~> y} τ) <= gas →
  x ∉ dom Σ ∪ fv_tm e →
  y ∉ dom Σ ∪ fv_tm e →
  fv_tm e ⊆ dom Σ →
  basic_choice_ty (dom Σ ∪ {[y]}) ({0 ~> y} τ) →
  Σ ⊢ₑ e ⋮ (erase_ty τx →ₜ erase_ty τ) →
  res_swap x y m ⊨ denot_ty_fuel gas (<[x := erase_ty τx]> Σ)
    ({0 ~> x} τ) (tapp_tm e (vfvar x)) →
  m ⊨ denot_ty_fuel_body gas (<[y := erase_ty τx]> Σ)
    ({0 ~> y} τ) (tapp_tm e (vfvar y)) →
  m ⊨ denot_ty_fuel gas (<[y := erase_ty τx]> Σ)
    ({0 ~> y} τ) (tapp_tm e (vfvar y)).
Proof.
  intros Hgas Hx Hy Hfve Hbasic Htye Hsrc Hbody.
  pose proof (res_models_with_store_fuel_scoped _ ∅ (res_swap x y m)
    (denot_ty_fuel gas (<[x := erase_ty τx]> Σ)
      ({0 ~> x} τ) (tapp_tm e (vfvar x))) Hsrc) as Hscope_src.
  assert (Hscope_y :
    dom (<[y := erase_ty τx]> Σ) ⊆ world_dom (m : World)).
  {
    replace (dom (<[y:=erase_ty τx]> Σ)) with (dom Σ ∪ {[y]})
      by (rewrite dom_insert_L; set_solver).
    eapply swap_scoped_insert_dom;
      [intro H; apply Hx; set_solver
      |intro H; apply Hy; set_solver
      |].
    replace (dom Σ ∪ {[x]}) with (dom (<[x:=erase_ty τx]> Σ))
      by (rewrite dom_insert_L; set_solver).
    etransitivity.
    - eapply (denot_ty_fuel_env_fv_subset
        gas (<[x:=erase_ty τx]> Σ) ({0 ~> x} τ)
        (tapp_tm e (vfvar x))).
      rewrite !cty_open_preserves_measure in *. exact Hgas.
    - unfold formula_scoped_in_world in Hscope_src.
      rewrite dom_empty_L in Hscope_src.
      intros z Hz. apply Hscope_src. apply elem_of_union. right. exact Hz.
  }
  eapply denot_ty_fuel_intro.
  - eapply basic_choice_ty_mono; [| exact Hbasic].
    rewrite dom_insert_L. set_solver.
  - eapply basic_typing_tapp_tm_fvar_insert.
    + set_solver.
    + rewrite cty_open_preserves_erasure. exact Htye.
  - pose proof (denot_ty_fuel_world_closed_on_of_formula _ _ _ _ _ Hsrc)
      as Hclosed_src.
    rewrite dom_insert_L in Hclosed_src.
    rewrite dom_insert_L.
    replace ({[y]} ∪ dom Σ) with (dom Σ ∪ {[y]}) by set_solver.
    replace ({[x]} ∪ dom Σ) with (dom Σ ∪ {[x]}) in Hclosed_src by set_solver.
    apply (proj1 (world_closed_on_swap_fresh_union_singleton_iff
      (dom Σ) x y m ltac:(set_solver) ltac:(set_solver))).
    exact Hclosed_src.
  - pose proof (denot_ty_fuel_expr_total_on_of_formula _ _ _ _ _ Hsrc)
      as Htotal_src.
    rewrite dom_insert_L in Htotal_src.
    rewrite dom_insert_L.
    replace ({[y]} ∪ dom Σ) with (dom Σ ∪ {[y]}) by set_solver.
    replace ({[x]} ∪ dom Σ) with (dom Σ ∪ {[x]}) in Htotal_src by set_solver.
    assert (Hclosed_y : world_closed_on (dom Σ ∪ {[y]}) m).
    {
      pose proof (denot_ty_fuel_world_closed_on_of_formula _ _ _ _ _ Hsrc)
        as Hclosed_src.
      rewrite dom_insert_L in Hclosed_src.
      replace ({[x]} ∪ dom Σ) with (dom Σ ∪ {[x]}) in Hclosed_src by set_solver.
      apply (proj1 (world_closed_on_swap_fresh_union_singleton_iff
        (dom Σ) x y m ltac:(set_solver) ltac:(set_solver))).
      exact Hclosed_src.
    }
    apply (proj1 (expr_total_on_tapp_tm_fvar_swap_iff
      (dom Σ) e x y m Hx Hy Hfve
      ltac:(rewrite dom_insert_L in Hscope_y;
            intros z Hz; apply Hscope_y; set_solver)
      Hclosed_y)).
    exact Htotal_src.
  - exact Hbody.
  - exact Hscope_y.
Qed.

(** The two lemmas below are the explicit-name/cofinite rename principles
    needed by the function-type cases.

    They are intentionally stated as semantic [formula_family_rename_stable_on]
    lemmas rather than syntactic equalities.  [denot_ty_fuel] now contains
    [FPure], [FClosedResourceIn], and [FStrongTotalIn] obligations; a syntactic
    [formula_rename_atom] does not rewrite those Rocq propositions.  The proof
    must therefore transport the obligations semantically:

    - [FPure] uses basic typing/formation rename for the fresh parameter;
    - [FClosedResourceIn] uses resource swap/restrict compatibility;
    - [FStrongTotalIn] uses operational totality under swapped stores;
    - the recursive body uses the [gas] induction hypothesis.

    The argument-family lemma covers the antecedent of Arrow/Wand.  The result
    family covers the consequent, where the result type is opened with the same
    fresh parameter and the expression is the ANF application sugar
    [tapp_tm e (vfvar x)]. *)
