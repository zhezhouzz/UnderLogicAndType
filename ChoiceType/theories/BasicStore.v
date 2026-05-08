(** * ChoiceType.BasicStore

    Basic well-typedness for stores and worlds.

    Choice-type denotations are semantic predicates over worlds, but their
    erased basic types must still constrain the values stored at tracked
    coordinates.  This file isolates that constraint from the refinement and
    resource definitions. *)

From CoreLang Require Import BasicTyping BasicTypingProps Instantiation InstantiationProps.
From ChoiceType Require Export Syntax.
From Stdlib Require Import Logic.FunctionalExtensionality Logic.PropExtensionality.

(** [store_has_type_on Σ X σ] says that every coordinate in [X] whose basic
    type is recorded by [Σ] is occupied by a closed value of that type.  The
    relation is intentionally domain-limited: denotations can ask only for the
    coordinates they introduce or inspect. *)
Definition store_has_type_on
    (Σ : gmap atom ty) (X : aset) (σ : Store) : Prop :=
  ∀ x T v,
    x ∈ X →
    Σ !! x = Some T →
    σ !! x = Some v →
    ∅ ⊢ᵥ v ⋮ T.

Definition world_has_type_on
    (Σ : gmap atom ty) (X : aset) (w : WfWorld) : Prop :=
  X ⊆ world_dom (w : World) ∧
  ∀ σ, (w : World) σ → store_has_type_on Σ X σ.

Definition basic_world_lqual
    (Σ : gmap atom ty) (X : aset) : logic_qualifier :=
  lqual X (fun _ w => world_has_type_on Σ X w).

Definition basic_world_formula
    (Σ : gmap atom ty) (X : aset) : FormulaQ :=
  FAtom (basic_world_lqual Σ X).

Lemma store_has_type_on_mono Σ X Y σ :
  X ⊆ Y →
  store_has_type_on Σ Y σ →
  store_has_type_on Σ X σ.
Proof.
  intros HXY Htyped x T v Hx HΣ Hσ.
  eapply Htyped; eauto.
Qed.

Lemma world_has_type_on_mono Σ X Y w :
  X ⊆ Y →
  world_has_type_on Σ Y w →
  world_has_type_on Σ X w.
Proof.
  intros HXY [Hdom Htyped]. split; [set_solver |].
  intros σ Hσ.
  eapply store_has_type_on_mono; eauto.
Qed.

Lemma basic_world_formula_fv Σ X :
  formula_fv (basic_world_formula Σ X) = X.
Proof. reflexivity. Qed.

Lemma basic_world_lqual_agree Σ1 Σ2 X :
  (∀ x, x ∈ X → Σ1 !! x = Σ2 !! x) →
  basic_world_lqual Σ1 X = basic_world_lqual Σ2 X.
Proof.
  intros Hagree. unfold basic_world_lqual. f_equal.
  apply functional_extensionality. intros σ.
  apply functional_extensionality. intros w.
  apply propositional_extensionality.
  unfold world_has_type_on, store_has_type_on in *.
  split.
  - intros [Hdom Htyped]. split; [exact Hdom |].
    intros σw Hσw x T v Hx HΣ Hlook.
    apply (Htyped σw Hσw x T v Hx); [| exact Hlook].
    rewrite Hagree; exact HΣ || exact Hx.
  - intros [Hdom Htyped]. split; [exact Hdom |].
    intros σw Hσw x T v Hx HΣ Hlook.
    apply (Htyped σw Hσw x T v Hx); [| exact Hlook].
    rewrite <- Hagree; exact HΣ || exact Hx.
Qed.

Lemma basic_world_formula_agree Σ1 Σ2 X :
  (∀ x, x ∈ X → Σ1 !! x = Σ2 !! x) →
  basic_world_formula Σ1 X = basic_world_formula Σ2 X.
Proof.
  intros Hagree. unfold basic_world_formula.
  rewrite (basic_world_lqual_agree Σ1 Σ2 X Hagree). reflexivity.
Qed.

Lemma lookup_insert_atom_swap_fresh_l
    (Σ : gmap atom ty) (X : aset) (x y : atom) (T : ty) z :
  x ∉ X →
  y ∉ X →
  z ∈ {[y]} ∪ X →
  (<[x := T]> Σ) !! atom_swap x y z = (<[y := T]> Σ) !! z.
Proof.
  intros Hx Hy Hz.
  destruct (decide (z = y)) as [->|Hzy].
  - replace (atom_swap x y y) with x
      by (unfold atom_swap; repeat destruct decide; congruence).
    rewrite !lookup_insert_eq. reflexivity.
  - assert (HzX : z ∈ X) by set_solver.
    assert (Hzx : z ≠ x) by set_solver.
    rewrite atom_swap_fresh by congruence.
    rewrite !lookup_insert_ne by congruence.
    reflexivity.
Qed.

Lemma lookup_insert_atom_swap_fresh_r
    (Σ : gmap atom ty) (X : aset) (x y : atom) (T : ty) z :
  x ∉ X →
  y ∉ X →
  z ∈ {[x]} ∪ X →
  (<[y := T]> Σ) !! atom_swap x y z = (<[x := T]> Σ) !! z.
Proof.
  intros Hx Hy Hz.
  destruct (decide (z = x)) as [->|Hzx].
  - replace (atom_swap x y x) with y
      by (unfold atom_swap; repeat destruct decide; congruence).
    rewrite !lookup_insert_eq. reflexivity.
  - assert (HzX : z ∈ X) by set_solver.
    assert (Hzy : z ≠ y) by set_solver.
    rewrite atom_swap_fresh by congruence.
    rewrite !lookup_insert_ne by congruence.
    reflexivity.
Qed.

Lemma store_has_type_on_swap_insert_fresh
    (Σ : gmap atom ty) (X : aset) (σ : Store) (x y : atom) (T : ty) :
  x ∉ X →
  y ∉ X →
  store_has_type_on (<[x := T]> Σ) ({[x]} ∪ X) (store_swap x y σ) ↔
  store_has_type_on (<[y := T]> Σ) ({[y]} ∪ X) σ.
Proof.
  intros Hx Hy. split.
  - intros Htyped z Tz v Hz HΣ Hσ.
    eapply Htyped with (x := atom_swap x y z); eauto.
    + destruct (decide (z = y)) as [->|Hzy].
      * replace (atom_swap x y y) with x
          by (unfold atom_swap; repeat destruct decide; congruence).
        set_solver.
      * rewrite atom_swap_fresh by set_solver.
        set_solver.
    + rewrite (lookup_insert_atom_swap_fresh_l Σ X x y T z Hx Hy Hz).
      exact HΣ.
    + rewrite store_swap_lookup. exact Hσ.
  - intros Htyped z Tz v Hz HΣ Hσ.
    eapply Htyped with (x := atom_swap x y z); eauto.
    + destruct (decide (z = x)) as [->|Hzx].
      * replace (atom_swap x y x) with y
          by (unfold atom_swap; repeat destruct decide; congruence).
        set_solver.
      * rewrite atom_swap_fresh by set_solver.
        set_solver.
    + rewrite (lookup_insert_atom_swap_fresh_r Σ X x y T z Hx Hy Hz).
      exact HΣ.
    + rewrite <- store_swap_lookup_inv. exact Hσ.
Qed.

Lemma world_has_type_on_swap_insert_fresh
    (Σ : gmap atom ty) (X : aset) (w : WfWorld) (x y : atom) (T : ty) :
  x ∉ X →
  y ∉ X →
  world_has_type_on (<[x := T]> Σ) ({[x]} ∪ X) (res_swap x y w) ↔
  world_has_type_on (<[y := T]> Σ) ({[y]} ∪ X) w.
Proof.
  intros Hx Hy. split.
  - intros [Hdom Htyped]. split.
    + simpl in Hdom.
      rewrite elem_of_subseteq. intros z Hz.
      assert (Hzswap : atom_swap x y z ∈ {[x]} ∪ X).
      {
        destruct (decide (z = y)) as [->|Hzy].
        - replace (atom_swap x y y) with x
            by (unfold atom_swap; repeat destruct decide; congruence).
          set_solver.
        - rewrite atom_swap_fresh by set_solver.
          set_solver.
      }
      apply Hdom in Hzswap.
      simpl in Hzswap. rewrite elem_of_aset_swap in Hzswap.
      rewrite atom_swap_involutive in Hzswap. exact Hzswap.
    + intros σ Hσ.
      apply (proj1 (store_has_type_on_swap_insert_fresh Σ X σ x y T Hx Hy)).
      apply Htyped. simpl. exists σ. split; [exact Hσ | reflexivity].
  - intros [Hdom Htyped]. split.
    + simpl. rewrite elem_of_subseteq. intros z Hz.
      rewrite elem_of_aset_swap.
      destruct (decide (z = x)) as [->|Hzx].
      * replace (atom_swap x y x) with y
          by (unfold atom_swap; repeat destruct decide; congruence).
        set_solver.
      * rewrite atom_swap_fresh by set_solver.
        set_solver.
    + intros σ Hσ.
      simpl in Hσ. destruct Hσ as [σ0 [Hσ0 Hswap]]. subst σ.
      apply (proj2 (store_has_type_on_swap_insert_fresh Σ X σ0 x y T Hx Hy)).
      apply Htyped. exact Hσ0.
Qed.

Lemma logic_qualifier_denote_basic_world_lqual_swap_insert_fresh
    (Σ : gmap atom ty) (X : aset) (x y : atom) (T : ty) σ w :
  x ∉ X →
  y ∉ X →
  logic_qualifier_denote
    (lqual_swap x y (basic_world_lqual (<[x := T]> Σ) ({[x]} ∪ X))) σ w ↔
  logic_qualifier_denote
    (basic_world_lqual (<[y := T]> Σ) ({[y]} ∪ X)) σ w.
Proof.
  intros Hx Hy.
  rewrite logic_qualifier_denote_swap.
  unfold basic_world_lqual. simpl.
  set (Xx := ({[x]} ∪ X : aset)).
  set (Xy := ({[y]} ∪ X : aset)).
  replace (aset_swap x y Xx) with Xy.
  2:{
    subst Xx Xy.
    rewrite aset_swap_union, aset_swap_singleton.
    replace (atom_swap x y x) with y
      by (unfold atom_swap; repeat destruct decide; congruence).
    rewrite aset_swap_fresh by assumption.
    reflexivity.
  }
  replace Xx with (aset_swap x y Xy).
  2:{
    subst Xx Xy.
    rewrite aset_swap_union, aset_swap_singleton.
    replace (atom_swap x y y) with x
      by (unfold atom_swap; repeat destruct decide; congruence).
    rewrite aset_swap_fresh by assumption.
    reflexivity.
  }
  rewrite res_restrict_swap.
  subst Xy.
  replace (aset_swap x y ({[y]} ∪ X)) with ({[x]} ∪ X).
  2:{
    rewrite aset_swap_union, aset_swap_singleton.
    replace (atom_swap x y y) with x
      by (unfold atom_swap; repeat destruct decide; congruence).
    rewrite aset_swap_fresh by assumption.
    reflexivity.
  }
  apply world_has_type_on_swap_insert_fresh; assumption.
Qed.

Lemma res_models_with_store_basic_world_formula_rename_insert_fresh
    (Σ : gmap atom ty) (X : aset) (x y : atom) (T : ty) ρ m :
  x ∉ X →
  y ∉ X →
  res_models_with_store ρ m (formula_rename_atom x y
    (basic_world_formula (<[x := T]> Σ) ({[x]} ∪ X))) ↔
  res_models_with_store ρ m
    (basic_world_formula (<[y := T]> Σ) ({[y]} ∪ X)).
Proof.
  intros Hx Hy.
  unfold res_models_with_store.
  simpl. split; intros [Hscope Hmodel]; split.
  - unfold formula_scoped_in_world in *. simpl in *.
    unfold stale, stale_logic_qualifier, basic_world_lqual, lqual_dom in *.
    intros z Hz. apply Hscope.
    replace (aset_swap x y ({[x]} ∪ X)) with ({[y]} ∪ X) by
      (rewrite aset_swap_union, aset_swap_singleton;
       replace (atom_swap x y x) with y by
         (unfold atom_swap; repeat destruct decide; congruence);
       rewrite aset_swap_fresh by assumption; reflexivity).
    exact Hz.
  - destruct Hmodel as [m0 [Hscope0 [Hq Hle]]].
    exists m0. split.
    + unfold formula_scoped_in_world in *. simpl in *.
      unfold stale, stale_logic_qualifier, basic_world_lqual, lqual_dom in *.
      intros z Hz. apply Hscope0.
      replace (aset_swap x y ({[x]} ∪ X)) with ({[y]} ∪ X) by
        (rewrite aset_swap_union, aset_swap_singleton;
         replace (atom_swap x y x) with y by
           (unfold atom_swap; repeat destruct decide; congruence);
         rewrite aset_swap_fresh by assumption; reflexivity).
      exact Hz.
    + split; [| exact Hle].
    apply (proj1 (logic_qualifier_denote_basic_world_lqual_swap_insert_fresh
      Σ X x y T ρ m0 Hx Hy)). exact Hq.
  - unfold formula_scoped_in_world in *. simpl in *.
    unfold stale, stale_logic_qualifier, basic_world_lqual, lqual_dom in *.
    intros z Hz. apply Hscope.
    replace (aset_swap x y ({[x]} ∪ X)) with ({[y]} ∪ X) in Hz by
      (rewrite aset_swap_union, aset_swap_singleton;
       replace (atom_swap x y x) with y by
         (unfold atom_swap; repeat destruct decide; congruence);
       rewrite aset_swap_fresh by assumption; reflexivity).
    exact Hz.
  - destruct Hmodel as [m0 [Hscope0 [Hq Hle]]].
    exists m0. split.
    + unfold formula_scoped_in_world in *. simpl in *.
      unfold stale, stale_logic_qualifier, basic_world_lqual, lqual_dom in *.
      intros z Hz. apply Hscope0.
      replace (aset_swap x y ({[x]} ∪ X)) with ({[y]} ∪ X) in Hz by
        (rewrite aset_swap_union, aset_swap_singleton;
         replace (atom_swap x y x) with y by
           (unfold atom_swap; repeat destruct decide; congruence);
         rewrite aset_swap_fresh by assumption; reflexivity).
      exact Hz.
    + split; [| exact Hle].
    apply (proj2 (logic_qualifier_denote_basic_world_lqual_swap_insert_fresh
      Σ X x y T ρ m0 Hx Hy)). exact Hq.
Qed.

Lemma res_models_basic_world_formula_rename_insert_fresh
    (Σ : gmap atom ty) (X : aset) (x y : atom) (T : ty) m :
  x ∉ X →
  y ∉ X →
  res_models m (formula_rename_atom x y
    (basic_world_formula (<[x := T]> Σ) ({[x]} ∪ X))) ↔
  res_models m (basic_world_formula (<[y := T]> Σ) ({[y]} ∪ X)).
Proof.
  apply res_models_with_store_basic_world_formula_rename_insert_fresh.
Qed.

Lemma basic_world_formula_current Σ X m :
  res_models m (basic_world_formula Σ X) →
  world_has_type_on Σ X (res_restrict m X).
Proof.
  unfold basic_world_formula, res_models, res_models_with_store.
  simpl. intros [_ [m0 [_ [Htyped0 Hle]]]].
  assert (HXm0 : X ⊆ world_dom (m0 : World)).
  {
    destruct Htyped0 as [Hdom0 _]. simpl in Hdom0. set_solver.
  }
  rewrite <- (res_restrict_le_eq m0 m X Hle HXm0).
  exact Htyped0.
Qed.

Lemma basic_world_formula_subset_current Σ X Y m :
  X ⊆ Y →
  res_models m (basic_world_formula Σ Y) →
  world_has_type_on Σ X (res_restrict m X).
Proof.
  intros HXY Hbasic.
  pose proof (basic_world_formula_current Σ Y m Hbasic) as HtypedY.
  destruct HtypedY as [HdomY HtypedY].
  split.
  - simpl in *. set_solver.
  - intros σ Hσ z T v Hz HΣ Hlookup.
    simpl in Hσ.
    destruct Hσ as [σm [Hσm Hrestrict]].
    subst σ.
    apply store_restrict_lookup_some in Hlookup as [_ Hlookup].
    eapply HtypedY.
    + simpl. exists σm. split; [exact Hσm | reflexivity].
    + exact (HXY z Hz).
    + exact HΣ.
    + apply store_restrict_lookup_some_2; [exact Hlookup | exact (HXY z Hz)].
Qed.

Lemma basic_world_formula_store_typed Σ X m σ :
  res_models m (basic_world_formula Σ X) →
  (res_restrict m X : World) σ →
  store_has_type_on Σ X σ.
Proof.
  intros Hbasic Hσ.
  destruct (basic_world_formula_current Σ X m Hbasic) as [_ Htyped].
  exact (Htyped σ Hσ).
Qed.

Lemma basic_world_formula_store_restrict_typed Σ X m σ :
  res_models m (basic_world_formula Σ X) →
  (m : World) σ →
  store_has_type_on Σ X (store_restrict σ X).
Proof.
  intros Hbasic Hσ.
  eapply basic_world_formula_store_typed; [exact Hbasic |].
  simpl. exists σ. split; [exact Hσ | reflexivity].
Qed.

Lemma store_has_type_on_lookup Σ X σ x T v :
  store_has_type_on Σ X σ →
  x ∈ X →
  Σ !! x = Some T →
  σ !! x = Some v →
  ∅ ⊢ᵥ v ⋮ T.
Proof.
  intros Htyped Hx HΣ Hσ.
  eapply Htyped; eauto.
Qed.

Lemma store_has_type_on_closed_env Σ X σ :
  dom σ ⊆ X →
  X ⊆ dom Σ →
  store_has_type_on Σ X σ →
  closed_env σ.
Proof.
  intros Hdomσ HXΣ Htyped.
  unfold closed_env. apply map_Forall_lookup_2.
  intros x v Hlookup.
  assert (Hxσ : x ∈ dom σ) by (apply elem_of_dom; eexists; exact Hlookup).
  assert (HxX : x ∈ X) by set_solver.
  assert (HxΣ : x ∈ dom Σ) by set_solver.
  apply elem_of_dom in HxΣ as [T HΣ].
  pose proof (Htyped x T v HxX HΣ Hlookup) as Hvalue.
  apply basic_typing_closed_value in Hvalue.
  exact Hvalue.
Qed.

Lemma store_has_type_on_lc_env Σ X σ :
  dom σ ⊆ X →
  X ⊆ dom Σ →
  store_has_type_on Σ X σ →
  lc_env σ.
Proof.
  intros Hdomσ HXΣ Htyped.
  unfold lc_env. apply map_Forall_lookup_2.
  intros x v Hlookup.
  assert (Hxσ : x ∈ dom σ) by (apply elem_of_dom; eexists; exact Hlookup).
  assert (HxX : x ∈ X) by set_solver.
  assert (HxΣ : x ∈ dom Σ) by set_solver.
  apply elem_of_dom in HxΣ as [T HΣ].
  pose proof (Htyped x T v HxX HΣ Hlookup) as Hvalue.
  exact (typing_value_lc _ _ _ Hvalue).
Qed.

Lemma basic_world_formula_store_closed_env Σ X m σ :
  res_models m (basic_world_formula Σ X) →
  X ⊆ dom Σ →
  (res_restrict m X : World) σ →
  closed_env σ.
Proof.
  intros Hbasic HXΣ Hσ.
  eapply (store_has_type_on_closed_env Σ X σ).
  - pose proof (wfworld_store_dom (res_restrict m X) σ Hσ) as Hdom.
    simpl in Hdom. set_solver.
  - exact HXΣ.
  - eapply basic_world_formula_store_typed; eauto.
Qed.

Lemma basic_world_formula_store_restrict_closed_env Σ X m σ :
  res_models m (basic_world_formula Σ X) →
  X ⊆ dom Σ →
  (m : World) σ →
  closed_env (store_restrict σ X).
Proof.
  intros Hbasic HXΣ Hσ.
  eapply (store_has_type_on_closed_env Σ X (store_restrict σ X)).
  - rewrite store_restrict_dom. set_solver.
  - exact HXΣ.
  - eapply basic_world_formula_store_restrict_typed; eauto.
Qed.

Lemma basic_world_formula_store_lc_env Σ X m σ :
  res_models m (basic_world_formula Σ X) →
  X ⊆ dom Σ →
  (res_restrict m X : World) σ →
  lc_env σ.
Proof.
  intros Hbasic HXΣ Hσ.
  eapply (store_has_type_on_lc_env Σ X σ).
  - pose proof (wfworld_store_dom (res_restrict m X) σ Hσ) as Hdom.
    simpl in Hdom. set_solver.
  - exact HXΣ.
  - eapply basic_world_formula_store_typed; eauto.
Qed.

Lemma basic_world_formula_store_restrict_lc_env Σ X m σ :
  res_models m (basic_world_formula Σ X) →
  X ⊆ dom Σ →
  (m : World) σ →
  lc_env (store_restrict σ X).
Proof.
  intros Hbasic HXΣ Hσ.
  eapply (store_has_type_on_lc_env Σ X (store_restrict σ X)).
  - rewrite store_restrict_dom. set_solver.
  - exact HXΣ.
  - eapply basic_world_formula_store_restrict_typed; eauto.
Qed.

Lemma basic_world_formula_extension_store_restrict_closed_env
    Σ X m my σ :
  res_models m (basic_world_formula Σ X) →
  X ⊆ dom Σ →
  X ⊆ world_dom (m : World) →
  res_restrict my (world_dom (m : World)) = m →
  (my : World) σ →
  closed_env (store_restrict σ X).
Proof.
  intros Hbasic HXΣ HXm Hrestr Hσ.
  assert (Hmσ : (m : World) (store_restrict σ (world_dom (m : World)))).
  {
    rewrite <- Hrestr. simpl.
    exists σ. split; [exact Hσ |].
    pose proof (wfworld_store_dom my σ Hσ) as Hdomσ.
    rewrite <- (store_restrict_restrict σ (world_dom (my : World))
      (world_dom (m : World))).
    replace (store_restrict σ (world_dom (my : World))) with σ.
    2:{ symmetry. apply store_restrict_idemp.
        intros z Hz. rewrite <- Hdomσ. exact Hz. }
    reflexivity.
  }
  replace (store_restrict σ X)
    with (store_restrict (store_restrict σ (world_dom (m : World))) X).
  2:{ rewrite store_restrict_restrict.
      replace (world_dom (m : World) ∩ X) with X by set_solver.
      reflexivity. }
  eapply basic_world_formula_store_restrict_closed_env; eauto.
Qed.

Lemma basic_world_formula_extension_store_restrict_lc_env
    Σ X m my σ :
  res_models m (basic_world_formula Σ X) →
  X ⊆ dom Σ →
  X ⊆ world_dom (m : World) →
  res_restrict my (world_dom (m : World)) = m →
  (my : World) σ →
  lc_env (store_restrict σ X).
Proof.
  intros Hbasic HXΣ HXm Hrestr Hσ.
  assert (Hmσ : (m : World) (store_restrict σ (world_dom (m : World)))).
  {
    rewrite <- Hrestr. simpl.
    exists σ. split; [exact Hσ |].
    pose proof (wfworld_store_dom my σ Hσ) as Hdomσ.
    rewrite <- (store_restrict_restrict σ (world_dom (my : World))
      (world_dom (m : World))).
    replace (store_restrict σ (world_dom (my : World))) with σ.
    2:{ symmetry. apply store_restrict_idemp.
        intros z Hz. rewrite <- Hdomσ. exact Hz. }
    reflexivity.
  }
  replace (store_restrict σ X)
    with (store_restrict (store_restrict σ (world_dom (m : World))) X).
  2:{ rewrite store_restrict_restrict.
      replace (world_dom (m : World) ∩ X) with X by set_solver.
      reflexivity. }
  eapply basic_world_formula_store_restrict_lc_env; eauto.
Qed.

Lemma store_has_type_on_insert_self Σ X σ x T v :
  store_has_type_on (<[x := T]> Σ) X σ →
  x ∈ X →
  σ !! x = Some v →
  ∅ ⊢ᵥ v ⋮ T.
Proof.
  intros Htyped Hx Hσ.
  exact (Htyped x T v Hx (lookup_insert_eq Σ x T) Hσ).
Qed.

Lemma world_has_type_on_lookup Σ X w σ x T v :
  world_has_type_on Σ X w →
  (w : World) σ →
  x ∈ X →
  Σ !! x = Some T →
  σ !! x = Some v →
  ∅ ⊢ᵥ v ⋮ T.
Proof.
  intros [_ Htyped] Hσ Hx HΣ Hlook.
  eapply store_has_type_on_lookup; eauto.
Qed.

Lemma world_has_type_on_insert_self Σ X w σ x T v :
  world_has_type_on (<[x := T]> Σ) X w →
  (w : World) σ →
  x ∈ X →
  σ !! x = Some v →
  ∅ ⊢ᵥ v ⋮ T.
Proof.
  intros [_ Htyped] Hσ Hx Hlook.
  eapply store_has_type_on_insert_self; eauto.
Qed.

Lemma store_has_type_on_restrict Σ X Y σ :
  store_has_type_on Σ X σ →
  store_has_type_on Σ (X ∩ Y) (store_restrict σ Y).
Proof.
  intros Htyped z T v Hz HΣ Hlookup.
  apply store_restrict_lookup_some in Hlookup as [_ Hlookup].
  eapply Htyped; eauto. set_solver.
Qed.

Lemma world_has_type_on_restrict Σ X Y w :
  world_has_type_on Σ X w →
  world_has_type_on Σ (X ∩ Y) (res_restrict w Y).
Proof.
  intros [Hdom Htyped]. split; [simpl; set_solver |].
  intros σ Hσ.
  simpl in Hσ.
  destruct Hσ as [σ0 [Hσ0 Hrestrict]].
  subst σ.
  apply store_has_type_on_restrict.
  apply Htyped. exact Hσ0.
Qed.

Lemma world_has_type_on_restrict_mono Σ X Y w :
  X ⊆ Y →
  world_has_type_on Σ X w →
  world_has_type_on Σ X (res_restrict w Y).
Proof.
  intros HXY [Hdom Htyped]. split; [simpl; set_solver |].
  intros σ Hσ.
  simpl in Hσ.
  destruct Hσ as [σ0 [Hσ0 Hrestrict]].
  subst σ.
  intros x T v Hx HΣ Hlookup.
  apply store_restrict_lookup_some in Hlookup as [_ Hlookup].
  eapply Htyped; eauto.
Qed.
