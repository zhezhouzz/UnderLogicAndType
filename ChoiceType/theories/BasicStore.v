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

Lemma basic_world_formula_current Σ X m :
  res_models m (basic_world_formula Σ X) →
  world_has_type_on Σ X (res_restrict m X).
Proof.
  unfold basic_world_formula, res_models, res_models_with_store.
  simpl. intros [_ [m0 [Htyped0 Hle]]].
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
