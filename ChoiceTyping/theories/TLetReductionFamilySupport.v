(** * ChoiceTyping.TLetReductionFamilySupport

    Fuel-level and model-level reduction lemmas for the [tlet] soundness case.
    The final semantic wrappers stay in [TLetDenotation]. *)

From CoreLang Require Import Instantiation InstantiationProps OperationalProps BasicTypingProps
  LocallyNamelessProps StrongNormalization Sugar.
From ChoiceTyping Require Import TLetReductionSwapSupport
  Naming ResultWorldBridge ResultWorldFreshForall.
From ChoiceType Require Import BasicStore LocallyNamelessProps DenotationRefinement.

Import Tactics.

(** Formula-family support and rename-stability helpers for the [tlet] reduction proof. *)
Lemma formula_family_rename_stable_and D P Q :
  formula_family_rename_stable_on D P →
  formula_family_rename_stable_on D Q →
  formula_family_rename_stable_on D (fun x => FAnd (P x) (Q x)).
Proof.
  intros HP HQ.
  unfold formula_family_rename_stable_on in *.
  intros x y n Hx Hy. simpl.
  split; intros Hmodel.
  - apply res_models_and_intro_from_models.
    + apply (proj1 (HP x y n Hx Hy)).
      apply res_models_and_elim_l in Hmodel. exact Hmodel.
    + apply (proj1 (HQ x y n Hx Hy)).
      apply res_models_and_elim_r in Hmodel. exact Hmodel.
  - apply res_models_and_intro_from_models.
    + apply (proj2 (HP x y n Hx Hy)).
      apply res_models_and_elim_l in Hmodel. exact Hmodel.
    + apply (proj2 (HQ x y n Hx Hy)).
      apply res_models_and_elim_r in Hmodel. exact Hmodel.
Qed.

Lemma formula_family_rename_stable_const D φ :
  formula_fv φ ⊆ D →
  formula_family_rename_stable_on D (fun _ => φ).
Proof.
  intros Hfv.
  unfold formula_family_rename_stable_on.
  intros x y n Hx Hy.
  apply res_models_rename_atom_fresh; set_solver.
Qed.

Definition formula_family_support_exact_on (D : aset) (P : atom → FormulaQ) : Prop :=
  ∀ x, x ∉ D → formula_fv (P x) = D ∪ {[x]}.

Lemma formula_family_support_exact_and D P Q :
  formula_family_support_exact_on D P →
  formula_family_support_exact_on D Q →
  formula_family_support_exact_on D (fun x => FAnd (P x) (Q x)).
Proof.
  intros HP HQ x Hx. simpl. rewrite HP, HQ by exact Hx. set_solver.
Qed.

Lemma formula_family_support_exact_or D P Q :
  formula_family_support_exact_on D P →
  formula_family_support_exact_on D Q →
  formula_family_support_exact_on D (fun x => FOr (P x) (Q x)).
Proof.
  intros HP HQ x Hx. simpl. rewrite HP, HQ by exact Hx. set_solver.
Qed.

Lemma formula_family_support_exact_plus D P Q :
  formula_family_support_exact_on D P →
  formula_family_support_exact_on D Q →
  formula_family_support_exact_on D (fun x => FPlus (P x) (Q x)).
Proof.
  intros HP HQ x Hx. simpl. rewrite HP, HQ by exact Hx. set_solver.
Qed.

Lemma formula_family_support_exact_impl D P Q :
  formula_family_support_exact_on D P →
  formula_family_support_exact_on D Q →
  formula_family_support_exact_on D (fun x => FImpl (P x) (Q x)).
Proof.
  intros HP HQ x Hx. simpl. rewrite HP, HQ by exact Hx. set_solver.
Qed.

Lemma formula_family_support_exact_wand D P Q :
  formula_family_support_exact_on D P →
  formula_family_support_exact_on D Q →
  formula_family_support_exact_on D (fun x => FWand (P x) (Q x)).
Proof.
  intros HP HQ x Hx. simpl. rewrite HP, HQ by exact Hx. set_solver.
Qed.

Lemma atom_swap_left_eq x y : atom_swap x y x = y.
Proof. unfold atom_swap. repeat destruct decide; congruence. Qed.

Lemma atom_swap_right_eq x y : atom_swap x y y = x.
Proof. unfold atom_swap. repeat destruct decide; congruence. Qed.

Lemma denot_ty_fuel_fresh_arg_family_support_exact
    gas (Σ : gmap atom ty) τx :
  cty_measure τx <= gas →
  basic_choice_ty (dom Σ) τx →
  formula_family_support_exact_on (dom Σ) (fun x =>
    denot_ty_fuel gas (<[x := erase_ty τx]> Σ)
      τx (tret (vfvar x))).
Proof.
  intros Hgas Hbasic x Hx.
  apply set_eq. intros z. split.
  - intros Hz.
    eapply denot_ty_fuel_formula_fv_subset_env in Hz.
    + rewrite dom_insert_L in Hz. set_solver.
    + exact Hgas.
    + eapply basic_choice_ty_fv_subset.
      eapply basic_choice_ty_mono; [| exact Hbasic].
      rewrite dom_insert_L. set_solver.
  - intros Hz.
    eapply denot_ty_fuel_env_fv_subset; [exact Hgas |].
    rewrite dom_insert_L. set_solver.
Qed.

Lemma denot_ty_fuel_fresh_result_family_support_exact
    gas (Σ : gmap atom ty) τx τ e :
  cty_measure τ <= gas →
  (∀ x, x ∉ dom Σ → basic_choice_ty (dom Σ ∪ {[x]}) ({0 ~> x} τ)) →
  formula_family_support_exact_on (dom Σ) (fun x =>
    denot_ty_fuel gas (<[x := erase_ty τx]> Σ)
      ({0 ~> x} τ) (tapp_tm e (vfvar x))).
Proof.
  intros Hgas Hbasic_body x Hx.
  apply set_eq. intros z. split.
  - intros Hz.
    eapply denot_ty_fuel_formula_fv_subset_env in Hz.
    + rewrite dom_insert_L in Hz. set_solver.
    + rewrite cty_open_preserves_measure. exact Hgas.
    + eapply basic_choice_ty_fv_subset.
      replace (dom (<[x:=erase_ty τx]> Σ)) with (dom Σ ∪ {[x]})
        by (rewrite dom_insert_L; set_solver).
      apply Hbasic_body. exact Hx.
  - intros Hz.
    eapply denot_ty_fuel_env_fv_subset.
    + rewrite cty_open_preserves_measure. exact Hgas.
    + rewrite dom_insert_L. set_solver.
Qed.

Lemma denot_ty_fuel_fresh_arg_family_rename_stable
    gas (Σ : gmap atom ty) τx :
  cty_measure τx <= gas →
  basic_choice_ty (dom Σ) τx →
  formula_family_rename_stable_on (dom Σ) (fun x =>
    denot_ty_fuel gas (<[x := erase_ty τx]> Σ)
      τx (tret (vfvar x))).
Proof.
Admitted.

Lemma denot_ty_fuel_fresh_result_family_rename_stable
    gas (Σ : gmap atom ty) τx τ e :
  cty_measure τ <= gas →
  fv_tm e ⊆ dom Σ →
  Σ ⊢ₑ e ⋮ (erase_ty τx →ₜ erase_ty τ) →
  (∀ x, x ∉ dom Σ → basic_choice_ty (dom Σ ∪ {[x]}) ({0 ~> x} τ)) →
  formula_family_rename_stable_on (dom Σ) (fun x =>
    denot_ty_fuel gas (<[x := erase_ty τx]> Σ)
      ({0 ~> x} τ) (tapp_tm e (vfvar x))).
Proof.
Admitted.

Lemma denot_ty_fuel_arrow_body_family_support_exact
    gas (Σ : gmap atom ty) τx τ e :
  cty_measure τx <= gas →
  cty_measure τ <= gas →
  basic_choice_ty (dom Σ) τx →
  (∀ x, x ∉ dom Σ → basic_choice_ty (dom Σ ∪ {[x]}) ({0 ~> x} τ)) →
  formula_family_support_exact_on (dom Σ) (fun x =>
    FImpl
      (denot_ty_fuel gas (<[x := erase_ty τx]> Σ)
        τx (tret (vfvar x)))
      (denot_ty_fuel gas (<[x := erase_ty τx]> Σ)
        ({0 ~> x} τ) (tapp_tm e (vfvar x)))).
Proof.
  intros Hgasx Hgas Hbasicx Hbasic_body.
  apply formula_family_support_exact_impl.
  - eapply denot_ty_fuel_fresh_arg_family_support_exact; eauto.
  - eapply denot_ty_fuel_fresh_result_family_support_exact; eauto.
Qed.

Lemma denot_ty_fuel_wand_body_family_support_exact
    gas (Σ : gmap atom ty) τx τ e :
  cty_measure τx <= gas →
  cty_measure τ <= gas →
  basic_choice_ty (dom Σ) τx →
  (∀ x, x ∉ dom Σ → basic_choice_ty (dom Σ ∪ {[x]}) ({0 ~> x} τ)) →
  formula_family_support_exact_on (dom Σ) (fun x =>
    FWand
      (denot_ty_fuel gas (<[x := erase_ty τx]> Σ)
        τx (tret (vfvar x)))
      (denot_ty_fuel gas (<[x := erase_ty τx]> Σ)
        ({0 ~> x} τ) (tapp_tm e (vfvar x)))).
Proof.
  intros Hgasx Hgas Hbasicx Hbasic_body.
  apply formula_family_support_exact_wand.
  - eapply denot_ty_fuel_fresh_arg_family_support_exact; eauto.
  - eapply denot_ty_fuel_fresh_result_family_support_exact; eauto.
Qed.

Lemma support_exact_rename_to_target_scope D P x y n :
  formula_family_support_exact_on D P →
  x ∉ D →
  y ∉ D →
  n ⊨ formula_rename_atom x y (P x) →
  formula_fv (P y) ⊆ world_dom (n : World).
Proof.
  intros Hsupp Hx Hy Hmodel.
  pose proof (res_models_with_store_fuel_scoped
    (formula_measure (formula_rename_atom x y (P x))) ∅ n
    (formula_rename_atom x y (P x)) Hmodel) as Hscope.
  unfold formula_scoped_in_world in Hscope.
  rewrite dom_empty_L in Hscope.
  rewrite Hsupp by exact Hy.
  intros z Hz.
  apply Hscope.
  apply elem_of_union_r.
  rewrite formula_fv_rename_atom.
  rewrite Hsupp by exact Hx.
  rewrite elem_of_aset_swap.
  apply elem_of_union in Hz as [HzD | Hzy].
  - apply elem_of_union_l.
    rewrite atom_swap_fresh; [exact HzD | set_solver | set_solver].
  - apply elem_of_union_r.
    apply elem_of_singleton in Hzy. subst z.
    rewrite atom_swap_right_eq. apply elem_of_singleton. reflexivity.
Qed.

Lemma support_exact_target_to_rename_scope D P x y n :
  formula_family_support_exact_on D P →
  x ∉ D →
  y ∉ D →
  n ⊨ P y →
  formula_fv (formula_rename_atom x y (P x)) ⊆ world_dom (n : World).
Proof.
  intros Hsupp Hx Hy Hmodel.
  pose proof (res_models_with_store_fuel_scoped
    (formula_measure (P y)) ∅ n (P y) Hmodel) as Hscope.
  unfold formula_scoped_in_world in Hscope.
  rewrite dom_empty_L in Hscope.
  rewrite formula_fv_rename_atom.
  rewrite Hsupp by exact Hx.
  intros z Hz.
  rewrite elem_of_aset_swap in Hz.
  apply Hscope.
  apply elem_of_union_r.
  rewrite Hsupp by exact Hy.
  apply elem_of_union in Hz as [HzD | Hzx].
  - apply elem_of_union_l.
    assert (Hzx : z ≠ x).
    { intros ->. rewrite atom_swap_left_eq in HzD. exact (Hy HzD). }
    assert (Hzy : z ≠ y).
    { intros ->. rewrite atom_swap_right_eq in HzD. exact (Hx HzD). }
    rewrite atom_swap_fresh in HzD by assumption. exact HzD.
  - apply elem_of_union_r.
    apply elem_of_singleton in Hzx.
    apply elem_of_singleton.
    unfold atom_swap in Hzx. repeat destruct decide; congruence.
Qed.

Lemma support_exact_renamed_family_covers_target D P x y :
  formula_family_support_exact_on D P →
  x ∉ D →
  y ∉ D →
  D ∪ {[y]} ⊆ formula_fv (formula_rename_atom x y (P x)).
Proof.
  intros Hsupp Hx Hy z Hz.
  rewrite formula_fv_rename_atom.
  rewrite Hsupp by exact Hx.
  rewrite elem_of_aset_swap.
  apply elem_of_union in Hz as [HzD | Hzy].
  - apply elem_of_union_l.
    rewrite atom_swap_fresh; [exact HzD | set_solver | set_solver].
  - apply elem_of_union_r.
    apply elem_of_singleton in Hzy. subst z.
    rewrite atom_swap_right_eq. apply elem_of_singleton. reflexivity.
Qed.

Lemma support_exact_renamed_scope_to_target_scope D P x y n :
  formula_family_support_exact_on D P →
  x ∉ D →
  y ∉ D →
  formula_fv (formula_rename_atom x y (P x)) ⊆ world_dom (n : World) →
  formula_fv (P y) ⊆ world_dom (n : World).
Proof.
  intros Hsupp Hx Hy Hscope.
  rewrite Hsupp by exact Hy.
  intros z Hz.
  apply Hscope.
  eapply support_exact_renamed_family_covers_target; eauto.
Qed.

Lemma support_exact_target_scope_to_renamed_scope D P x y n :
  formula_family_support_exact_on D P →
  x ∉ D →
  y ∉ D →
  formula_fv (P y) ⊆ world_dom (n : World) →
  formula_fv (formula_rename_atom x y (P x)) ⊆ world_dom (n : World).
Proof.
  intros Hsupp Hx Hy Hscope z Hz.
  rewrite formula_fv_rename_atom in Hz.
  pose proof (Hsupp x Hx) as Hsuppx.
  rewrite Hsuppx in Hz.
  rewrite elem_of_aset_swap in Hz.
  apply Hscope.
  rewrite Hsupp by exact Hy.
  apply elem_of_union in Hz as [HzD | Hzx].
  - apply elem_of_union_l.
    assert (Hz_ne_x : z ≠ x).
    { intros ->. rewrite atom_swap_left_eq in HzD. exact (Hy HzD). }
    assert (Hz_ne_y : z ≠ y).
    { intros ->. rewrite atom_swap_right_eq in HzD. exact (Hx HzD). }
    rewrite atom_swap_fresh in HzD by assumption. exact HzD.
  - apply elem_of_union_r.
    apply elem_of_singleton in Hzx.
    apply elem_of_singleton.
    unfold atom_swap in Hzx. repeat destruct decide; congruence.
Qed.

Lemma formula_family_rename_stable_or_exact D P Q :
  formula_family_support_exact_on D P →
  formula_family_support_exact_on D Q →
  formula_family_rename_stable_on D P →
  formula_family_rename_stable_on D Q →
  formula_family_rename_stable_on D (fun x => FOr (P x) (Q x)).
Proof.
  intros HPsupp HQsupp HP HQ.
  unfold formula_family_rename_stable_on in *.
  intros x y n Hx Hy. simpl. split; intros Hmodel.
  - pose proof (res_models_with_store_fuel_scoped
      (formula_measure (FOr (formula_rename_atom x y (P x))
         (formula_rename_atom x y (Q x)))) ∅ n
      (FOr (formula_rename_atom x y (P x))
         (formula_rename_atom x y (Q x))) Hmodel) as Hscope.
    unfold formula_scoped_in_world in Hscope.
    eapply res_models_or_transport_between_worlds; [| | | | exact Hmodel].
    + eapply support_exact_renamed_scope_to_target_scope; [exact HPsupp | exact Hx | exact Hy |].
      simpl in Hscope. set_solver.
    + eapply support_exact_renamed_scope_to_target_scope; [exact HQsupp | exact Hx | exact Hy |].
      simpl in Hscope. set_solver.
    + apply (proj1 (HP x y n Hx Hy)).
    + apply (proj1 (HQ x y n Hx Hy)).
  - pose proof (res_models_with_store_fuel_scoped
      (formula_measure (FOr (P y) (Q y))) ∅ n
      (FOr (P y) (Q y)) Hmodel) as Hscope.
    unfold formula_scoped_in_world in Hscope.
    eapply res_models_or_transport_between_worlds; [| | | | exact Hmodel].
    + eapply support_exact_target_scope_to_renamed_scope; [exact HPsupp | exact Hx | exact Hy |].
      simpl in Hscope. set_solver.
    + eapply support_exact_target_scope_to_renamed_scope; [exact HQsupp | exact Hx | exact Hy |].
      simpl in Hscope. set_solver.
    + apply (proj2 (HP x y n Hx Hy)).
    + apply (proj2 (HQ x y n Hx Hy)).
Qed.

Lemma formula_family_rename_stable_plus_exact D P Q :
  formula_family_support_exact_on D P →
  formula_family_support_exact_on D Q →
  formula_family_rename_stable_on D P →
  formula_family_rename_stable_on D Q →
  formula_family_rename_stable_on D (fun x => FPlus (P x) (Q x)).
Proof.
  intros HPsupp HQsupp HP HQ.
  unfold formula_family_rename_stable_on in *.
  intros x y n Hx Hy. simpl. split; intros Hmodel.
  - pose proof (res_models_with_store_fuel_scoped
      (formula_measure (FPlus (formula_rename_atom x y (P x))
         (formula_rename_atom x y (Q x)))) ∅ n
      (FPlus (formula_rename_atom x y (P x))
         (formula_rename_atom x y (Q x))) Hmodel) as Hscope.
    unfold formula_scoped_in_world in Hscope.
    eapply res_models_plus_map; [| | | exact Hmodel].
    + unfold formula_scoped_in_world. simpl.
      assert (HPscope : formula_fv (P y) ⊆ world_dom (n : World)).
      { eapply support_exact_renamed_scope_to_target_scope; [exact HPsupp | exact Hx | exact Hy |].
        simpl in Hscope. set_solver. }
      assert (HQscope : formula_fv (Q y) ⊆ world_dom (n : World)).
      { eapply support_exact_renamed_scope_to_target_scope; [exact HQsupp | exact Hx | exact Hy |].
        simpl in Hscope. set_solver. }
      set_solver.
    + intros m' Hm'. apply (proj1 (HP x y m' Hx Hy)). exact Hm'.
    + intros m' Hm'. apply (proj1 (HQ x y m' Hx Hy)). exact Hm'.
  - pose proof (res_models_with_store_fuel_scoped
      (formula_measure (FPlus (P y) (Q y))) ∅ n
      (FPlus (P y) (Q y)) Hmodel) as Hscope.
    unfold formula_scoped_in_world in Hscope.
    eapply res_models_plus_map; [| | | exact Hmodel].
    + unfold formula_scoped_in_world. simpl.
      assert (HPscope : formula_fv (formula_rename_atom x y (P x)) ⊆ world_dom (n : World)).
      { eapply support_exact_target_scope_to_renamed_scope; [exact HPsupp | exact Hx | exact Hy |].
        simpl in Hscope. set_solver. }
      assert (HQscope : formula_fv (formula_rename_atom x y (Q x)) ⊆ world_dom (n : World)).
      { eapply support_exact_target_scope_to_renamed_scope; [exact HQsupp | exact Hx | exact Hy |].
        simpl in Hscope. set_solver. }
      set_solver.
    + intros m' Hm'. apply (proj2 (HP x y m' Hx Hy)). exact Hm'.
    + intros m' Hm'. apply (proj2 (HQ x y m' Hx Hy)). exact Hm'.
Qed.

Lemma formula_family_rename_stable_impl_exact D P Q :
  formula_family_support_exact_on D P →
  formula_family_support_exact_on D Q →
  formula_family_rename_stable_on D P →
  formula_family_rename_stable_on D Q →
  formula_family_rename_stable_on D (fun x => FImpl (P x) (Q x)).
Proof.
  intros HPsupp HQsupp HP HQ.
  unfold formula_family_rename_stable_on in *.
  intros x y n Hx Hy. simpl. split; intros Hmodel.
  - pose proof (res_models_with_store_fuel_scoped
      (formula_measure (FImpl (formula_rename_atom x y (P x))
         (formula_rename_atom x y (Q x)))) ∅ n
      (FImpl (formula_rename_atom x y (P x))
         (formula_rename_atom x y (Q x))) Hmodel) as Hscope.
    unfold formula_scoped_in_world in Hscope.
    eapply res_models_impl_map; [| | | exact Hmodel].
    + unfold formula_scoped_in_world. simpl.
      assert (HPscope : formula_fv (P y) ⊆ world_dom (n : World)).
      { eapply support_exact_renamed_scope_to_target_scope; [exact HPsupp | exact Hx | exact Hy |].
        simpl in Hscope. set_solver. }
      assert (HQscope : formula_fv (Q y) ⊆ world_dom (n : World)).
      { eapply support_exact_renamed_scope_to_target_scope; [exact HQsupp | exact Hx | exact Hy |].
        simpl in Hscope. set_solver. }
      set_solver.
    + intros m' _ HPy. apply (proj2 (HP x y m' Hx Hy)). exact HPy.
    + intros m' _ HQx. apply (proj1 (HQ x y m' Hx Hy)). exact HQx.
  - pose proof (res_models_with_store_fuel_scoped
      (formula_measure (FImpl (P y) (Q y))) ∅ n
      (FImpl (P y) (Q y)) Hmodel) as Hscope.
    unfold formula_scoped_in_world in Hscope.
    eapply res_models_impl_map; [| | | exact Hmodel].
    + unfold formula_scoped_in_world. simpl.
      assert (HPscope : formula_fv (formula_rename_atom x y (P x)) ⊆ world_dom (n : World)).
      { eapply support_exact_target_scope_to_renamed_scope; [exact HPsupp | exact Hx | exact Hy |].
        simpl in Hscope. set_solver. }
      assert (HQscope : formula_fv (formula_rename_atom x y (Q x)) ⊆ world_dom (n : World)).
      { eapply support_exact_target_scope_to_renamed_scope; [exact HQsupp | exact Hx | exact Hy |].
        simpl in Hscope. set_solver. }
      set_solver.
    + intros m' _ HPx. apply (proj1 (HP x y m' Hx Hy)). exact HPx.
    + intros m' _ HQy. apply (proj2 (HQ x y m' Hx Hy)). exact HQy.
Qed.

Lemma formula_family_rename_stable_wand_exact D P Q :
  formula_family_support_exact_on D P →
  formula_family_support_exact_on D Q →
  formula_family_rename_stable_on D P →
  formula_family_rename_stable_on D Q →
  formula_family_rename_stable_on D (fun x => FWand (P x) (Q x)).
Proof.
  intros HPsupp HQsupp HP HQ.
  unfold formula_family_rename_stable_on in *.
  intros x y n Hx Hy. simpl. split; intros Hmodel.
  - pose proof (res_models_with_store_fuel_scoped
      (formula_measure (FWand (formula_rename_atom x y (P x))
         (formula_rename_atom x y (Q x)))) ∅ n
      (FWand (formula_rename_atom x y (P x))
         (formula_rename_atom x y (Q x))) Hmodel) as Hscope.
    unfold formula_scoped_in_world in Hscope.
    eapply res_models_wand_map; [| | | exact Hmodel].
    + unfold formula_scoped_in_world. simpl.
      assert (HPscope : formula_fv (P y) ⊆ world_dom (n : World)).
      { eapply support_exact_renamed_scope_to_target_scope; [exact HPsupp | exact Hx | exact Hy |].
        simpl in Hscope. set_solver. }
      assert (HQscope : formula_fv (Q y) ⊆ world_dom (n : World)).
      { eapply support_exact_renamed_scope_to_target_scope; [exact HQsupp | exact Hx | exact Hy |].
        simpl in Hscope. set_solver. }
      set_solver.
    + intros m' _ HPy. apply (proj2 (HP x y m' Hx Hy)). exact HPy.
    + intros m' Hc HQx.
      apply (proj1 (HQ x y (res_product m' n Hc) Hx Hy)). exact HQx.
  - pose proof (res_models_with_store_fuel_scoped
      (formula_measure (FWand (P y) (Q y))) ∅ n
      (FWand (P y) (Q y)) Hmodel) as Hscope.
    unfold formula_scoped_in_world in Hscope.
    eapply res_models_wand_map; [| | | exact Hmodel].
    + unfold formula_scoped_in_world. simpl.
      assert (HPscope : formula_fv (formula_rename_atom x y (P x)) ⊆ world_dom (n : World)).
      { eapply support_exact_target_scope_to_renamed_scope; [exact HPsupp | exact Hx | exact Hy |].
        simpl in Hscope. set_solver. }
      assert (HQscope : formula_fv (formula_rename_atom x y (Q x)) ⊆ world_dom (n : World)).
      { eapply support_exact_target_scope_to_renamed_scope; [exact HQsupp | exact Hx | exact Hy |].
        simpl in Hscope. set_solver. }
      set_solver.
    + intros m' _ HPx. apply (proj1 (HP x y m' Hx Hy)). exact HPx.
    + intros m' Hc HQy.
      apply (proj2 (HQ x y (res_product m' n Hc) Hx Hy)). exact HQy.
Qed.

Lemma denot_ty_fuel_arrow_body_family_rename_stable
    gas (Σ : gmap atom ty) τx τ e :
  cty_measure τx <= gas →
  cty_measure τ <= gas →
  basic_choice_ty (dom Σ) τx →
  fv_tm e ⊆ dom Σ →
  Σ ⊢ₑ e ⋮ (erase_ty τx →ₜ erase_ty τ) →
  (∀ x, x ∉ dom Σ → basic_choice_ty (dom Σ ∪ {[x]}) ({0 ~> x} τ)) →
  formula_family_rename_stable_on (dom Σ) (fun x =>
    FImpl
      (denot_ty_fuel gas (<[x := erase_ty τx]> Σ)
        τx (tret (vfvar x)))
      (denot_ty_fuel gas (<[x := erase_ty τx]> Σ)
        ({0 ~> x} τ) (tapp_tm e (vfvar x)))).
Proof.
  intros Hgasx Hgas Hbasicx Hfve Htye Hbasic_body.
  apply formula_family_rename_stable_impl_exact.
  - eapply denot_ty_fuel_fresh_arg_family_support_exact; eauto.
  - eapply denot_ty_fuel_fresh_result_family_support_exact; eauto.
  - eapply denot_ty_fuel_fresh_arg_family_rename_stable; eauto.
  - eapply denot_ty_fuel_fresh_result_family_rename_stable; eauto.
Qed.

Lemma denot_ty_fuel_wand_body_family_rename_stable
    gas (Σ : gmap atom ty) τx τ e :
  cty_measure τx <= gas →
  cty_measure τ <= gas →
  basic_choice_ty (dom Σ) τx →
  fv_tm e ⊆ dom Σ →
  Σ ⊢ₑ e ⋮ (erase_ty τx →ₜ erase_ty τ) →
  (∀ x, x ∉ dom Σ → basic_choice_ty (dom Σ ∪ {[x]}) ({0 ~> x} τ)) →
  formula_family_rename_stable_on (dom Σ) (fun x =>
    FWand
      (denot_ty_fuel gas (<[x := erase_ty τx]> Σ)
        τx (tret (vfvar x)))
      (denot_ty_fuel gas (<[x := erase_ty τx]> Σ)
        ({0 ~> x} τ) (tapp_tm e (vfvar x)))).
Proof.
  intros Hgasx Hgas Hbasicx Hfve Htye Hbasic_body.
  apply formula_family_rename_stable_wand_exact.
  - eapply denot_ty_fuel_fresh_arg_family_support_exact; eauto.
  - eapply denot_ty_fuel_fresh_result_family_support_exact; eauto.
  - eapply denot_ty_fuel_fresh_arg_family_rename_stable; eauto.
  - eapply denot_ty_fuel_fresh_result_family_rename_stable; eauto.
Qed.
