(** * ChoiceType.DenotationFormulaEquiv

    Formula/store equivalence and fiber permutation helpers used by type denotation. *)

From LocallyNameless Require Import Tactics.
From ChoiceType Require Export DenotationExprProps.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

Local Notation FQ := FormulaQ.

Definition formula_equiv (φ ψ : FQ) : Prop :=
  (φ ⊫ ψ) ∧ (ψ ⊫ φ).

Notation "φ '⊣⊢' ψ" := (formula_equiv φ ψ)
  (at level 85, no associativity).

Definition formula_store_equiv (φ ψ : FQ) : Prop :=
  ∀ ρ m, res_models_with_store ρ m φ ↔ res_models_with_store ρ m ψ.

Lemma formula_equiv_refl φ : φ ⊣⊢ φ.
Proof. unfold formula_equiv, entails. hauto. Qed.

Lemma formula_equiv_sym φ ψ :
  φ ⊣⊢ ψ → ψ ⊣⊢ φ.
Proof. unfold formula_equiv. hauto. Qed.

Lemma formula_equiv_trans φ ψ χ :
  φ ⊣⊢ ψ → ψ ⊣⊢ χ → φ ⊣⊢ χ.
Proof. unfold formula_equiv, entails. hauto. Qed.

Lemma formula_store_equiv_refl φ : formula_store_equiv φ φ.
Proof. unfold formula_store_equiv. hauto. Qed.

Lemma formula_store_equiv_sym φ ψ :
  formula_store_equiv φ ψ → formula_store_equiv ψ φ.
Proof. unfold formula_store_equiv. hauto. Qed.

Lemma formula_store_equiv_trans φ ψ χ :
  formula_store_equiv φ ψ →
  formula_store_equiv ψ χ →
  formula_store_equiv φ χ.
Proof. unfold formula_store_equiv. hauto. Qed.

Lemma formula_store_equiv_and φ1 φ2 ψ1 ψ2 :
  formula_fv φ1 = formula_fv ψ1 →
  formula_fv φ2 = formula_fv ψ2 →
  formula_store_equiv φ1 ψ1 →
  formula_store_equiv φ2 ψ2 →
  formula_store_equiv (FAnd φ1 φ2) (FAnd ψ1 ψ2).
Proof.
  intros Hfv1 Hfv2 H1 H2 ρ m.
  unfold res_models_with_store. simpl. split; intros [Hscope Hmodel]; split.
  - unfold formula_scoped_in_world in *. simpl in *.
    rewrite <- Hfv1, <- Hfv2. exact Hscope.
  - destruct Hmodel as [Hφ1 Hφ2]. split.
    + pose proof (proj1 (H1 ρ m) ltac:(models_fuel_irrel Hφ1)) as H.
      models_fuel_irrel H.
    + pose proof (proj1 (H2 ρ m) ltac:(models_fuel_irrel Hφ2)) as H.
      models_fuel_irrel H.
  - unfold formula_scoped_in_world in *. simpl in *.
    rewrite Hfv1, Hfv2. exact Hscope.
  - destruct Hmodel as [Hψ1 Hψ2]. split.
    + pose proof (proj2 (H1 ρ m) ltac:(models_fuel_irrel Hψ1)) as H.
      models_fuel_irrel H.
    + pose proof (proj2 (H2 ρ m) ltac:(models_fuel_irrel Hψ2)) as H.
      models_fuel_irrel H.
Qed.

Lemma formula_store_equiv_over φ ψ :
  formula_fv φ = formula_fv ψ →
  formula_store_equiv φ ψ →
  formula_store_equiv (FOver φ) (FOver ψ).
Proof.
  intros Hfv Heq ρ m.
  unfold res_models_with_store. simpl. split; intros [Hscope [m0 [Hsub Hφ]]]; split.
  - unfold formula_scoped_in_world in *. simpl in *. rewrite <- Hfv. exact Hscope.
  - exists m0. split; [exact Hsub |].
    pose proof (proj1 (Heq ρ m0) ltac:(models_fuel_irrel Hφ)) as H.
    models_fuel_irrel H.
  - unfold formula_scoped_in_world in *. simpl in *. rewrite Hfv. exact Hscope.
  - exists m0. split; [exact Hsub |].
    pose proof (proj2 (Heq ρ m0) ltac:(models_fuel_irrel Hφ)) as H.
    models_fuel_irrel H.
Qed.

Lemma formula_store_equiv_under φ ψ :
  formula_fv φ = formula_fv ψ →
  formula_store_equiv φ ψ →
  formula_store_equiv (FUnder φ) (FUnder ψ).
Proof.
  intros Hfv Heq ρ m.
  unfold res_models_with_store. simpl. split; intros [Hscope [m0 [Hsub Hφ]]]; split.
  - unfold formula_scoped_in_world in *. simpl in *. rewrite <- Hfv. exact Hscope.
  - exists m0. split; [exact Hsub |].
    pose proof (proj1 (Heq ρ m0) ltac:(models_fuel_irrel Hφ)) as H.
    models_fuel_irrel H.
  - unfold formula_scoped_in_world in *. simpl in *. rewrite Hfv. exact Hscope.
  - exists m0. split; [exact Hsub |].
    pose proof (proj2 (Heq ρ m0) ltac:(models_fuel_irrel Hφ)) as H.
    models_fuel_irrel H.
Qed.

Lemma fib_vars_store_equiv D φ ψ :
  formula_fv φ = formula_fv ψ →
  formula_store_equiv φ ψ →
  formula_fv (FFibVars D φ) =
    formula_fv (FFibVars D ψ) ∧
  formula_store_equiv
    (FFibVars D φ)
    (FFibVars D ψ).
Proof.
  intros Hfv Heq.
  split.
  - simpl. rewrite Hfv. reflexivity.
  - intros ρ m.
    unfold res_models_with_store. simpl.
    split; intros [Hscope [Hdisj Hfib]]; split.
    + unfold formula_scoped_in_world in *. simpl in *. rewrite <- Hfv. exact Hscope.
    + split; [exact Hdisj |].
      intros σ Hproj.
      pose proof (Hfib σ Hproj) as Hp.
      unfold res_models_with_store in Heq.
      exact (proj1 (Heq _ _) Hp).
    + unfold formula_scoped_in_world in *. simpl in *. rewrite Hfv. exact Hscope.
    + split; [exact Hdisj |].
      intros σ Hproj.
      pose proof (Hfib σ Hproj) as Hp.
      unfold res_models_with_store in Heq.
      exact (proj2 (Heq _ _) Hp).
Qed.

Lemma list_to_set_permutation_aset (xs ys : list atom) :
  xs ≡ₚ ys →
  (list_to_set xs : aset) = list_to_set ys.
Proof.
  intros Hperm.
  apply set_eq. intros z.
  rewrite !elem_of_list_to_set.
  by rewrite Hperm.
Qed.

Lemma fib_vars_insert_store_equiv x D (φ : FQ) :
  x ∉ lvars_fv D →
  formula_store_equiv
    (FFibVars ({[LVFree x]} ∪ D) φ)
    (FFibVars ({[LVFree x]} ∪ D) φ).
Proof.
  intros _. apply formula_store_equiv_refl.
Qed.

Lemma res_models_of_formula_store_equiv φ ψ (m : WfWorld) :
  formula_store_equiv φ ψ →
  m ⊨ φ ↔ m ⊨ ψ.
Proof. intros Heq. unfold res_models. apply Heq. Qed.

Lemma FExprContIn_post_open_store_equiv
    (Σ : gmap atom ty) e (P Q : FQ) :
  formula_fv P = formula_fv Q →
  (∀ ν, ν ∉ dom Σ →
    formula_fv (formula_open 0 ν P) = formula_fv (formula_open 0 ν Q)) →
  (∀ ν, ν ∉ dom Σ →
    formula_store_equiv (formula_open 0 ν P) (formula_open 0 ν Q)) →
  formula_store_equiv (FExprContIn Σ e P) (FExprContIn Σ e Q).
Proof.
  intros Hfv Hopen_fv Heq ρ m.
  unfold FExprContIn, res_models_with_store.
  denot_sugar_norm.
  cbn [formula_measure res_models_with_store_fuel formula_scoped_in_world
    formula_fv formula_open].
  split; intros [Hscope [L [HLdom Hforall]]]; split.
  - unfold formula_scoped_in_world in *.
    cbn [formula_fv] in *.
    rewrite <- Hfv. exact Hscope.
  - exists (L ∪ dom Σ). split.
    { intros z Hz. apply elem_of_union. left. exact (HLdom z Hz). }
    intros y Hy m' Hdom Hrestrict.
    rewrite not_elem_of_union in Hy.
    destruct Hy as [HyL HyΣ].
    specialize (Hforall y HyL m' Hdom Hrestrict).
    cbn [formula_open formula_measure res_models_with_store_fuel
      formula_scoped_in_world formula_fv] in *.
    destruct Hforall as [HscopeImp Himpl].
    split.
    + unfold formula_scoped_in_world in *.
      cbn [formula_fv] in *.
      rewrite <- Hopen_fv by exact HyΣ.
      exact HscopeImp.
    + intros n Hle HA.
      assert (HA_src : res_models_with_store_fuel
        (0 + formula_measure (FExprResultOn (into_lvars Σ) e) +
          formula_measure P)
        ρ n (formula_open 0 y (FExprResultOn (into_lvars Σ) e))).
      { models_fuel_irrel HA. }
      specialize (Himpl n Hle HA_src) as HP.
      pose proof (Heq y HyΣ ρ n) as HyEq.
      unfold res_models_with_store in HyEq.
      assert (HQ_exact :
        res_models_with_store_fuel (formula_measure (formula_open 0 y Q))
          ρ n (formula_open 0 y Q)).
      {
        apply (proj1 HyEq).
        eapply res_models_with_store_fuel_irrel; [| | exact HP];
          rewrite formula_open_preserves_measure; simpl; lia.
      }
      eapply res_models_with_store_fuel_irrel; [| | exact HQ_exact];
        rewrite formula_open_preserves_measure; simpl; lia.
  - unfold formula_scoped_in_world in *.
    cbn [formula_fv] in *.
    rewrite Hfv. exact Hscope.
  - exists (L ∪ dom Σ). split.
    { intros z Hz. apply elem_of_union. left. exact (HLdom z Hz). }
    intros y Hy m' Hdom Hrestrict.
    rewrite not_elem_of_union in Hy.
    destruct Hy as [HyL HyΣ].
    specialize (Hforall y HyL m' Hdom Hrestrict).
    cbn [formula_open formula_measure res_models_with_store_fuel
      formula_scoped_in_world formula_fv] in *.
    destruct Hforall as [HscopeImp Himpl].
    split.
    + unfold formula_scoped_in_world in *.
      cbn [formula_fv] in *.
      rewrite Hopen_fv by exact HyΣ.
      exact HscopeImp.
    + intros n Hle HA.
      assert (HA_src : res_models_with_store_fuel
        (0 + formula_measure (FExprResultOn (into_lvars Σ) e) +
          formula_measure Q)
        ρ n (formula_open 0 y (FExprResultOn (into_lvars Σ) e))).
      { models_fuel_irrel HA. }
      specialize (Himpl n Hle HA_src) as HQ.
      pose proof (Heq y HyΣ ρ n) as HyEq.
      unfold res_models_with_store in HyEq.
      assert (HP_exact :
        res_models_with_store_fuel (formula_measure (formula_open 0 y P))
          ρ n (formula_open 0 y P)).
      {
        apply (proj2 HyEq).
        eapply res_models_with_store_fuel_irrel; [| | exact HQ];
          rewrite formula_open_preserves_measure; simpl; lia.
      }
      eapply res_models_with_store_fuel_irrel; [| | exact HP_exact];
        rewrite formula_open_preserves_measure; simpl; lia.
Qed.

Lemma fib_vars_insert_rename_res_models x y X (φ : FQ) (m : WfWorld) :
  x ∉ X →
  y ∉ X →
  m ⊨ formula_rename_atom x y
        (FFibVars (lvars_of_atoms ({[x]} ∪ X)) φ) ↔
  m ⊨ FFibVars (lvars_of_atoms ({[y]} ∪ X))
        (formula_rename_atom x y φ).
Proof.
  (* Legacy explicit-rename helper.  The LN refactor removes this route. *)
Admitted.

Lemma fib_vars_insert_rename_store_equiv x y X (φ : FQ) :
  x ∉ X →
  y ∉ X →
  formula_store_equiv
    (formula_rename_atom x y (FFibVars (lvars_of_atoms ({[x]} ∪ X)) φ))
    (FFibVars (lvars_of_atoms ({[y]} ∪ X)) (formula_rename_atom x y φ)).
Proof.
  (* Legacy explicit-rename helper.  The LN refactor removes this route. *)
Admitted.

Lemma store_swap_restrict_fresh x y (s : Store) X :
  x ∉ X →
  y ∉ X →
  store_swap x y (store_restrict s X) = store_restrict s X.
Proof.
  intros Hx Hy.
  apply (map_eq (M := gmap atom)). intros z.
  rewrite store_swap_lookup_inv, !store_restrict_lookup.
  destruct (decide (z ∈ X)) as [Hz|Hz];
    destruct (decide (atom_swap x y z ∈ X)) as [Hzs|Hzs].
  - rewrite atom_swap_fresh by set_solver. reflexivity.
  - exfalso. apply Hzs.
    rewrite atom_swap_fresh by set_solver. exact Hz.
  - exfalso. apply Hz.
    assert (Hzz : atom_swap x y (atom_swap x y z) ∈ X).
    {
      assert (Hsx : atom_swap x y z ≠ x).
      { intros Heq. apply Hx. rewrite <- Heq. exact Hzs. }
      assert (Hsy : atom_swap x y z ≠ y).
      { intros Heq. apply Hy. rewrite <- Heq. exact Hzs. }
      rewrite atom_swap_fresh by assumption.
      exact Hzs.
    }
    rewrite atom_swap_involutive in Hzz. exact Hzz.
  - reflexivity.
Qed.

Lemma res_models_rename_atom_fresh x y (φ : FQ) (m : WfWorld) :
  x ∉ formula_fv φ →
  y ∉ formula_fv φ →
  m ⊨ formula_rename_atom x y φ ↔ m ⊨ φ.
Proof.
  intros Hx Hy.
  rewrite res_models_swap.
  transitivity (res_restrict (res_swap x y m) (formula_fv φ) ⊨ φ).
  - apply res_models_minimal_on. reflexivity.
  - transitivity (res_restrict m (formula_fv φ) ⊨ φ).
    + assert (Hrestrict :
        res_restrict (res_swap x y m) (formula_fv φ) =
        res_restrict m (formula_fv φ)).
      {
        rewrite <- (aset_swap_fresh x y (formula_fv φ)) at 1 by assumption.
        rewrite res_restrict_swap.
        apply wfworld_ext. apply world_ext.
        - simpl. rewrite aset_swap_fresh by set_solver. reflexivity.
        - intros σ. simpl. split.
          + intros [σ0 [[σm [Hσm Hswap]] Hσ0]].
            subst σ0.
            exists σm. split; [exact Hσm |].
            rewrite <- Hσ0.
            rewrite store_swap_restrict_fresh by assumption.
            reflexivity.
          + intros [σm [Hσm Hrestrict]].
            exists (store_restrict σm (formula_fv φ)).
            split.
            * exists σm. split; [exact Hσm | reflexivity].
            * rewrite <- Hrestrict.
              rewrite store_swap_restrict_fresh by assumption.
              reflexivity.
      }
      rewrite Hrestrict. reflexivity.
    + symmetry. apply res_models_minimal_on. reflexivity.
Qed.
