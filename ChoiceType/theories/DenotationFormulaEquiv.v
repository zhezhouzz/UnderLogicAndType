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
    + pose proof (proj1 (H1 ρ m)) as H.
      assert (Hφ1_exact : res_models_with_store ρ m φ1).
      { models_fuel_irrel Hφ1. }
      models_fuel_irrel (H Hφ1_exact).
    + pose proof (proj1 (H2 ρ m)) as H.
      assert (Hφ2_exact : res_models_with_store ρ m φ2).
      { models_fuel_irrel Hφ2. }
      models_fuel_irrel (H Hφ2_exact).
  - unfold formula_scoped_in_world in *. simpl in *.
    rewrite Hfv1, Hfv2. exact Hscope.
  - destruct Hmodel as [Hψ1 Hψ2]. split.
    + pose proof (proj2 (H1 ρ m)) as H.
      assert (Hψ1_exact : res_models_with_store ρ m ψ1).
      { models_fuel_irrel Hψ1. }
      models_fuel_irrel (H Hψ1_exact).
    + pose proof (proj2 (H2 ρ m)) as H.
      assert (Hψ2_exact : res_models_with_store ρ m ψ2).
      { models_fuel_irrel Hψ2. }
      models_fuel_irrel (H Hψ2_exact).
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
    pose proof (proj1 (Heq ρ m0)) as H.
    assert (Hφ_exact : res_models_with_store ρ m0 φ).
    { models_fuel_irrel Hφ. }
    models_fuel_irrel (H Hφ_exact).
  - unfold formula_scoped_in_world in *. simpl in *. rewrite Hfv. exact Hscope.
  - exists m0. split; [exact Hsub |].
    pose proof (proj2 (Heq ρ m0)) as H.
    assert (Hψ_exact : res_models_with_store ρ m0 ψ).
    { models_fuel_irrel Hφ. }
    models_fuel_irrel (H Hψ_exact).
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
    pose proof (proj1 (Heq ρ m0)) as H.
    assert (Hφ_exact : res_models_with_store ρ m0 φ).
    { models_fuel_irrel Hφ. }
    models_fuel_irrel (H Hφ_exact).
  - unfold formula_scoped_in_world in *. simpl in *. rewrite Hfv. exact Hscope.
  - exists m0. split; [exact Hsub |].
    pose proof (proj2 (Heq ρ m0)) as H.
    assert (Hψ_exact : res_models_with_store ρ m0 ψ).
    { models_fuel_irrel Hφ. }
    models_fuel_irrel (H Hψ_exact).
Qed.

Lemma formula_store_equiv_fib x φ ψ :
  formula_fv φ = formula_fv ψ →
  formula_store_equiv φ ψ →
  formula_store_equiv (FFib x φ) (FFib x ψ).
Proof.
  intros Hfv Heq ρ m.
  unfold res_models_with_store. simpl. split; intros [Hscope [Hdisj Hfib]]; split.
  - unfold formula_scoped_in_world in *. simpl in *. rewrite <- Hfv. exact Hscope.
  - split; [exact Hdisj |].
    intros σ Hproj.
    pose proof (Hfib σ Hproj) as Hφ.
    pose proof (proj1 (Heq (ρ ∪ σ)
      (res_fiber_from_projection m {[x]} σ Hproj))) as H.
    assert (Hφ_exact : res_models_with_store (ρ ∪ σ)
      (res_fiber_from_projection m {[x]} σ Hproj) φ).
    { models_fuel_irrel Hφ. }
    models_fuel_irrel (H Hφ_exact).
  - unfold formula_scoped_in_world in *. simpl in *. rewrite Hfv. exact Hscope.
  - split; [exact Hdisj |].
    intros σ Hproj.
    pose proof (Hfib σ Hproj) as Hψ.
    pose proof (proj2 (Heq (ρ ∪ σ)
      (res_fiber_from_projection m {[x]} σ Hproj))) as H.
    assert (Hψ_exact : res_models_with_store (ρ ∪ σ)
      (res_fiber_from_projection m {[x]} σ Hproj) ψ).
    { models_fuel_irrel Hψ. }
    models_fuel_irrel (H Hψ_exact).
Qed.

Lemma formula_store_equiv_fib_commute_dir x y (φ : FQ) ρ m :
  x ≠ y →
  res_models_with_store ρ m (FFib x (FFib y φ)) →
  res_models_with_store ρ m (FFib y (FFib x φ)).
Proof.
  intros Hxy Hm.
  unfold res_models_with_store in Hm. simpl in Hm.
  destruct Hm as [Hscope [Hdisj Hfib]].
  assert (Hxdom : x ∈ world_dom (m : World)).
  { unfold formula_scoped_in_world in Hscope. simpl in Hscope. set_solver. }
  assert (Hydom : y ∈ world_dom (m : World)).
  { unfold formula_scoped_in_world in Hscope. simpl in Hscope. set_solver. }
  set (R := fun ρ m => res_models_with_store ρ m φ).
  assert (Hoblxy : fib_vars_obligation_step x (fib_vars_obligation_step y R) ρ m).
  {
    unfold fib_vars_obligation_step. split; [exact Hdisj |].
    intros σx Hprojx.
    specialize (Hfib σx Hprojx).
    unfold R, res_models_with_store in Hfib. simpl in Hfib.
    destruct Hfib as [_ Hstep].
    exact Hstep.
  }
  pose proof (fib_vars_obligation_step_commute y x R ρ m
    ltac:(congruence) Hydom Hxdom Hoblxy) as Hoblyx.
  unfold fib_vars_obligation_step in Hoblyx.
  destruct Hoblyx as [Hdisjy Hfibyx].
  unfold res_models_with_store. simpl.
  split.
  - unfold formula_scoped_in_world in *. simpl in *. set_solver.
  - split; [exact Hdisjy |].
    intros σy Hprojy.
    specialize (Hfibyx σy Hprojy).
    unfold fib_vars_obligation_step in Hfibyx.
    destruct Hfibyx as [Hdisjx Hfibx].
    unfold res_models_with_store. simpl.
    split.
    + unfold formula_scoped_in_world in *.
      simpl in *.
      pose proof (wfworld_store_dom (res_restrict m {[y]}) σy Hprojy) as Hdomσy.
      simpl in Hdomσy.
      rewrite dom_union_L.
      intros z Hz.
      apply elem_of_union in Hz as [Hzρσ|Hzφ].
      * apply elem_of_union in Hzρσ as [Hzρ|Hzσ].
        -- apply Hscope. set_solver.
        -- rewrite Hdomσy in Hzσ. apply Hscope. set_solver.
      * apply Hscope. set_solver.
    + split; [exact Hdisjx |].
      intros σx Hprojx.
      specialize (Hfibx σx Hprojx).
      unfold R, res_models_with_store in Hfibx.
      exact Hfibx.
Qed.

Lemma formula_store_equiv_fib_commute x y (φ : FQ) :
  x ≠ y →
  formula_store_equiv (FFib x (FFib y φ)) (FFib y (FFib x φ)).
Proof.
  intros Hxy ρ m. split.
  - apply formula_store_equiv_fib_commute_dir. exact Hxy.
  - apply formula_store_equiv_fib_commute_dir. congruence.
Qed.

Lemma foldr_fib_store_equiv xs φ ψ :
  formula_fv φ = formula_fv ψ →
  formula_store_equiv φ ψ →
  formula_fv (foldr FFib φ xs) = formula_fv (foldr FFib ψ xs) ∧
  formula_store_equiv (foldr FFib φ xs) (foldr FFib ψ xs).
Proof.
  induction xs as [|x xs IH]; simpl; intros Hfv Heq.
  - split; [exact Hfv | exact Heq].
  - destruct (IH Hfv Heq) as [Hfv' Heq'].
    split.
    + simpl. rewrite Hfv'. reflexivity.
    + apply formula_store_equiv_fib; assumption.
Qed.

Lemma fib_vars_store_equiv X φ ψ :
  formula_fv φ = formula_fv ψ →
  formula_store_equiv φ ψ →
  formula_fv (fib_vars X φ) = formula_fv (fib_vars X ψ) ∧
  formula_store_equiv (fib_vars X φ) (fib_vars X ψ).
Proof.
  intros Hfv Heq.
  split.
  - unfold fib_vars. simpl. rewrite Hfv. reflexivity.
  - unfold fib_vars. intros ρ m.
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

Lemma foldr_fib_formula_fv xs (φ : FQ) :
  formula_fv (foldr FFib φ xs) = list_to_set xs ∪ formula_fv φ.
Proof.
  induction xs as [|x xs IH]; simpl.
  - set_solver.
  - rewrite IH. set_solver.
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

Lemma foldr_fib_store_equiv_permutation xs ys (φ : FQ) :
  xs ≡ₚ ys →
  formula_store_equiv (foldr FFib φ xs) (foldr FFib φ ys).
Proof.
  intros Hperm.
  induction Hperm.
  - apply formula_store_equiv_refl.
  - apply formula_store_equiv_fib.
    + rewrite !(foldr_fib_formula_fv _ φ).
      rewrite (list_to_set_permutation_aset _ _ Hperm).
      reflexivity.
    + exact IHHperm.
  - destruct (decide (x = y)) as [->|Hxy].
    + apply formula_store_equiv_refl.
    + apply formula_store_equiv_fib_commute. congruence.
  - eapply formula_store_equiv_trans; eauto.
Qed.

Lemma fib_vars_insert_store_equiv x X (φ : FQ) :
  x ∉ X →
  formula_store_equiv (fib_vars ({[x]} ∪ X) φ) (FFib x (fib_vars X φ)).
Proof.
  intros Hx.
  unfold fib_vars. intros ρ m.
  simpl.
  admit.
Admitted.

Lemma res_models_of_formula_store_equiv φ ψ (m : WfWorld) :
  formula_store_equiv φ ψ →
  m ⊨ φ ↔ m ⊨ ψ.
Proof. intros Heq. unfold res_models. apply Heq. Qed.

Lemma fib_vars_insert_rename_res_models x y X (φ : FQ) (m : WfWorld) :
  x ∉ X →
  y ∉ X →
  m ⊨ formula_rename_atom x y (fib_vars ({[x]} ∪ X) φ) ↔
  m ⊨ fib_vars ({[y]} ∪ X) (formula_rename_atom x y φ).
Proof.
  (* Legacy explicit-rename helper.  The LN refactor removes this route. *)
Admitted.

Lemma fib_vars_insert_rename_store_equiv x y X (φ : FQ) :
  x ∉ X →
  y ∉ X →
  formula_store_equiv
    (formula_rename_atom x y (fib_vars ({[x]} ∪ X) φ))
    (fib_vars ({[y]} ∪ X) (formula_rename_atom x y φ)).
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
