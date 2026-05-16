(** * ChoiceType.DenotationFormulaEquiv

    Formula/store equivalence and fiber permutation helpers used by type denotation. *)

From LocallyNameless Require Import Tactics.
From ChoiceType Require Export DenotationFormula.
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

Lemma formula_store_equiv_refl φ : formula_store_equiv φ φ.
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

Lemma formula_store_equiv_or φ1 φ2 ψ1 ψ2 :
  formula_fv φ1 = formula_fv ψ1 →
  formula_fv φ2 = formula_fv ψ2 →
  formula_store_equiv φ1 ψ1 →
  formula_store_equiv φ2 ψ2 →
  formula_store_equiv (FOr φ1 φ2) (FOr ψ1 ψ2).
Proof.
  intros Hfv1 Hfv2 H1 H2 ρ m.
  unfold res_models_with_store. simpl. split; intros [Hscope Hmodel]; split.
  - unfold formula_scoped_in_world in *. simpl in *.
    rewrite <- Hfv1, <- Hfv2. exact Hscope.
  - destruct Hmodel as [Hφ1 | Hφ2].
    + left.
      pose proof (proj1 (H1 ρ m) ltac:(models_fuel_irrel Hφ1)) as H.
      models_fuel_irrel H.
    + right.
      pose proof (proj1 (H2 ρ m) ltac:(models_fuel_irrel Hφ2)) as H.
      models_fuel_irrel H.
  - unfold formula_scoped_in_world in *. simpl in *.
    rewrite Hfv1, Hfv2. exact Hscope.
  - destruct Hmodel as [Hψ1 | Hψ2].
    + left.
      pose proof (proj2 (H1 ρ m) ltac:(models_fuel_irrel Hψ1)) as H.
      models_fuel_irrel H.
    + right.
      pose proof (proj2 (H2 ρ m) ltac:(models_fuel_irrel Hψ2)) as H.
      models_fuel_irrel H.
Qed.

Lemma formula_store_equiv_impl φ1 φ2 ψ1 ψ2 :
  formula_fv φ1 = formula_fv ψ1 →
  formula_fv φ2 = formula_fv ψ2 →
  formula_store_equiv φ1 ψ1 →
  formula_store_equiv φ2 ψ2 →
  formula_store_equiv (FImpl φ1 φ2) (FImpl ψ1 ψ2).
Proof.
  intros Hfv1 Hfv2 H1 H2 ρ m.
  unfold res_models_with_store. simpl. split; intros [Hscope Hmodel]; split.
  - unfold formula_scoped_in_world in *. simpl in *.
    rewrite <- Hfv1, <- Hfv2. exact Hscope.
  - intros m' Hle Hψ1.
    pose proof (proj2 (H1 ρ m') ltac:(models_fuel_irrel Hψ1)) as Hφ1.
    specialize (Hmodel m' Hle ltac:(models_fuel_irrel Hφ1)) as Hφ2.
    pose proof (proj1 (H2 ρ m') ltac:(models_fuel_irrel Hφ2)) as Hψ2.
    models_fuel_irrel Hψ2.
  - unfold formula_scoped_in_world in *. simpl in *.
    rewrite Hfv1, Hfv2. exact Hscope.
  - intros m' Hle Hφ1.
    pose proof (proj1 (H1 ρ m') ltac:(models_fuel_irrel Hφ1)) as Hψ1.
    specialize (Hmodel m' Hle ltac:(models_fuel_irrel Hψ1)) as Hψ2.
    pose proof (proj2 (H2 ρ m') ltac:(models_fuel_irrel Hψ2)) as Hφ2.
    models_fuel_irrel Hφ2.
Qed.

Lemma formula_store_equiv_wand φ1 φ2 ψ1 ψ2 :
  formula_fv φ1 = formula_fv ψ1 →
  formula_fv φ2 = formula_fv ψ2 →
  formula_store_equiv φ1 ψ1 →
  formula_store_equiv φ2 ψ2 →
  formula_store_equiv (FWand φ1 φ2) (FWand ψ1 ψ2).
Proof.
  intros Hfv1 Hfv2 H1 H2 ρ m.
  unfold res_models_with_store. simpl. split; intros [Hscope Hmodel]; split.
  - unfold formula_scoped_in_world in *. simpl in *.
    rewrite <- Hfv1, <- Hfv2. exact Hscope.
  - intros m' Hc Hψ1.
    pose proof (proj2 (H1 ρ m') ltac:(models_fuel_irrel Hψ1)) as Hφ1.
    specialize (Hmodel m' Hc ltac:(models_fuel_irrel Hφ1)) as Hφ2.
    pose proof (proj1 (H2 ρ (res_product m' m Hc))
      ltac:(models_fuel_irrel Hφ2)) as Hψ2.
    models_fuel_irrel Hψ2.
  - unfold formula_scoped_in_world in *. simpl in *.
    rewrite Hfv1, Hfv2. exact Hscope.
  - intros m' Hc Hφ1.
    pose proof (proj1 (H1 ρ m') ltac:(models_fuel_irrel Hφ1)) as Hψ1.
    specialize (Hmodel m' Hc ltac:(models_fuel_irrel Hψ1)) as Hψ2.
    pose proof (proj2 (H2 ρ (res_product m' m Hc))
      ltac:(models_fuel_irrel Hψ2)) as Hφ2.
    models_fuel_irrel Hφ2.
Qed.

Lemma formula_store_equiv_plus φ1 φ2 ψ1 ψ2 :
  formula_fv φ1 = formula_fv ψ1 →
  formula_fv φ2 = formula_fv ψ2 →
  formula_store_equiv φ1 ψ1 →
  formula_store_equiv φ2 ψ2 →
  formula_store_equiv (FPlus φ1 φ2) (FPlus ψ1 ψ2).
Proof.
  intros Hfv1 Hfv2 H1 H2 ρ m.
  unfold res_models_with_store. simpl. split; intros [Hscope Hmodel]; split.
  - unfold formula_scoped_in_world in *. simpl in *.
    rewrite <- Hfv1, <- Hfv2. exact Hscope.
  - destruct Hmodel as [m1 [m2 [Hdef [Hle [Hφ1 Hφ2]]]]].
    exists m1, m2, Hdef. split; [exact Hle |]. split.
    + pose proof (proj1 (H1 ρ m1) ltac:(models_fuel_irrel Hφ1)) as H.
      models_fuel_irrel H.
    + pose proof (proj1 (H2 ρ m2) ltac:(models_fuel_irrel Hφ2)) as H.
      models_fuel_irrel H.
  - unfold formula_scoped_in_world in *. simpl in *.
    rewrite Hfv1, Hfv2. exact Hscope.
  - destruct Hmodel as [m1 [m2 [Hdef [Hle [Hψ1 Hψ2]]]]].
    exists m1, m2, Hdef. split; [exact Hle |]. split.
    + pose proof (proj2 (H1 ρ m1) ltac:(models_fuel_irrel Hψ1)) as H.
      models_fuel_irrel H.
    + pose proof (proj2 (H2 ρ m2) ltac:(models_fuel_irrel Hψ2)) as H.
      models_fuel_irrel H.
Qed.

Lemma formula_store_equiv_over φ ψ :
  formula_fv φ = formula_fv ψ →
  formula_store_equiv φ ψ →
  formula_store_equiv (FOver φ) (FOver ψ).
Proof.
  intros Hfv Heq ρ m.
  unfold res_models_with_store. simpl. split; intros [Hscope Hmodel]; split.
  - unfold formula_scoped_in_world in *. simpl in *.
    rewrite <- Hfv. exact Hscope.
  - destruct Hmodel as [m0 [Hsub Hφ]].
    exists m0. split; [exact Hsub |].
    pose proof (proj1 (Heq ρ m0) ltac:(models_fuel_irrel Hφ)) as Hψ.
    models_fuel_irrel Hψ.
  - unfold formula_scoped_in_world in *. simpl in *.
    rewrite Hfv. exact Hscope.
  - destruct Hmodel as [m0 [Hsub Hψ]].
    exists m0. split; [exact Hsub |].
    pose proof (proj2 (Heq ρ m0) ltac:(models_fuel_irrel Hψ)) as Hφ.
    models_fuel_irrel Hφ.
Qed.

Lemma formula_store_equiv_under φ ψ :
  formula_fv φ = formula_fv ψ →
  formula_store_equiv φ ψ →
  formula_store_equiv (FUnder φ) (FUnder ψ).
Proof.
  intros Hfv Heq ρ m.
  unfold res_models_with_store. simpl. split; intros [Hscope Hmodel]; split.
  - unfold formula_scoped_in_world in *. simpl in *.
    rewrite <- Hfv. exact Hscope.
  - destruct Hmodel as [m0 [Hsub Hφ]].
    exists m0. split; [exact Hsub |].
    pose proof (proj1 (Heq ρ m0) ltac:(models_fuel_irrel Hφ)) as Hψ.
    models_fuel_irrel Hψ.
  - unfold formula_scoped_in_world in *. simpl in *.
    rewrite Hfv. exact Hscope.
  - destruct Hmodel as [m0 [Hsub Hψ]].
    exists m0. split; [exact Hsub |].
    pose proof (proj2 (Heq ρ m0) ltac:(models_fuel_irrel Hψ)) as Hφ.
    models_fuel_irrel Hφ.
Qed.

Lemma formula_store_equiv_forall φ ψ :
  formula_fv φ = formula_fv ψ →
  (∀ y, formula_store_equiv (formula_open 0 y φ) (formula_open 0 y ψ)) →
  formula_store_equiv (FForall φ) (FForall ψ).
Proof.
  intros Hfv Hopen ρ m.
  unfold res_models_with_store. simpl. split; intros [Hscope Hmodel]; split.
  - unfold formula_scoped_in_world in *. simpl in *.
    rewrite <- Hfv. exact Hscope.
  - destruct Hmodel as [L [HL Hbody]].
    exists L. split; [exact HL |].
    intros y Hy my Hdom Hrestrict.
    specialize (Hbody y Hy my Hdom Hrestrict).
    pose proof (proj1 (Hopen y ρ my) ltac:(models_fuel_irrel Hbody)) as Hψ.
    models_fuel_irrel Hψ.
  - unfold formula_scoped_in_world in *. simpl in *.
    rewrite Hfv. exact Hscope.
  - destruct Hmodel as [L [HL Hbody]].
    exists L. split; [exact HL |].
    intros y Hy my Hdom Hrestrict.
    specialize (Hbody y Hy my Hdom Hrestrict).
    pose proof (proj2 (Hopen y ρ my) ltac:(models_fuel_irrel Hbody)) as Hφ.
    models_fuel_irrel Hφ.
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
  denot_lvars_norm.
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
