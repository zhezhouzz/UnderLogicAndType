(** * ChoiceType.TypeDenotation.FormulaEquiv

    Formula/store equivalence and fiber permutation helpers used by type denotation. *)

From LocallyNameless Require Import Tactics.
From ChoiceType Require Export TypeDenotation.Formula.
From ChoiceType Require Import BasicStore LocallyNamelessProps.
From Stdlib Require Import Classes.Morphisms Classes.RelationClasses.

Local Notation FQ := FormulaQ.

Class DenotEquiv (A : Type) := denot_equiv : relation A.

Notation "x ≈d y" := (denot_equiv x y)
  (at level 70, no associativity).

Ltac type_denot_store_norm :=
  repeat change (into_lvars ?D) with D in *;
  repeat rewrite ?store_restrict_restrict in *.

Lemma lvars_fv_open_has_bv k x D :
  k ∈ lvars_bv D →
  lvars_fv (lvars_open k x D) = lvars_fv D ∪ {[x]}.
Proof.
  intros Hk.
  rewrite lvars_fv_open.
  destruct decide as [_|Hbad]; [reflexivity | set_solver].
Qed.

Lemma lvars_fv_open_no_bv k x D :
  k ∉ lvars_bv D →
  lvars_fv (lvars_open k x D) = lvars_fv D.
Proof.
  intros Hk.
  rewrite lvars_fv_open.
  destruct decide as [Hbad|_]; [set_solver | set_solver].
Qed.

Lemma store_restrict_open_old k x D (σ : gmap atom value) :
  store_restrict (store_restrict σ (lvars_fv (lvars_open k x D)))
    (lvars_fv D) =
  store_restrict σ (lvars_fv D).
Proof.
  rewrite store_restrict_restrict.
  rewrite lvars_fv_open.
  destruct decide; f_equal; set_solver.
Qed.

Lemma store_restrict_open_old_has_bv k x D (σ : gmap atom value) :
  k ∈ lvars_bv D →
  store_restrict (store_restrict σ (lvars_fv (lvars_open k x D)))
    (lvars_fv D) =
  store_restrict σ (lvars_fv D).
Proof.
  intros _. apply store_restrict_open_old.
Qed.

Lemma store_restrict_open_open_old k x D (σ : gmap atom value) :
  store_restrict
    (store_restrict (store_restrict σ (lvars_fv (lvars_open k x D)))
      (lvars_fv (lvars_open k x D)))
    (lvars_fv D) =
  store_restrict σ (lvars_fv D).
Proof.
  rewrite store_restrict_twice_same.
  apply store_restrict_open_old.
Qed.

Lemma store_restrict_open2_old k x j y D (σ : gmap atom value) :
  store_restrict
    (store_restrict σ (lvars_fv (lvars_open j y (lvars_open k x D))))
    (lvars_fv D) =
  store_restrict σ (lvars_fv D).
Proof.
  rewrite store_restrict_restrict.
  rewrite !lvars_fv_open.
  f_equal. set_solver.
Qed.

Lemma store_restrict_open2_open_old k x j y D (σ : gmap atom value) :
  store_restrict
    (store_restrict
      (store_restrict σ (lvars_fv (lvars_open j y (lvars_open k x D))))
      (lvars_fv (lvars_open k x D)))
    (lvars_fv D) =
  store_restrict σ (lvars_fv D).
Proof.
  rewrite !store_restrict_restrict.
  rewrite !lvars_fv_open.
  f_equal. set_solver.
Qed.

Lemma map_restrict_insert_open_bv
    (β : gmap nat value) k x D v :
  k ∈ lvars_bv D →
  <[k:=v]> (map_restrict value β (lvars_bv (lvars_open k x D))) =
  map_restrict value (<[k:=v]> β) (lvars_bv D).
Proof.
  intros Hk.
  rewrite lvars_bv_open.
  rewrite map_restrict_insert_present by exact Hk.
  reflexivity.
Qed.

Definition formula_equiv (φ ψ : FQ) : Prop :=
  (φ ⊫ ψ) ∧ (ψ ⊫ φ).

Notation "φ '⊣⊢' ψ" := (formula_equiv φ ψ)
  (at level 85, no associativity).

Definition formula_store_equiv (φ ψ : FQ) : Prop :=
  ∀ ρ m, res_models_with_store ρ m φ ↔ res_models_with_store ρ m ψ.

Definition formula_store_iso (φ ψ : FQ) : Prop :=
  formula_fv φ = formula_fv ψ ∧ formula_store_equiv φ ψ.

Lemma formula_store_iso_fv φ ψ :
  formula_store_iso φ ψ →
  formula_fv φ = formula_fv ψ.
Proof. intros H. exact (proj1 H). Qed.

Lemma formula_store_iso_equiv φ ψ :
  formula_store_iso φ ψ →
  formula_store_equiv φ ψ.
Proof. intros H. exact (proj2 H). Qed.

Lemma formula_fv_open_ne k y z (φ : FQ) :
  z ≠ y →
  z ∈ formula_fv (formula_open k y φ) ↔ z ∈ formula_fv φ.
Proof.
  induction φ in k |- *; intros Hzy;
    cbn [formula_open formula_fv stale stale_formula stale_logic_qualifier
      lqual_dom];
    try set_solver.
  - destruct a as [D p].
    cbn [lqual_open lqual_dom stale stale_logic_qualifier].
    rewrite lvars_fv_open. destruct decide; set_solver.
  all: try match goal with
  | IH1 : ∀ k0, _ → _ ↔ _,
    IH2 : ∀ k0, _ → _ ↔ _ |- _ =>
      pose proof (IH1 k Hzy); pose proof (IH2 k Hzy); set_solver
  end.
  all: try match goal with
  | IH : ∀ k0, _ → _ ↔ _ |- _ =>
      pose proof (IH k Hzy); pose proof (IH (S k) Hzy); set_solver
  end.
  - rewrite lvars_fv_open. destruct decide;
      match goal with
      | IH : ∀ k0, _ → _ ↔ _ |- _ =>
          pose proof (IH k Hzy); set_solver
      end.
Qed.

Lemma formula_fv_eq_of_open_fresh (S : aset) (φ ψ : FQ) :
  (∀ y, y ∉ S →
    formula_fv (formula_open 0 y φ) =
    formula_fv (formula_open 0 y ψ)) →
  formula_fv φ = formula_fv ψ.
Proof.
  intros Hopen.
  apply set_eq. intros z. split; intros Hz.
  - set (y := fresh_for (S ∪ formula_fv φ ∪ formula_fv ψ ∪ {[z]})).
    assert (Hy : y ∉ S ∪ formula_fv φ ∪ formula_fv ψ ∪ {[z]})
      by (subst y; apply fresh_for_not_in).
    assert (Hzy : z ≠ y) by set_solver.
    specialize (Hopen y ltac:(set_solver)).
    apply (proj1 (formula_fv_open_ne 0 y z ψ Hzy)).
    rewrite <- Hopen.
    apply (proj2 (formula_fv_open_ne 0 y z φ Hzy)).
    exact Hz.
  - set (y := fresh_for (S ∪ formula_fv φ ∪ formula_fv ψ ∪ {[z]})).
    assert (Hy : y ∉ S ∪ formula_fv φ ∪ formula_fv ψ ∪ {[z]})
      by (subst y; apply fresh_for_not_in).
    assert (Hzy : z ≠ y) by set_solver.
    specialize (Hopen y ltac:(set_solver)).
    apply (proj1 (formula_fv_open_ne 0 y z φ Hzy)).
    rewrite Hopen.
    apply (proj2 (formula_fv_open_ne 0 y z ψ Hzy)).
    exact Hz.
Qed.

Lemma formula_equiv_refl φ : φ ⊣⊢ φ.
Proof. unfold formula_equiv, entails. hauto. Qed.

Lemma formula_store_equiv_refl φ : formula_store_equiv φ φ.
Proof. unfold formula_store_equiv. hauto. Qed.

Lemma formula_store_equiv_sym φ ψ :
  formula_store_equiv φ ψ →
  formula_store_equiv ψ φ.
Proof.
  unfold formula_store_equiv. intros H ρ m. symmetry. apply H.
Qed.

Lemma formula_store_equiv_trans φ ψ χ :
  formula_store_equiv φ ψ →
  formula_store_equiv ψ χ →
  formula_store_equiv φ χ.
Proof.
  unfold formula_store_equiv. intros Hφψ Hψχ ρ m.
  split.
  - intros Hφ. apply (proj1 (Hψχ ρ m)). apply (proj1 (Hφψ ρ m)).
    exact Hφ.
  - intros Hχ. apply (proj2 (Hφψ ρ m)). apply (proj2 (Hψχ ρ m)).
    exact Hχ.
Qed.

#[global] Instance formula_store_equiv_equivalence :
  Equivalence formula_store_equiv.
Proof.
  split.
  - intros φ. apply formula_store_equiv_refl.
  - intros φ ψ. apply formula_store_equiv_sym.
  - intros φ ψ χ. apply formula_store_equiv_trans.
Qed.

#[global] Instance denot_equiv_formula : DenotEquiv FQ :=
  formula_store_equiv.

#[global] Instance denot_equiv_formula_equivalence :
  Equivalence (@denot_equiv FQ denot_equiv_formula).
Proof. apply formula_store_equiv_equivalence. Qed.

Lemma FTypeQualifier_open_fv k x φ :
  formula_fv (formula_open k x (FTypeQualifier φ)) =
  formula_fv (FTypeQualifier (qual_open_atom k x φ)).
Proof.
  destruct φ as [D p].
  unfold FTypeQualifier, FStoreResourceAtom.
  cbn [formula_open formula_fv stale stale_logic_qualifier lqual_dom
    qual_dom qual_vars].
  unfold qual_open_atom, qual_bvars.
  destruct (decide (k ∈ lvars_bv D)) as [Hin|Hnot]; cbn [formula_fv
    stale stale_logic_qualifier lqual_dom qual_dom].
  - reflexivity.
  - cbn [stale stale_logic_qualifier lqual_dom].
    change (lvars_fv (lvars_open k x D) = lvars_fv D).
    rewrite lvars_fv_open.
    destruct (decide (k ∈ lvars_bv D)) as [Hin'|_]; [set_solver |].
    set_solver.
Qed.

Lemma FTypeQualifier_open_store_equiv k x φ :
  formula_store_equiv
    (formula_open k x (FTypeQualifier φ))
    (FTypeQualifier (qual_open_atom k x φ)).
Proof.
  destruct φ as [D p].
  unfold formula_store_equiv; intros ρ m.
  unfold FTypeQualifier, FStoreResourceAtom, res_models_with_store.
  cbn [formula_measure res_models_with_store_fuel formula_scoped_in_world
    formula_fv stale stale_logic_qualifier lqual_dom logic_qualifier_denote
    lqual_prop qual_open_atom qual_vars].
  destruct (decide (k ∈ lvars_bv D)) as [Hk|Hk].
  - destruct (decide (k ∈ lvars_bv D)) as [_|Hbad]; [| set_solver].
    split; intros [Hscope Hex]; split; [exact Hscope | | exact Hscope |].
    + destruct Hex as [m0 [Hscope0 [HP Hle]]].
      exists m0. split; [exact Hscope0 |]. split; [| exact Hle].
      destruct HP as [Hdom [σw [Hw Hp]]].
      assert (Hxv :
        ∃ v, store_restrict ρ (lvars_fv (lvars_open k x D)) !! x = Some v).
      {
        eapply bstore_of_env_insert_dom_requires_value; eauto.
      }
      destruct Hxv as [v Hv].
      split.
      * apply (proj1 (bstore_of_env_insert_dom_open ∅
          (store_restrict ρ (lvars_fv (lvars_open k x D))) k x v D Hv)).
        exact Hdom.
      * exists σw. split; [exact Hw |].
        exists v. split; [rewrite store_restrict_twice_same; exact Hv |].
        denot_lvars_norm.
        rewrite (store_restrict_open_open_old k x D ρ).
        rewrite (store_restrict_open_old k x D σw).
        rewrite map_restrict_insert_open_bv by exact Hk.
        rewrite <- (bstore_of_env_insert_restrict_some ∅
          (store_restrict ρ (lvars_fv (lvars_open k x D))) k x v
          (lvars_bv D)) by exact Hv.
        rewrite store_restrict_open_old in Hp.
        exact Hp.
    + destruct Hex as [m0 [Hscope0 [HP Hle]]].
      exists m0. split; [exact Hscope0 |]. split; [| exact Hle].
      destruct HP as [Hdom [σw [Hw [v [Hv Hp]]]]].
      rewrite store_restrict_twice_same in Hp, Hv.
      split.
      * apply (proj2 (bstore_of_env_insert_dom_open ∅
          (store_restrict ρ (lvars_fv (lvars_open k x D))) k x v D Hv)).
        exact Hdom.
      * exists σw. split; [exact Hw |].
        denot_lvars_norm.
        rewrite map_restrict_insert_open_bv in Hp by exact Hk.
        rewrite <- (bstore_of_env_insert_restrict_some ∅
          (store_restrict ρ (lvars_fv (lvars_open k x D))) k x v
          (lvars_bv D)) in Hp by exact Hv.
        rewrite store_restrict_open_old in Hp.
        rewrite store_restrict_open_old.
        rewrite (store_restrict_open_old k x D σw) in Hp.
        exact Hp.
  - destruct (decide (k ∈ lvars_bv D)) as [Hbad|_]; [set_solver |].
    split; intros [Hscope Hex]; split.
    + unfold formula_scoped_in_world in *.
      cbn [formula_open formula_fv stale stale_logic_qualifier lqual_dom
        lqual_open] in *.
      rewrite lvars_fv_open_no_bv in Hscope by exact Hk.
      exact Hscope.
    + destruct Hex as [m0 [Hscope0 [HP Hle]]].
      exists m0. split.
      { unfold formula_scoped_in_world in *.
        cbn [formula_open formula_fv stale stale_logic_qualifier lqual_dom
          lqual_open] in *.
        rewrite lvars_fv_open_no_bv in Hscope0 by exact Hk.
        exact Hscope0. }
      split; [| exact Hle].
      destruct HP as [Hdom [σw [Hw Hp]]].
      denot_lvars_norm.
      rewrite lvars_fv_open_no_bv in Hdom, Hw, Hp by exact Hk.
      split.
      * apply (proj1 (bstore_of_env_insert_dom_absent ∅
          (store_restrict ρ (lvars_fv D)) k x (lvars_bv D) Hk)).
        exact Hdom.
      * exists σw. split; [exact Hw |].
        rewrite <- (bstore_of_env_insert_restrict_absent ∅
          (store_restrict ρ (lvars_fv D)) k x (lvars_bv D)) by exact Hk.
        exact Hp.
    + unfold formula_scoped_in_world in *.
      cbn [formula_open formula_fv stale stale_logic_qualifier lqual_dom
        lqual_open] in *.
      rewrite lvars_fv_open_no_bv by exact Hk.
      exact Hscope.
    + destruct Hex as [m0 [Hscope0 [HP Hle]]].
      exists m0. split.
      { unfold formula_scoped_in_world in *.
        cbn [formula_open formula_fv stale stale_logic_qualifier lqual_dom
          lqual_open] in *.
        rewrite lvars_fv_open_no_bv by exact Hk.
        exact Hscope0. }
      split; [| exact Hle].
      destruct HP as [Hdom [σw [Hw Hp]]].
      denot_lvars_norm.
      split.
      * apply (proj2 (bstore_of_env_insert_dom_absent ∅
          (store_restrict ρ (lvars_fv (lvars_open k x D))) k x
          (lvars_bv D) Hk)).
        exact Hdom.
      * exists σw. split.
        { rewrite lvars_fv_open_no_bv by exact Hk. exact Hw. }
        rewrite lvars_fv_open_no_bv by exact Hk.
        rewrite <- (bstore_of_env_insert_restrict_absent ∅
          (store_restrict ρ (lvars_fv D)) k x
          (lvars_bv D)) in Hp by exact Hk.
        exact Hp.
Qed.

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

Lemma formula_store_equiv_star φ1 φ2 ψ1 ψ2 :
  formula_fv φ1 = formula_fv ψ1 →
  formula_fv φ2 = formula_fv ψ2 →
  formula_store_equiv φ1 ψ1 →
  formula_store_equiv φ2 ψ2 →
  formula_store_equiv (FStar φ1 φ2) (FStar ψ1 ψ2).
Proof.
  intros Hfv1 Hfv2 H1 H2 ρ m.
  unfold res_models_with_store. simpl. split; intros [Hscope Hmodel]; split.
  - unfold formula_scoped_in_world in *. simpl in *.
    rewrite <- Hfv1, <- Hfv2. exact Hscope.
  - destruct Hmodel as [m1 [m2 [Hc [Hle [Hφ1 Hφ2]]]]].
    exists m1, m2, Hc. split; [exact Hle |]. split.
    + pose proof (proj1 (H1 ρ m1) ltac:(models_fuel_irrel Hφ1)) as H.
      models_fuel_irrel H.
    + pose proof (proj1 (H2 ρ m2) ltac:(models_fuel_irrel Hφ2)) as H.
      models_fuel_irrel H.
  - unfold formula_scoped_in_world in *. simpl in *.
    rewrite Hfv1, Hfv2. exact Hscope.
  - destruct Hmodel as [m1 [m2 [Hc [Hle [Hψ1 Hψ2]]]]].
    exists m1, m2, Hc. split; [exact Hle |]. split.
    + pose proof (proj2 (H1 ρ m1) ltac:(models_fuel_irrel Hψ1)) as H.
      models_fuel_irrel H.
    + pose proof (proj2 (H2 ρ m2) ltac:(models_fuel_irrel Hψ2)) as H.
      models_fuel_irrel H.
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

Lemma formula_store_equiv_fibvars D E φ ψ :
  D = E →
  formula_fv φ = formula_fv ψ →
  formula_store_equiv φ ψ →
  formula_store_equiv (FFibVars D φ) (FFibVars E ψ).
Proof.
  intros HDE Hfv Heq ρ m. subst E.
  unfold res_models_with_store. simpl. split; intros [Hscope Hmodel]; split.
  - unfold formula_scoped_in_world in *. simpl in *.
    rewrite <- Hfv. exact Hscope.
  - destruct Hmodel as [Hdisj Hfib]. split; [exact Hdisj |].
    intros σ Hproj.
    specialize (Hfib σ Hproj) as Hφ.
    pose proof (proj1 (Heq (ρ ∪ σ)
      (res_fiber_from_projection m (lvars_fv D) σ Hproj))
      ltac:(models_fuel_irrel Hφ)) as Hψ.
    models_fuel_irrel Hψ.
  - unfold formula_scoped_in_world in *. simpl in *.
    rewrite Hfv. exact Hscope.
  - destruct Hmodel as [Hdisj Hfib]. split; [exact Hdisj |].
    intros σ Hproj.
    specialize (Hfib σ Hproj) as Hψ.
    pose proof (proj2 (Heq (ρ ∪ σ)
      (res_fiber_from_projection m (lvars_fv D) σ Hproj))
      ltac:(models_fuel_irrel Hψ)) as Hφ.
    models_fuel_irrel Hφ.
Qed.

Lemma formula_store_equiv_open_FResultQualifier_over j x φ :
  formula_store_equiv
    (formula_open j x (FFibVars (qual_vars φ) (FOver (FTypeQualifier φ))))
    (FFibVars (qual_vars ({j ~> x} φ))
      (FOver (FTypeQualifier ({j ~> x} φ)))).
Proof.
  rewrite formula_open_fibvars, formula_open_over.
  eapply formula_store_equiv_fibvars.
  - symmetry. apply qual_vars_open_atom.
  - cbn [formula_fv]. apply FTypeQualifier_open_fv.
  - eapply formula_store_equiv_over.
    + apply FTypeQualifier_open_fv.
    + apply FTypeQualifier_open_store_equiv.
Qed.

Lemma formula_fv_open_FResultQualifier_over j x φ :
  formula_fv
    (formula_open j x (FFibVars (qual_vars φ) (FOver (FTypeQualifier φ)))) =
  formula_fv
    (FFibVars (qual_vars ({j ~> x} φ))
      (FOver (FTypeQualifier ({j ~> x} φ)))).
Proof.
  rewrite formula_open_fibvars, formula_open_over.
  cbn [formula_fv].
  rewrite qual_vars_open_atom.
  rewrite FTypeQualifier_open_fv.
  reflexivity.
Qed.

Lemma formula_store_equiv_open_FResultQualifier_under j x φ :
  formula_store_equiv
    (formula_open j x (FFibVars (qual_vars φ) (FUnder (FTypeQualifier φ))))
    (FFibVars (qual_vars ({j ~> x} φ))
      (FUnder (FTypeQualifier ({j ~> x} φ)))).
Proof.
  rewrite formula_open_fibvars, formula_open_under.
  eapply formula_store_equiv_fibvars.
  - symmetry. apply qual_vars_open_atom.
  - cbn [formula_fv]. apply FTypeQualifier_open_fv.
  - eapply formula_store_equiv_under.
    + apply FTypeQualifier_open_fv.
    + apply FTypeQualifier_open_store_equiv.
Qed.

Lemma formula_fv_open_FResultQualifier_under j x φ :
  formula_fv
    (formula_open j x (FFibVars (qual_vars φ) (FUnder (FTypeQualifier φ)))) =
  formula_fv
    (FFibVars (qual_vars ({j ~> x} φ))
      (FUnder (FTypeQualifier ({j ~> x} φ)))).
Proof.
  rewrite formula_open_fibvars, formula_open_under.
  cbn [formula_fv].
  rewrite qual_vars_open_atom.
  rewrite FTypeQualifier_open_fv.
  reflexivity.
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

Lemma formula_store_equiv_forall_fresh (S : aset) φ ψ :
  formula_fv φ = formula_fv ψ →
  (∀ y, y ∉ S →
    formula_store_equiv (formula_open 0 y φ) (formula_open 0 y ψ)) →
  formula_store_equiv (FForall φ) (FForall ψ).
Proof.
  intros Hfv Hopen ρ m.
  unfold res_models_with_store. simpl. split; intros [Hscope Hmodel]; split.
  - unfold formula_scoped_in_world in *. simpl in *.
    rewrite <- Hfv. exact Hscope.
  - destruct Hmodel as [L [HL Hbody]].
    exists (L ∪ S). split; [set_solver |].
    intros y Hy my Hdom Hrestrict.
    assert (HyL : y ∉ L) by set_solver.
    assert (HyS : y ∉ S) by set_solver.
    specialize (Hbody y HyL my Hdom Hrestrict).
    pose proof (proj1 (Hopen y HyS ρ my)
      ltac:(models_fuel_irrel Hbody)) as Hψ.
    models_fuel_irrel Hψ.
  - unfold formula_scoped_in_world in *. simpl in *.
    rewrite Hfv. exact Hscope.
  - destruct Hmodel as [L [HL Hbody]].
    exists (L ∪ S). split; [set_solver |].
    intros y Hy my Hdom Hrestrict.
    assert (HyL : y ∉ L) by set_solver.
    assert (HyS : y ∉ S) by set_solver.
    specialize (Hbody y HyL my Hdom Hrestrict).
    pose proof (proj2 (Hopen y HyS ρ my)
      ltac:(models_fuel_irrel Hbody)) as Hφ.
    models_fuel_irrel Hφ.
Qed.

Lemma res_models_of_formula_store_equiv φ ψ (m : WfWorld) :
  formula_store_equiv φ ψ →
  m ⊨ φ ↔ m ⊨ ψ.
Proof. intros Heq. unfold res_models. apply Heq. Qed.
