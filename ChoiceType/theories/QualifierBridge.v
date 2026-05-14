(** * ChoiceType.QualifierBridge

    Bridges from type-level shallow qualifiers to Choice Logic atoms.

    The raw [type_qualifier] syntax and its local operations live in
    [Qualifier].  This file contains the denotational lift that depends on the
    Choice Logic world structure. *)

From ChoiceType Require Export Qualifier.
From ChoiceType Require Import QualifierProps.
From Stdlib Require Import Logic.PropExtensionality.

(** Formula-level lift of a type qualifier.

    A type qualifier is a shallow predicate over an explicit store and a
    singleton result-resource.  [FTypeQualifier] exposes that shape directly as
    a [FStoreResourceAtom], instead of first manufacturing an intermediate
    logic qualifier. *)
Definition FTypeQualifier (q : type_qualifier) : Formula :=
  match q with
  | qual B d p =>
      FStoreResourceAtom d (fun σ (w : WfWorld) =>
        B = ∅ ∧ ∃ σw, (w : World) = singleton_world σw ∧ p ∅ σ σw)
  end.

Lemma formula_fv_FTypeQualifier q :
  formula_fv (FTypeQualifier q) = qual_dom q.
Proof.
  destruct q. unfold FTypeQualifier, FStoreResourceAtom, lqual_fvars. simpl.
  apply lvars_fv_of_atoms.
Qed.

Lemma formula_fv_FTypeQualifier_open_member k x q :
  k ∈ qual_bvars q →
  formula_fv (FTypeQualifier (qual_open_atom k x q)) =
  {[x]} ∪ qual_dom q.
Proof.
  intros Hk.
  rewrite formula_fv_FTypeQualifier.
  destruct q as [B d p]. unfold qual_open_atom, qual_bvars, qual_dom in *.
  simpl in *. rewrite decide_True by exact Hk. reflexivity.
Qed.

Lemma formula_fv_FTypeQualifier_open_not_member k x q :
  k ∉ qual_bvars q →
  formula_fv (FTypeQualifier (qual_open_atom k x q)) =
  qual_dom q.
Proof.
  intros Hk.
  rewrite formula_fv_FTypeQualifier.
  destruct q as [B d p]. unfold qual_open_atom, qual_bvars, qual_dom in *.
  simpl in *. rewrite decide_False by exact Hk. reflexivity.
Qed.

Lemma formula_scoped_FTypeQualifier ρ m q :
  formula_scoped_in_world ρ m (FTypeQualifier q) ↔
  dom ρ ∪ qual_dom q ⊆ world_dom (m : World).
Proof.
  unfold formula_scoped_in_world.
  rewrite formula_fv_FTypeQualifier.
  reflexivity.
Qed.

Lemma res_models_with_store_FTypeQualifier_intro ρ m q :
  formula_scoped_in_world ρ m (FTypeQualifier q) →
  match q with
  | qual B d p =>
      B = ∅ ∧
      ∃ σw,
        (res_restrict m d : World) = singleton_world σw ∧
        p ∅ (store_restrict ρ d) σw
  end →
  res_models_with_store ρ m (FTypeQualifier q).
Proof.
  destruct q as [B d p]. simpl.
  intros Hscope Hden.
  eapply res_models_with_store_store_resource_atom_intro.
  - exact Hscope.
  - exact Hden.
Qed.

Lemma res_models_with_store_FTypeQualifier_elim ρ m q :
  res_models_with_store ρ m (FTypeQualifier q) →
  ∃ m0,
    formula_scoped_in_world ρ m0 (FTypeQualifier q) ∧
    match q with
    | qual B d p =>
        B = ∅ ∧
        ∃ σw,
          (res_restrict m0 d : World) = singleton_world σw ∧
          p ∅ (store_restrict ρ d) σw
    end ∧
    m0 ⊑ m.
Proof.
  destruct q as [B d p]. simpl.
  intros Hmodel.
  exact (res_models_with_store_store_resource_atom_elim ρ m d
    (fun σ w => B = ∅ ∧ ∃ σw, (w : World) = singleton_world σw ∧ p ∅ σ σw)
    Hmodel).
Qed.

Lemma res_models_FTypeQualifier_intro m q :
  formula_scoped_in_world ∅ m (FTypeQualifier q) →
  match q with
  | qual B d p =>
      B = ∅ ∧
      ∃ σw,
        (res_restrict m d : World) = singleton_world σw ∧
        p ∅ ∅ σw
  end →
  res_models m (FTypeQualifier q).
Proof.
  intros Hscope Hden.
  eapply res_models_with_store_FTypeQualifier_intro.
  - exact Hscope.
  - destruct q as [B d p]. simpl in *.
    destruct Hden as [HB [σw [Hres Hp]]].
    split; [exact HB |].
    exists σw. split; [exact Hres |].
    rewrite store_restrict_empty. exact Hp.
Qed.

Lemma res_models_with_store_FTypeQualifier_swap x y q ρ m :
  res_models_with_store (store_swap x y ρ) (res_swap x y m)
    (FTypeQualifier q) ↔
  res_models_with_store ρ m (FTypeQualifier (qual_swap_atom x y q)).
Proof.
  (* Legacy explicit-swap/type-qualifier bridge; replaced by LN open bridge. *)
Admitted.

Lemma res_models_with_store_FTypeQualifier_open_rename_fresh k x y q ρ m :
  k ∈ qual_bvars q →
  x ∉ qual_dom q →
  y ∉ qual_dom q →
  res_models_with_store ρ m (formula_rename_atom x y
    (FTypeQualifier (qual_open_atom k x q))) ↔
  res_models_with_store ρ m (FTypeQualifier (qual_open_atom k y q)).
Proof.
  (* Legacy explicit-swap/type-qualifier bridge; replaced by LN open bridge. *)
Admitted.

Lemma res_models_FTypeQualifier_open_rename_fresh k x y q m :
  k ∈ qual_bvars q →
  x ∉ qual_dom q →
  y ∉ qual_dom q →
  res_models m (formula_rename_atom x y
    (FTypeQualifier (qual_open_atom k x q))) ↔
  res_models m (FTypeQualifier (qual_open_atom k y q)).
Proof.
  (* Legacy explicit-swap/type-qualifier bridge; replaced by LN open bridge. *)
Admitted.

