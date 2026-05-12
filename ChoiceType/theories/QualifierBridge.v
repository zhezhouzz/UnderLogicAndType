(** * ChoiceType.QualifierBridge

    Bridges from type-level shallow qualifiers to Choice Logic atoms.

    The raw [type_qualifier] syntax and its local operations live in
    [Qualifier].  This file contains the denotational lift that depends on the
    Choice Logic world structure. *)

From ChoiceType Require Export Qualifier.
From ChoiceType Require Import QualifierProps.
From Stdlib Require Import Logic.PropExtensionality.

(** Lift a type-level store predicate into a logic atom.

    Logic denotation restricts the world to the qualifier domain before this
    predicate is called, so the singleton requirement applies to the relevant
    world fragment. *)
Definition lift_type_qualifier_to_logic (q : type_qualifier) : logic_qualifier :=
  match q with
  | qual B d p =>
      lqual d (fun σ (w : WfWorld) =>
        B = ∅ ∧ ∃ σw, (w : World) = singleton_world σw ∧ p ∅ σ σw)
  end.

(** Formula-level lift of a type qualifier.

    This is definitionally the same singleton-world lift as
    [FAtom (lift_type_qualifier_to_logic q)], but it exposes the intended
    shape directly as a store/resource atom.  Keeping the [match] here lets
    formula proofs reuse the generic atom lemmas for [FStoreResourceAtom]. *)
Definition FTypeQualifier (q : type_qualifier) : Formula :=
  match q with
  | qual B d p =>
      FStoreResourceAtom d (fun σ (w : WfWorld) =>
        B = ∅ ∧ ∃ σw, (w : World) = singleton_world σw ∧ p ∅ σ σw)
  end.

Lemma FTypeQualifier_unfold q :
  FTypeQualifier q = FAtom (lift_type_qualifier_to_logic q).
Proof. destruct q; reflexivity. Qed.

Lemma formula_fv_FTypeQualifier q :
  formula_fv (FTypeQualifier q) = qual_dom q.
Proof. destruct q; reflexivity. Qed.

Lemma lqual_dom_lift_type_qualifier_to_logic q :
  lqual_dom (lift_type_qualifier_to_logic q) = qual_dom q.
Proof. destruct q; reflexivity. Qed.

Lemma logic_qualifier_denote_lift_swap x y q σ w :
  logic_qualifier_denote
    (lqual_swap x y (lift_type_qualifier_to_logic q)) σ w ↔
  logic_qualifier_denote
    (lift_type_qualifier_to_logic (qual_swap_atom x y q)) σ w.
Proof.
  destruct q as [B d p]. simpl.
  split.
  - intros [HB [σw [Hw Hp]]]. split; [exact HB |].
    exists (store_swap x y σw). split.
    + assert (Hwf : res_swap x y (res_restrict w (aset_swap x y d)) =
          exist _ (singleton_world σw) (wf_singleton_world σw)).
      { apply wfworld_ext. exact Hw. }
      apply (f_equal (res_swap x y)) in Hwf.
      rewrite res_swap_involutive in Hwf.
      rewrite res_swap_singleton_wfworld in Hwf.
      exact (f_equal raw_world Hwf).
    + rewrite store_swap_involutive. exact Hp.
  - intros [HB [σw [Hw Hp]]]. split; [exact HB |].
    exists (store_swap x y σw). split.
    + assert (Hwf : res_restrict w (aset_swap x y d) =
          exist _ (singleton_world σw) (wf_singleton_world σw)).
      { apply wfworld_ext. exact Hw. }
      apply (f_equal (res_swap x y)) in Hwf.
      rewrite res_swap_singleton_wfworld in Hwf.
      exact (f_equal raw_world Hwf).
    + exact Hp.
Qed.

Lemma logic_qualifier_denote_lift_open_swap_fresh k x y q σ w :
  k ∈ qual_bvars q →
  x ∉ qual_dom q →
  y ∉ qual_dom q →
  logic_qualifier_denote
    (lqual_swap x y (lift_type_qualifier_to_logic (qual_open_atom k x q))) σ w ↔
  logic_qualifier_denote
    (lift_type_qualifier_to_logic (qual_open_atom k y q)) σ w.
Proof.
  intros Hk Hx Hy.
  rewrite logic_qualifier_denote_lift_swap.
  rewrite (qual_open_atom_swap_fresh k x y q Hk Hx Hy).
  reflexivity.
Qed.

Lemma res_models_with_store_lift_open_rename_fresh k x y q ρ m :
  k ∈ qual_bvars q →
  x ∉ qual_dom q →
  y ∉ qual_dom q →
  res_models_with_store ρ m (formula_rename_atom x y
    (FAtom (lift_type_qualifier_to_logic (qual_open_atom k x q)))) ↔
  res_models_with_store ρ m
    (FAtom (lift_type_qualifier_to_logic (qual_open_atom k y q))).
Proof.
  intros Hk Hx Hy.
  destruct q as [B d p]. simpl in *.
  unfold res_models_with_store.
  simpl. split; intros [Hscope Hmodel]; split.
  - unfold formula_scoped_in_world in *. simpl in *.
    unfold stale, stale_logic_qualifier in *.
    unfold lqual_dom in Hscope.
    unfold lift_type_qualifier_to_logic in Hscope.
    cbn in Hscope.
    rewrite !decide_True in Hscope by exact Hk.
    assert (Hsets : aset_swap x y ({[x]} ∪ d) = {[y]} ∪ d).
    { rewrite aset_swap_union, aset_swap_singleton.
      replace (atom_swap x y x) with y
        by (unfold atom_swap; repeat destruct decide; congruence).
      rewrite aset_swap_fresh by assumption. reflexivity. }
    intros z Hz.
    unfold lqual_dom in Hz. cbn in Hz.
    rewrite decide_True in Hz by exact Hk.
    apply Hscope.
    unfold lqual_dom. cbn.
    rewrite Hsets. exact Hz.
  - destruct Hmodel as [m0 [Hscope0 [Hq Hle]]].
    exists m0. split.
    + unfold formula_scoped_in_world in *. simpl in *.
      unfold stale, stale_logic_qualifier in *.
      unfold lqual_dom in *.
      unfold lift_type_qualifier_to_logic in *.
      cbn in *.
      rewrite decide_True by exact Hk.
      rewrite decide_True in Hscope0 by exact Hk.
      assert (Hsets : aset_swap x y ({[x]} ∪ d) = {[y]} ∪ d).
      { rewrite aset_swap_union, aset_swap_singleton.
        replace (atom_swap x y x) with y
          by (unfold atom_swap; repeat destruct decide; congruence).
        rewrite aset_swap_fresh by assumption. reflexivity. }
      intros z Hz. apply Hscope0.
      unfold lqual_swap, lift_type_qualifier_to_logic. cbn.
      rewrite Hsets. change (z ∈ dom ρ ∪ ({[y]} ∪ d)). exact Hz.
    + split; [| exact Hle].
    apply (proj1 (logic_qualifier_denote_lift_open_swap_fresh
      k x y (qual B d p) ρ m0 Hk Hx Hy)).
    exact Hq.
  - unfold formula_scoped_in_world in *. simpl in *.
    unfold stale, stale_logic_qualifier in *.
    unfold lqual_dom in Hscope.
    unfold lift_type_qualifier_to_logic in Hscope.
    cbn in Hscope.
    rewrite !decide_True in Hscope by exact Hk.
    assert (Hsets : aset_swap x y ({[x]} ∪ d) = {[y]} ∪ d).
    { rewrite aset_swap_union, aset_swap_singleton.
      replace (atom_swap x y x) with y
        by (unfold atom_swap; repeat destruct decide; congruence).
      rewrite aset_swap_fresh by assumption. reflexivity. }
    intros z Hz.
    unfold lqual_dom, lqual_swap, lift_type_qualifier_to_logic in Hz. cbn in Hz.
    rewrite decide_True in Hz by exact Hk.
    apply Hscope.
    rewrite Hsets in Hz. exact Hz.
  - destruct Hmodel as [m0 [Hscope0 [Hq Hle]]].
    exists m0. split.
    + unfold formula_scoped_in_world in *. simpl in *.
      unfold stale, stale_logic_qualifier in *.
      unfold lqual_dom in *.
      unfold lift_type_qualifier_to_logic in *.
      cbn in *.
      rewrite decide_True by exact Hk.
      rewrite decide_True in Hscope0 by exact Hk.
      assert (Hsets : aset_swap x y ({[x]} ∪ d) = {[y]} ∪ d).
      { rewrite aset_swap_union, aset_swap_singleton.
        replace (atom_swap x y x) with y
          by (unfold atom_swap; repeat destruct decide; congruence).
        rewrite aset_swap_fresh by assumption. reflexivity. }
      intros z Hz. apply Hscope0.
      unfold lqual_swap, lift_type_qualifier_to_logic in Hz. cbn in Hz.
      rewrite Hsets in Hz.
      change (z ∈ dom ρ ∪ ({[y]} ∪ d)). exact Hz.
    + split; [| exact Hle].
    apply (proj2 (logic_qualifier_denote_lift_open_swap_fresh
      k x y (qual B d p) ρ m0 Hk Hx Hy)).
    exact Hq.
Qed.

Lemma res_models_lift_open_rename_fresh k x y q m :
  k ∈ qual_bvars q →
  x ∉ qual_dom q →
  y ∉ qual_dom q →
  res_models m (formula_rename_atom x y
    (FAtom (lift_type_qualifier_to_logic (qual_open_atom k x q)))) ↔
  res_models m (FAtom (lift_type_qualifier_to_logic (qual_open_atom k y q))).
Proof.
  apply res_models_with_store_lift_open_rename_fresh.
Qed.

Lemma res_models_with_store_FTypeQualifier_open_rename_fresh k x y q ρ m :
  k ∈ qual_bvars q →
  x ∉ qual_dom q →
  y ∉ qual_dom q →
  res_models_with_store ρ m (formula_rename_atom x y
    (FTypeQualifier (qual_open_atom k x q))) ↔
  res_models_with_store ρ m (FTypeQualifier (qual_open_atom k y q)).
Proof.
  intros Hk Hx Hy.
  rewrite !FTypeQualifier_unfold.
  apply res_models_with_store_lift_open_rename_fresh; assumption.
Qed.

Lemma res_models_FTypeQualifier_open_rename_fresh k x y q m :
  k ∈ qual_bvars q →
  x ∉ qual_dom q →
  y ∉ qual_dom q →
  res_models m (formula_rename_atom x y
    (FTypeQualifier (qual_open_atom k x q))) ↔
  res_models m (FTypeQualifier (qual_open_atom k y q)).
Proof.
  apply res_models_with_store_FTypeQualifier_open_rename_fresh.
Qed.
