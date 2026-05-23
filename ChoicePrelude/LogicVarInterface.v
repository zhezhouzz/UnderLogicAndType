(** * ChoicePrelude.LogicVarInterface

    Public helper lemmas for logic-variable sets. *)

From ChoicePrelude Require Export LogicVarOpenEnv.

Class IntoLVars A := into_lvars : A → lvset.

#[global] Instance into_lvars_aset : IntoLVars aset := lvars_of_atoms.
#[global] Instance into_lvars_lvset : IntoLVars lvset := id.

Lemma lvars_fv_of_atoms (X : aset) :
  lvars_fv (lvars_of_atoms X) = X.
Proof.
  apply set_eq. intros x.
  rewrite lvars_fv_elem.
  unfold lvars_of_atoms.
  rewrite elem_of_map.
  split.
  - intros [a [Heq Ha]]. inversion Heq. subst. exact Ha.
  - intros Hx. exists x. split; [reflexivity | exact Hx].
Qed.

Lemma lvars_bv_of_atoms (X : aset) :
  lvars_bv (lvars_of_atoms X) = ∅.
Proof.
  apply set_eq. intros k.
  rewrite lvars_bv_elem.
  unfold lvars_of_atoms.
  rewrite elem_of_empty, elem_of_map.
  split; [intros [a [Hbad _]]; discriminate | set_solver].
Qed.

Lemma lvars_bv_empty_subset_of_atoms_fv (D : lvset) :
  lvars_bv D = ∅ ->
  D ⊆ lvars_of_atoms (lvars_fv D).
Proof.
  intros Hbv v Hv.
  destruct v as [k|x].
  - exfalso.
    assert (k ∈ lvars_bv D) by (apply lvars_bv_elem; exact Hv).
    rewrite Hbv in H. set_solver.
  - unfold lvars_of_atoms. apply elem_of_map.
    exists x. split; [reflexivity|].
    apply lvars_fv_elem. exact Hv.
Qed.

Lemma lvars_open_of_atoms k x (X : aset) :
  x ∉ X →
  lvars_open k x (lvars_of_atoms X) = lvars_of_atoms X.
Proof.
  intros Hfresh.
  unfold lvars_open.
  apply gset_swap_fresh.
  - unfold lvars_of_atoms. intros Hin.
    apply elem_of_map in Hin as [a [Hbad _]]. discriminate.
  - unfold lvars_of_atoms. intros Hin.
    apply elem_of_map in Hin as [a [Heq Ha]].
    inversion Heq. subst. contradiction.
Qed.

Lemma lvars_fv_of_bvars (B : gset nat) :
  lvars_fv (lvars_of_bvars B) = ∅.
Proof.
  apply set_eq. intros x.
  rewrite lvars_fv_elem.
  unfold lvars_of_bvars.
  rewrite elem_of_empty, elem_of_map.
  split; [intros [k [Hbad _]]; discriminate | set_solver].
Qed.

Lemma lvars_fv_singleton_bound k :
  lvars_fv ({[LVBound k]} : lvset) = ∅.
Proof.
  apply set_eq. intros x.
  rewrite lvars_fv_elem.
  set_solver.
Qed.

Lemma lvars_fv_singleton_free x :
  lvars_fv ({[LVFree x]} : lvset) = {[x]}.
Proof.
  rewrite <- (lvars_fv_of_atoms ({[x]} : aset)).
  unfold lvars_of_atoms.
  rewrite set_map_singleton_L.
  reflexivity.
Qed.

Lemma lvars_fv_open k x (D : lvset) :
  lvars_fv (lvars_open k x D) =
  (lvars_fv D ∖ {[x]}) ∪
  (if decide (k ∈ lvars_bv D) then {[x]} else ∅).
Proof.
  apply set_eq. intros y.
  rewrite lvars_fv_elem.
  change (LVFree y ∈ gset_swap (LVBound k) (LVFree x) D ↔
    y ∈ (lvars_fv D ∖ {[x]}) ∪
      (if decide (k ∈ lvars_bv D) then {[x]} else ∅)).
  rewrite gset_swap_elem.
  destruct (decide (y = x)) as [->|Hyx].
  - rewrite eq_swap_r.
    destruct (decide (k ∈ lvars_bv D)) as [Hk|Hk].
    + rewrite elem_of_union, elem_of_difference, elem_of_singleton.
      rewrite lvars_bv_elem in Hk. tauto.
    + rewrite elem_of_union, elem_of_difference, elem_of_singleton.
      rewrite elem_of_empty. rewrite lvars_bv_elem in Hk. tauto.
  - rewrite eq_swap_fresh by congruence.
    destruct (decide (k ∈ lvars_bv D)); rewrite elem_of_union,
      elem_of_difference, !elem_of_singleton, ?elem_of_empty, lvars_fv_elem;
      tauto.
Qed.

Lemma lvars_bv_contains_bound_singleton k (D : lvset) :
  k ∈ lvars_bv (D ∪ {[LVBound k]}).
Proof.
  apply lvars_bv_elem. set_solver.
Qed.

Lemma lvars_fv_union (D1 D2 : lvset) :
  lvars_fv (D1 ∪ D2) = lvars_fv D1 ∪ lvars_fv D2.
Proof.
  apply set_eq. intros x.
  rewrite elem_of_union.
  rewrite !lvars_fv_elem.
  rewrite elem_of_union.
  tauto.
Qed.

Lemma lvars_bv_union (D1 D2 : lvset) :
  lvars_bv (D1 ∪ D2) = lvars_bv D1 ∪ lvars_bv D2.
Proof.
  apply set_eq. intros k.
  rewrite elem_of_union.
  rewrite !lvars_bv_elem.
  rewrite elem_of_union.
  tauto.
Qed.

Lemma logic_var_shift_inj : Inj (=) (=) logic_var_shift.
Proof.
  intros v1 v2 Heq.
  destruct v1 as [k1|x1], v2 as [k2|x2]; cbn in Heq; congruence.
Qed.

Lemma lvars_fv_shift D :
  lvars_fv (lvars_shift D) = lvars_fv D.
Proof.
  induction D as [|v D Hfresh IH] using set_ind_L.
  - unfold lvars_shift. rewrite set_map_empty. reflexivity.
  - unfold lvars_shift in *.
    rewrite set_map_union_L, set_map_singleton_L.
    rewrite !lvars_fv_union, IH.
    destruct v as [k|x]; cbn [logic_var_shift];
      rewrite ?lvars_fv_singleton_bound, ?lvars_fv_singleton_free;
      reflexivity.
Qed.

Lemma lvars_fv_open_atoms_with_bound k x (X : aset) :
  x ∉ X →
  lvars_fv (lvars_open k x (lvars_of_atoms X ∪ {[LVBound k]})) =
  X ∪ {[x]}.
Proof.
  intros Hfresh.
  rewrite lvars_fv_open.
  rewrite lvars_fv_union, lvars_fv_of_atoms, lvars_fv_singleton_bound.
  destruct (decide (k ∈ lvars_bv (lvars_of_atoms X ∪ {[LVBound k]}))) as [_|Hbad].
  - set_solver.
  - exfalso. apply Hbad. apply lvars_bv_contains_bound_singleton.
Qed.

Lemma logic_var_bv_swap x y v :
  logic_var_bv (logic_var_swap x y v) = logic_var_bv v.
Proof.
  destruct v; unfold logic_var_swap, swap, swap_action_self, eq_swap; simpl;
    repeat destruct decide; try congruence; reflexivity.
Qed.

Lemma lvars_bv_swap x y (D : lvset) :
  lvars_bv (lvars_swap x y D) = lvars_bv D.
Proof.
  apply set_eq. intros k.
  rewrite !lvars_bv_elem.
  change (LVBound k ∈ gset_swap (LVFree x) (LVFree y) D ↔ LVBound k ∈ D).
  rewrite gset_swap_elem.
  rewrite eq_swap_fresh by congruence.
  reflexivity.
Qed.

Lemma logic_var_swap_involutive x y v :
  logic_var_swap x y (logic_var_swap x y v) = v.
Proof.
  unfold logic_var_swap. apply swap_involutive.
Qed.

Lemma lvars_swap_involutive x y (D : lvset) :
  lvars_swap x y (lvars_swap x y D) = D.
Proof.
  unfold lvars_swap. apply swap_involutive.
Qed.

Lemma lvars_fv_open_subset k x (D : lvset) :
  lvars_fv (lvars_open k x D) ⊆ lvars_fv D ∪ {[x]}.
Proof.
  intros y Hy.
  rewrite lvars_fv_open in Hy.
  destruct (decide (k ∈ lvars_bv D)); set_solver.
Qed.

#[global] Instance stale_logic_var : Stale logic_var := logic_var_fv.
Arguments stale_logic_var /.

#[global] Instance stale_logic_vars : Stale lvset := lvars_fv.
Arguments stale_logic_vars /.
