(** * ContextBase.LogicVarInterface

    Public helper lemmas for logic-variable sets. *)

From ContextBase Require Export LogicVarOpenEnv.

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
  split; [intros [a [Hbad _]]; discriminate | better_set_solver].
Qed.

Lemma lvars_bv_empty_subset_of_atoms_fv (D : lvset) :
  lvars_bv D = ∅ ->
  D ⊆ lvars_of_atoms (lvars_fv D).
Proof.
  intros Hbv v Hv.
  destruct v as [k|x].
  - exfalso.
    assert (k ∈ lvars_bv D) by (apply lvars_bv_elem; exact Hv).
    rewrite Hbv in H. better_set_solver.
  - unfold lvars_of_atoms. apply elem_of_map.
    exists x. split; [reflexivity|].
    apply lvars_fv_elem. exact Hv.
Qed.

Lemma lvars_fv_singleton_bound k :
  lvars_fv ({[LVBound k]} : lvset) = ∅.
Proof.
  apply set_eq. intros x.
  rewrite lvars_fv_elem.
  better_set_solver.
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
  change (LVFree y ∈ set_swap (LVBound k) (LVFree x) D ↔
    y ∈ (lvars_fv D ∖ {[x]}) ∪
      (if decide (k ∈ lvars_bv D) then {[x]} else ∅)).
  rewrite set_swap_elem.
  destruct (decide (y = x)) as [->|Hyx].
  - rewrite swap_r.
    destruct (decide (k ∈ lvars_bv D)) as [Hk|Hk].
    + rewrite elem_of_union, elem_of_difference, elem_of_singleton.
      rewrite lvars_bv_elem in Hk. tauto.
    + rewrite elem_of_union, elem_of_difference, elem_of_singleton.
      rewrite elem_of_empty. rewrite lvars_bv_elem in Hk. tauto.
  - rewrite swap_fresh by congruence.
    destruct (decide (k ∈ lvars_bv D)); rewrite elem_of_union,
      elem_of_difference, !elem_of_singleton, ?elem_of_empty, lvars_fv_elem;
      tauto.
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

Lemma lvars_fv_difference_singleton_free (D : lvset) x :
  lvars_fv (D ∖ {[LVFree x]}) = lvars_fv D ∖ {[x]}.
Proof.
  apply set_eq. intros y.
  rewrite !lvars_fv_elem, !elem_of_difference, !elem_of_singleton.
  split.
  - intros [HyD Hyx]. split; [apply lvars_fv_elem; exact HyD|].
    intros ->. apply Hyx. reflexivity.
  - intros [HyD Hyx]. split; [apply lvars_fv_elem in HyD; exact HyD|].
    intros Heq. inversion Heq. subst. contradiction.
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

Lemma lvars_bv_swap x y (D : lvset) :
  lvars_bv (lvars_swap x y D) = lvars_bv D.
Proof.
  apply set_eq. intros k.
  rewrite !lvars_bv_elem.
  change (LVBound k ∈ set_swap (LVFree x) (LVFree y) D ↔ LVBound k ∈ D).
  rewrite set_swap_elem.
  rewrite swap_fresh by congruence.
  reflexivity.
Qed.

Lemma logic_var_swap_involutive x y v :
  logic_var_swap x y (logic_var_swap x y v) = v.
Proof.
  unfold logic_var_swap. apply swap_involutive.
Qed.

Lemma lvars_fv_open_subset k x (D : lvset) :
  lvars_fv (lvars_open k x D) ⊆ lvars_fv D ∪ {[x]}.
Proof.
  intros y Hy.
  rewrite lvars_fv_open in Hy.
  destruct (decide (k ∈ lvars_bv D)); better_set_solver.
Qed.

#[global] Instance stale_logic_var : Stale logic_var := logic_var_fv.
Arguments stale_logic_var /.

#[global] Instance stale_logic_vars : Stale lvset := lvars_fv.
Arguments stale_logic_vars /.
