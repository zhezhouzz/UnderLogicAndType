(** * ContextBase.LogicVarAtoms

    Shifts, atom projections, and atom swaps for logic-variable sets. *)

From ContextBase Require Export LogicVarOpen.

Definition logic_var_shift (v : logic_var) : logic_var :=
  match v with
  | LVBound k => LVBound (S k)
  | LVFree x => LVFree x
  end.

Definition logic_var_shift_by (k : nat) (v : logic_var) : logic_var :=
  match v with
  | LVBound n => LVBound (k + n)
  | LVFree x => LVFree x
  end.

Lemma logic_var_shift_by_inj k : Inj (=) (=) (logic_var_shift_by k).
Proof.
  intros [i|x] [j|y] Hij; cbn [logic_var_shift_by] in Hij;
    inversion Hij; subst; try reflexivity; f_equal; lia.
Qed.

#[global] Instance logic_var_shift_key : ShiftKey logic_var := {
  key_shift := logic_var_shift_by;
  key_shift_inj := logic_var_shift_by_inj
}.

Definition lvars_shift (D : lvset) : lvset :=
  set_map logic_var_shift D.

Definition lvars_shift_by (k : nat) (D : lvset) : lvset :=
  set_map (logic_var_shift_by k) D.

Definition lc_logic_var_key (v : logic_var) : Prop :=
  match v with
  | LVBound _ => False
  | LVFree _ => True
  end.

Definition lc_lvars (D : lvset) : Prop :=
  ∀ v, v ∈ D → lc_logic_var_key v.

Lemma lc_lvars_no_bv D :
  lc_lvars D ↔ lvars_bv D = ∅.
Proof.
  split.
  - intros Hlc. apply set_eq. intros k.
    rewrite elem_of_empty, lvars_bv_elem.
    split; [|tauto].
    intros Hin. specialize (Hlc (LVBound k) Hin). exact Hlc.
  - intros Hbv [k|x] Hin; cbn [lc_logic_var_key]; [|exact I].
    assert (k ∈ lvars_bv D) by (rewrite lvars_bv_elem; exact Hin).
    rewrite Hbv in H. better_set_solver.
Qed.

Definition logic_var_to_atom (η : gmap nat atom) (v : logic_var) : option atom :=
  match v with
  | LVBound k => η !! k
  | LVFree x => Some x
  end.

Definition logic_var_swap (x y : atom) : logic_var → logic_var :=
  swap (LVFree x) (LVFree y).

Definition lvars_swap (x y : atom) (D : lvset) : lvset :=
  set_swap (LVFree x) (LVFree y) D.

Lemma logic_var_swap_unfold x y v :
  logic_var_swap x y v = swap (LVFree x) (LVFree y) v.
Proof. reflexivity. Qed.

Lemma lvars_swap_unfold x y D :
  lvars_swap x y D = set_swap (LVFree x) (LVFree y) D.
Proof. reflexivity. Qed.

Lemma logic_var_swap_sym x y v :
  logic_var_swap x y v = logic_var_swap y x v.
Proof.
  unfold logic_var_swap. apply swap_sym.
Qed.

Lemma lvars_swap_sym x y D :
  lvars_swap x y D = lvars_swap y x D.
Proof.
  unfold lvars_swap. apply set_swap_sym.
Qed.

Lemma logic_var_free_swap x y z :
  swap (LVFree x) (LVFree y) (LVFree z) = LVFree (swap x y z).
Proof.
  unfold swap. repeat destruct decide; congruence.
Qed.

Lemma lvars_fv_swap x y (D : lvset) :
  lvars_fv (lvars_swap x y D) = set_swap x y (lvars_fv D).
Proof.
  apply set_eq. intros z.
  rewrite lvars_fv_elem, elem_of_set_swap, lvars_fv_elem.
  change (LVFree z ∈ set_swap (LVFree x) (LVFree y) D ↔
    LVFree (swap x y z) ∈ D).
  rewrite set_swap_elem, logic_var_free_swap.
  reflexivity.
Qed.

Definition lvars_of_atoms (X : aset) : lvset :=
  set_map LVFree X.

Definition lvars_of_bvars (B : gset nat) : lvset :=
  set_map LVBound B.
