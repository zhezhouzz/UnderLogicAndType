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
    rewrite Hbv in H. set_solver.
Qed.

Definition logic_var_to_atom (η : gmap nat atom) (v : logic_var) : option atom :=
  match v with
  | LVBound k => η !! k
  | LVFree x => Some x
  end.

Definition lvars_to_atoms (η : gmap nat atom) (D : lvset) : aset :=
  set_fold
    (λ v acc,
      match logic_var_to_atom η v with
      | Some x => {[x]} ∪ acc
      | None => acc
      end) ∅ D.

Lemma lvars_to_atoms_elem η D x :
  x ∈ lvars_to_atoms η D ↔
  ∃ v, v ∈ D ∧ logic_var_to_atom η v = Some x.
Proof.
  unfold lvars_to_atoms.
  refine (set_fold_ind_L
    (fun acc D => ∀ x, x ∈ acc ↔
      ∃ v, v ∈ D ∧ logic_var_to_atom η v = Some x)
    (λ v acc,
      match logic_var_to_atom η v with
      | Some x => {[x]} ∪ acc
      | None => acc
      end) ∅ _ _ D x).
  - intros y. set_solver.
  - intros v D' acc Hfresh IH z.
    destruct (logic_var_to_atom η v) as [a|] eqn:Hv.
    + pose proof (IH z) as Hz. split.
      * intros Hz'. apply elem_of_union in Hz' as [Hz'|Hz'].
        -- exists v. rewrite elem_of_singleton in Hz'. subst. set_solver.
        -- apply Hz in Hz' as [u [HuD Hu]]. exists u. set_solver.
      * intros [u [HuD Hu]].
        apply elem_of_union in HuD as [HuD|HuD].
        -- rewrite elem_of_singleton in HuD. subst u.
           apply elem_of_union. left. rewrite Hu in Hv. inversion Hv. set_solver.
        -- apply elem_of_union. right. apply Hz. exists u. set_solver.
    + pose proof (IH z) as Hz. split.
      * intros Hz'. apply Hz in Hz' as [u [HuD Hu]]. exists u. set_solver.
      * intros [u [HuD Hu]].
        apply elem_of_union in HuD as [HuD|HuD].
        -- rewrite elem_of_singleton in HuD. subst u. rewrite Hu in Hv. discriminate.
        -- apply Hz. exists u. set_solver.
Qed.

Definition logic_var_swap (x y : atom) : logic_var → logic_var :=
  swap (LVFree x) (LVFree y).

Definition lvars_swap (x y : atom) (D : lvset) : lvset :=
  swap (LVFree x) (LVFree y) D.

Lemma logic_var_swap_unfold x y v :
  logic_var_swap x y v = eq_swap (LVFree x) (LVFree y) v.
Proof. reflexivity. Qed.

Lemma lvars_swap_unfold x y D :
  lvars_swap x y D = gset_swap (LVFree x) (LVFree y) D.
Proof. reflexivity. Qed.

Lemma logic_var_swap_sym x y v :
  logic_var_swap x y v = logic_var_swap y x v.
Proof.
  unfold logic_var_swap. apply swap_sym.
Qed.

Lemma lvars_swap_sym x y D :
  lvars_swap x y D = lvars_swap y x D.
Proof.
  unfold lvars_swap. apply swap_sym.
Qed.

Lemma logic_var_free_eq_swap x y z :
  eq_swap (LVFree x) (LVFree y) (LVFree z) = LVFree (atom_swap x y z).
Proof.
  unfold atom_swap, eq_swap. repeat destruct decide; congruence.
Qed.

Lemma lvars_fv_swap x y (D : lvset) :
  lvars_fv (lvars_swap x y D) = aset_swap x y (lvars_fv D).
Proof.
  apply set_eq. intros z.
  rewrite lvars_fv_elem, elem_of_aset_swap, lvars_fv_elem.
  change (LVFree z ∈ gset_swap (LVFree x) (LVFree y) D ↔
    LVFree (atom_swap x y z) ∈ D).
  rewrite gset_swap_elem, logic_var_free_eq_swap.
  reflexivity.
Qed.

Definition lvars_of_atoms (X : aset) : lvset :=
  set_map LVFree X.

Definition lvars_of_bvars (B : gset nat) : lvset :=
  set_map LVBound B.

Lemma lvars_to_atoms_of_atoms η (X : aset) :
  lvars_to_atoms η (lvars_of_atoms X) = X.
Proof.
  apply set_eq. intros x.
  rewrite lvars_to_atoms_elem.
  split.
  - intros [v [HvD Hv]].
    unfold lvars_of_atoms in HvD.
    apply elem_of_map in HvD as [a [-> Ha]].
    cbn in Hv. inversion Hv. subst. exact Ha.
  - intros Hx. exists (LVFree x). split; [|reflexivity].
    unfold lvars_of_atoms. apply elem_of_map.
    exists x. split; [reflexivity | exact Hx].
Qed.

Lemma lvars_to_atoms_union η (D E : lvset) :
  lvars_to_atoms η (D ∪ E) =
  lvars_to_atoms η D ∪ lvars_to_atoms η E.
Proof.
  apply set_eq. intros x.
  rewrite lvars_to_atoms_elem.
  rewrite elem_of_union.
  rewrite !lvars_to_atoms_elem.
  split.
  - intros [v [Hv Hatom]].
    apply elem_of_union in Hv as [Hv|Hv].
    + left. exists v. split; [exact Hv|exact Hatom].
    + right. exists v. split; [exact Hv|exact Hatom].
  - intros Hx.
    destruct Hx as [[v [Hv Hatom]]|[v [Hv Hatom]]].
    + exists v. split; [set_solver|exact Hatom].
    + exists v. split; [set_solver|exact Hatom].
Qed.
