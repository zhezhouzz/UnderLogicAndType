(** * ChoicePrelude.Prelude

    Top-level shared infrastructure for the concrete development.  This file
    deliberately sits before both CoreLang and ChoiceAlgebra: it provides the
    global atom type, finite atom sets, an abstract value interface, freshness
    helpers, and the [Stale] interface used by all later layers. *)

From stdpp Require Export gmap sets fin_sets fin_map_dom countable.
From Corelib Require Export Program.Wf.
From Hammer Require Export Hammer.

(** ** Shared atom and freshness infrastructure *)

Definition atom : Type := positive.
#[global] Instance atom_eqdec     : EqDecision atom := _.
#[global] Instance atom_countable : Countable  atom := _.
#[global] Instance atom_infinite  : Infinite   atom := _.
Notation aset := (gset atom).

(** Free-variable/resource-domain collection. *)
Class Stale A := stale : A → aset.

#[global] Instance stale_aset : Stale aset := id.

Notation "x '#' s" := (x ∉ stale s) (at level 40).

(** ** Logic variables

    Logic and type qualifiers may mention both locally-nameless bound
    coordinates and ordinary atom coordinates.  We keep these references in a
    single finite set so opening a binder is just a finite-set map from the
    bound representative to the chosen atom.

    [LVBound k] is not a stale atom by itself; it becomes one only after an
    explicit open operation. *)
Inductive logic_var : Type :=
  | LVBound (k : nat)
  | LVFree  (x : atom).

#[global] Instance logic_var_eqdec : EqDecision logic_var.
Proof. solve_decision. Qed.
#[global] Instance logic_var_countable : Countable logic_var.
Proof.
  refine (inj_countable'
    (λ v, match v with LVBound k => inl k | LVFree x => inr x end)
    (λ s, match s with inl k => LVBound k | inr x => LVFree x end) _).
  intros []; reflexivity.
Qed.

Notation lvset := (gset logic_var).

Definition logic_var_fv (v : logic_var) : aset :=
  match v with
  | LVBound _ => ∅
  | LVFree x => {[x]}
  end.

Definition logic_var_bv (v : logic_var) : gset nat :=
  match v with
  | LVBound k => {[k]}
  | LVFree _ => ∅
  end.

Definition lvars_fv (D : lvset) : aset :=
  set_fold (λ v acc, logic_var_fv v ∪ acc) ∅ D.

Definition lvars_bv (D : lvset) : gset nat :=
  set_fold (λ v acc, logic_var_bv v ∪ acc) ∅ D.

Definition logic_var_open (k : nat) (x : atom) (v : logic_var) : logic_var :=
  match v with
  | LVBound j => if decide (j = k) then LVFree x else LVBound j
  | LVFree y => LVFree y
  end.

Definition lvars_open (k : nat) (x : atom) (D : lvset) : lvset :=
  set_map (logic_var_open k x) D.

Definition logic_var_swap (x y : atom) (v : logic_var) : logic_var :=
  match v with
  | LVBound k => LVBound k
  | LVFree z =>
      LVFree (if decide (z = x) then y else if decide (z = y) then x else z)
  end.

Definition lvars_swap (x y : atom) (D : lvset) : lvset :=
  set_map (logic_var_swap x y) D.

Definition lvars_of_atoms (X : aset) : lvset :=
  set_map LVFree X.

Class IntoLVars A := into_lvars : A → lvset.

#[global] Instance into_lvars_aset : IntoLVars aset := lvars_of_atoms.
#[global] Instance into_lvars_lvset : IntoLVars lvset := id.

Lemma lvars_fv_of_atoms (X : aset) :
  lvars_fv (lvars_of_atoms X) = X.
Proof.
Admitted.

Lemma lvars_bv_of_atoms (X : aset) :
  lvars_bv (lvars_of_atoms X) = ∅.
Proof.
Admitted.

Lemma logic_var_bv_swap x y v :
  logic_var_bv (logic_var_swap x y v) = logic_var_bv v.
Proof.
  destruct v; simpl; repeat destruct decide; reflexivity.
Qed.

Lemma lvars_bv_swap x y (D : lvset) :
  lvars_bv (lvars_swap x y D) = lvars_bv D.
Proof.
Admitted.

Lemma logic_var_swap_involutive x y v :
  logic_var_swap x y (logic_var_swap x y v) = v.
Proof.
  destruct v as [k|z]; simpl; [reflexivity |].
  repeat destruct decide; subst; try reflexivity; congruence.
Qed.

Lemma lvars_swap_involutive x y (D : lvset) :
  lvars_swap x y (lvars_swap x y D) = D.
Proof.
Admitted.

Lemma lvars_fv_open_subset k x (D : lvset) :
  lvars_fv (lvars_open k x D) ⊆ lvars_fv D ∪ {[x]}.
Proof.
Admitted.

#[global] Instance stale_logic_var : Stale logic_var := logic_var_fv.
Arguments stale_logic_var /.

#[global] Instance stale_logic_vars : Stale lvset := lvars_fv.
Arguments stale_logic_vars /.

(** ** Abstract store values

    The algebraic layers quantify over store values abstractly.  The
    ChoiceType layer later instantiates this interface with CoreLang [value]s. *)
Class ValueSig (V : Type) := {
  valuesig_eqdec : EqDecision V;
  valuesig_inhabited : Inhabited V;
}.

#[global] Existing Instance valuesig_eqdec.
#[global] Existing Instance valuesig_inhabited.

Definition fresh_for (s : aset) : atom := fresh s.

Lemma fresh_for_not_in (s : aset) : fresh_for s ∉ s.
Proof. apply is_fresh. Qed.

Ltac pick_fresh x s :=
  let a := fresh x in
  set (a := fresh_for s);
  assert (a ∉ s) by apply fresh_for_not_in.

#[global] Hint Unfold stale : class_simpl.
