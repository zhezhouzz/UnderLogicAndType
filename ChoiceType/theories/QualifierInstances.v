(** * ChoiceType.QualifierInstances

    Locally-nameless theorem-class instances for shallow type qualifiers.

    Qualifiers open binders with atoms, not CoreLang values.  We therefore only
    register atom-open instances whose statements are syntactic/domain facts.
    The full [OpenSwap] instance is intentionally absent: shallow qualifier
    propositions may be equal only up to logical equivalence after reordering
    nested existential witnesses. *)

From LocallyNameless Require Import Classes.
From ChoiceType Require Import QualifierProps.

#[global] Instance OpenFv_qualifier : OpenFv atom type_qualifier.
Proof.
  intros [B d p] x k. unfold open_one, stale; simpl.
  destruct (decide (k ∈ B)); set_solver.
Qed.

#[global] Instance OpenFvPrime_qualifier : OpenFvPrime atom type_qualifier.
Proof.
  intros [B d p] x k. unfold open_one, stale; simpl.
  destruct (decide (k ∈ B)); set_solver.
Qed.

#[global] Instance OpenRecLc_qualifier : OpenRecLc atom type_qualifier.
Proof.
  intros [B d p] Hlc k x. unfold is_lc, open_one in *. simpl in *.
  unfold lc_qualifier in Hlc. simpl in Hlc.
  rewrite Hlc. rewrite decide_False by set_solver. reflexivity.
Qed.

#[global] Instance OpenLcRespect_qualifier : OpenLcRespect atom type_qualifier.
Proof.
  intros [B d p] x y k Hopen _ _.
  unfold is_lc, open_one in *. simpl in *.
  destruct (decide (k ∈ B)); simpl in *; set_solver.
Qed.

#[global] Instance OpenIdemp_qualifier : OpenIdemp atom type_qualifier.
Proof.
  intros [B d p] x y k _. unfold open_one, qual_open_atom; simpl.
  destruct (decide (k ∈ B)) as [Hin | Hnot].
  - simpl. destruct (decide (k ∈ B ∖ {[k]})); [set_solver | reflexivity].
  - simpl. rewrite decide_False by done. reflexivity.
Qed.
