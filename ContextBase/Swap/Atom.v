(** * Atom instances for generic key operations *)

From ContextBase.Swap Require Export Core.

Lemma atom_key_shift_inj (k : nat) : Inj (=) (=) (λ x : atom, x).
Proof.
  intros x y Heq. exact Heq.
Qed.

#[global] Instance atom_shift_key : ShiftKey atom := {
  key_shift := λ _ x, x;
  key_shift_inj := atom_key_shift_inj
}.

