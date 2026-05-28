(** * Generic point swap *)

From ContextBase Require Export Atoms.

Definition swap {A : Type} `{EqDecision A} (x y z : A) : A :=
  if decide (z = x) then y else if decide (z = y) then x else z.

Lemma swap_involutive {A : Type} `{EqDecision A} (x y z : A) :
  swap x y (swap x y z) = z.
Proof.
  unfold swap. repeat destruct decide; congruence.
Qed.

Lemma swap_sym {A : Type} `{EqDecision A} (x y z : A) :
  swap x y z = swap y x z.
Proof.
  unfold swap. repeat destruct decide; congruence.
Qed.

Lemma swap_fresh {A : Type} `{EqDecision A} (x y z : A) :
  z ≠ x →
  z ≠ y →
  swap x y z = z.
Proof.
  unfold swap. repeat destruct decide; congruence.
Qed.

Lemma swap_l {A : Type} `{EqDecision A} (x y : A) :
  swap x y x = y.
Proof.
  unfold swap. destruct decide; congruence.
Qed.

Lemma swap_r {A : Type} `{EqDecision A} (x y : A) :
  swap x y y = x.
Proof.
  unfold swap. repeat destruct decide; congruence.
Qed.

Lemma swap_conjugate {A : Type} `{EqDecision A} (a b x y z : A) :
  swap a b (swap x y z) =
  swap (swap a b x) (swap a b y) (swap a b z).
Proof.
  unfold swap. repeat destruct decide; congruence.
Qed.

Lemma swap_conjugate_inv {A : Type} `{EqDecision A} (a b x y z : A) :
  swap x y (swap a b z) =
  swap a b (swap (swap a b x) (swap a b y) z).
Proof.
  unfold swap. repeat destruct decide; congruence.
Qed.

Lemma swap_inj {A : Type} `{EqDecision A} (x y : A) :
  Inj (=) (=) (swap x y).
Proof.
  intros z1 z2 Heq.
  rewrite <- (swap_involutive x y z1).
  rewrite <- (swap_involutive x y z2).
  by rewrite Heq.
Qed.
