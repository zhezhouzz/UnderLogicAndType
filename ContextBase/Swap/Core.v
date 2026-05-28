(** * Generic swap and shift infrastructure *)

From ContextBase Require Export Atoms.

Definition swap {A : Type} `{EqDecision A} (x y z : A) : A :=
  if decide (z = x) then y else if decide (z = y) then x else z.

Definition set_swap {A : Type} `{Countable A} (x y : A) (D : gset A) : gset A :=
  set_map (swap x y) D.

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

Lemma set_swap_elem {A : Type} `{Countable A} (x y z : A) (D : gset A) :
  z ∈ set_swap x y D ↔ swap x y z ∈ D.
Proof.
  unfold set_swap. split.
  - intros [z0 [-> Hz0]]%elem_of_map.
    rewrite swap_involutive. exact Hz0.
  - intros Hz.
    apply elem_of_map. exists (swap x y z). split;
      [symmetry; apply swap_involutive | exact Hz].
Qed.

Lemma set_swap_involutive {A : Type} `{Countable A} (x y : A) (D : gset A) :
  set_swap x y (set_swap x y D) = D.
Proof.
  apply set_eq. intros z. rewrite set_swap_elem, set_swap_elem.
  rewrite swap_involutive. reflexivity.
Qed.

Lemma set_swap_sym {A : Type} `{Countable A} (x y : A) (D : gset A) :
  set_swap x y D = set_swap y x D.
Proof.
  apply set_eq. intros z.
  rewrite !set_swap_elem, swap_sym. reflexivity.
Qed.

Lemma set_swap_fresh {A : Type} `{Countable A} (x y : A) (D : gset A) :
  x ∉ D →
  y ∉ D →
  set_swap x y D = D.
Proof.
  intros Hx Hy.
  apply set_eq. intros z.
  unfold set_swap. rewrite elem_of_map.
  split.
  - intros [z0 [-> HzD]].
    rewrite swap_fresh; [exact HzD | intros ->; contradiction | intros ->; contradiction].
  - intros HzD.
    exists z. split; [|exact HzD].
    symmetry. apply swap_fresh; intros ->; contradiction.
Qed.

Lemma elem_of_set_swap {A : Type} `{Countable A} (x y z : A) (D : gset A) :
  z ∈ set_swap x y D ↔ swap x y z ∈ D.
Proof.
  apply set_swap_elem.
Qed.

Lemma set_swap_conjugate {A : Type} `{Countable A} (a b x y : A) (D : gset A) :
  set_swap a b (set_swap x y D) =
  set_swap (swap a b x) (swap a b y) (set_swap a b D).
Proof.
  apply set_eq. intros z.
  rewrite !set_swap_elem.
  rewrite swap_conjugate_inv. reflexivity.
Qed.

Lemma set_swap_conjugate_inv {A : Type} `{Countable A} (a b x y : A) (D : gset A) :
  set_swap x y (set_swap a b D) =
  set_swap a b (set_swap (swap a b x) (swap a b y) D).
Proof.
  apply set_eq. intros z.
  rewrite !set_swap_elem.
  rewrite swap_conjugate. reflexivity.
Qed.

Lemma set_swap_empty {A : Type} `{Countable A} (x y : A) :
  set_swap x y (∅ : gset A) = ∅.
Proof.
  apply set_eq. intros z.
  rewrite set_swap_elem. better_set_solver.
Qed.

Lemma set_swap_union {A : Type} `{Countable A} (x y : A) (X Y : gset A) :
  set_swap x y (X ∪ Y) = set_swap x y X ∪ set_swap x y Y.
Proof.
  apply set_eq. intros z.
  rewrite elem_of_union, !set_swap_elem, elem_of_union. reflexivity.
Qed.

Lemma set_swap_intersection {A : Type} `{Countable A} (x y : A) (X Y : gset A) :
  set_swap x y (X ∩ Y) = set_swap x y X ∩ set_swap x y Y.
Proof.
  apply set_eq. intros z.
  rewrite elem_of_intersection, !set_swap_elem, elem_of_intersection. reflexivity.
Qed.

Lemma set_swap_difference_l {A : Type} `{Countable A} (x y : A) (D : gset A) :
  set_swap x y (D ∖ {[x]}) = set_swap x y D ∖ {[y]}.
Proof.
  apply set_eq. intros z.
  rewrite elem_of_difference, !set_swap_elem, elem_of_singleton.
  unfold swap. repeat destruct decide; subst; better_set_solver.
Qed.

Lemma set_swap_singleton {A : Type} `{Countable A} (x y z : A) :
  set_swap x y ({[z]} : gset A) = {[swap x y z]}.
Proof.
  apply set_eq. intros u.
  rewrite set_swap_elem, !elem_of_singleton.
  split; intro Hu.
  - rewrite <- Hu. symmetry. apply swap_involutive.
  - subst u. apply swap_involutive.
Qed.

(** Shifts are key renamings for binder-depth structure. *)
Class ShiftKey (K : Type) := {
  key_shift : nat → K → K;
  key_shift_inj : ∀ k, Inj (=) (=) (key_shift k)
}.

Definition nat_shift_key (k n : nat) : nat := k + n.

Lemma nat_shift_key_inj k : Inj (=) (=) (nat_shift_key k).
Proof.
  intros i j Hij. unfold nat_shift_key in Hij. lia.
Qed.

#[global] Instance nat_shift_key_inst : ShiftKey nat := {
  key_shift := nat_shift_key;
  key_shift_inj := nat_shift_key_inj
}.

Lemma elem_of_gset_shift {A : Type} `{Countable A} `{!ShiftKey A}
    (k : nat) (z : A) (D : gset A) :
  key_shift k z ∈ (set_map (key_shift k) D : gset A) ↔ z ∈ D.
Proof.
  split.
  - intros [z0 [Hz Hz0]]%elem_of_map.
    apply (key_shift_inj k) in Hz. subst z0. exact Hz0.
  - intros Hz.
    apply elem_of_map. exists z. split; [reflexivity | exact Hz].
Qed.

Lemma gset_shift_union {A : Type} `{Countable A} `{!ShiftKey A}
    (k : nat) (X Y : gset A) :
  set_map (key_shift k) (X ∪ Y) =
  ((set_map (key_shift k) X : gset A) ∪ set_map (key_shift k) Y).
Proof.
  apply set_eq. intros z.
  split.
  - intros [u [-> Hu]]%elem_of_map.
    apply elem_of_union in Hu as [Hu | Hu].
    + apply elem_of_union. left.
      apply elem_of_map. exists u. split; [reflexivity | exact Hu].
    + apply elem_of_union. right.
      apply elem_of_map. exists u. split; [reflexivity | exact Hu].
  - intros [Hz | Hz]%elem_of_union.
    + apply elem_of_map in Hz as [u [Heq Hu]]. subst z.
      apply elem_of_map. exists u. split; [reflexivity | better_set_solver].
    + apply elem_of_map in Hz as [u [Heq Hu]]. subst z.
      apply elem_of_map. exists u. split; [reflexivity | better_set_solver].
Qed.

Lemma gset_shift_intersection {A : Type} `{Countable A} `{!ShiftKey A}
    (k : nat) (X Y : gset A) :
  set_map (key_shift k) (X ∩ Y) =
  ((set_map (key_shift k) X : gset A) ∩ set_map (key_shift k) Y).
Proof.
  apply set_eq. intros z.
  split.
  - intros [u [-> Hu]]%elem_of_map.
    apply elem_of_intersection in Hu as [HuX HuY].
    apply elem_of_intersection. split; apply elem_of_map; eexists; split; eauto.
  - intros [HzX HzY]%elem_of_intersection.
    apply elem_of_map in HzX as [u [HeqX HuX]]. subst z.
    apply elem_of_map in HzY as [v [Hv HuY]].
    apply (key_shift_inj k) in Hv. subst v.
    apply elem_of_map. exists u. split; [reflexivity | better_set_solver].
Qed.
