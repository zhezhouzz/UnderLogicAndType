(** * Generic key shifts *)

From ContextBase.Swap Require Export SetSwap.

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

Lemma atom_key_shift_inj (k : nat) : Inj (=) (=) (λ x : atom, x).
Proof.
  intros x y Heq. exact Heq.
Qed.

#[global] Instance atom_shift_key : ShiftKey atom := {
  key_shift := λ _ x, x;
  key_shift_inj := atom_key_shift_inj
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
