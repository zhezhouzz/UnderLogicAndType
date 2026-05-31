(** * Finite-set swap *)

From ContextBase.Swap Require Export Swap.

Definition set_swap {A : Type} `{Countable A} (x y : A) (D : gset A) : gset A :=
  set_map (swap x y) D.

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

Lemma set_swap_mono {A : Type} `{Countable A}
    (x y : A) (X Y : gset A) :
  X ⊆ Y ->
  set_swap x y X ⊆ set_swap x y Y.
Proof.
  intros Hsub z Hz.
  apply set_swap_elem in Hz.
  apply set_swap_elem.
  exact (Hsub _ Hz).
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

Lemma set_swap_difference_fresh {A : Type} `{Countable A}
    (x y : A) (D R : gset A) :
  x ∉ R ->
  y ∉ R ->
  set_swap x y (D ∖ R) = set_swap x y D ∖ R.
Proof.
  intros Hx Hy.
  apply set_eq. intros z.
  rewrite elem_of_difference, !set_swap_elem, elem_of_difference.
  assert (HR : z ∈ R <-> swap x y z ∈ R).
  {
    unfold swap. repeat destruct decide; subst; set_solver.
  }
  set_solver.
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
