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

Lemma set_swap_opened_singleton_intersection
    {A : Type} `{Countable A} (M A0 : gset A) x y :
  x ∈ M ->
  y ∉ M ->
  x ∉ A0 ->
  y ∉ A0 ->
  (M ∪ {[y]}) ∩ (A0 ∪ {[y]}) =
    set_swap x y (M ∩ (A0 ∪ {[x]})).
Proof.
  intros HxM HyM HxA HyA.
  assert (Hxy : x <> y).
  { intros ->. exact (HyM HxM). }
  apply set_eq. intros a.
  rewrite set_swap_elem.
  destruct (decide (a = x)) as [->|Hax].
  - replace (swap x y x) with y
      by (unfold swap; repeat destruct decide; congruence).
    split.
    + intros Hleft. exfalso.
      apply elem_of_intersection in Hleft as [_ HxAy].
      apply elem_of_union in HxAy as [HxA'|Hxy'].
      * exact (HxA HxA').
      * apply elem_of_singleton in Hxy'. contradiction.
    + intros Hright. exfalso.
      apply elem_of_intersection in Hright as [HyM' _].
      exact (HyM HyM').
  - destruct (decide (a = y)) as [->|Hay].
    + replace (swap x y y) with x
        by (unfold swap; repeat destruct decide; congruence).
      split.
      * intros _. apply elem_of_intersection. split.
        -- exact HxM.
        -- apply elem_of_union_r. apply elem_of_singleton. reflexivity.
      * intros _. apply elem_of_intersection. split.
        -- apply elem_of_union_r. apply elem_of_singleton. reflexivity.
        -- apply elem_of_union_r. apply elem_of_singleton. reflexivity.
    + replace (swap x y a) with a
        by (unfold swap; repeat destruct decide; congruence).
      split.
      * intros Hleft.
        apply elem_of_intersection in Hleft as [HaMy HaAy].
        apply elem_of_intersection. split.
        -- apply elem_of_union in HaMy as [HaM|Hay']; [exact HaM|].
           apply elem_of_singleton in Hay'. contradiction.
        -- apply elem_of_union_l.
           apply elem_of_union in HaAy as [HaA|Hay']; [exact HaA|].
           apply elem_of_singleton in Hay'. contradiction.
      * intros Hright.
        apply elem_of_intersection in Hright as [HaM HaAx].
        apply elem_of_intersection. split.
        -- apply elem_of_union_l. exact HaM.
        -- apply elem_of_union_l.
           apply elem_of_union in HaAx as [HaA|Hax']; [exact HaA|].
           apply elem_of_singleton in Hax'. contradiction.
Qed.

Lemma set_swap_difference {A : Type} `{Countable A} (x y : A) (X Y : gset A) :
  set_swap x y (X ∖ Y) = set_swap x y X ∖ set_swap x y Y.
Proof.
  apply set_eq. intros z.
  rewrite elem_of_difference, !set_swap_elem, elem_of_difference.
  reflexivity.
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
