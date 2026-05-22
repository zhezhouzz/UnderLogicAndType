(** * ChoicePrelude.Prelude

    Top-level shared infrastructure for the concrete development.  This file
    deliberately sits before both CoreLang and ChoiceAlgebra: it provides the
    global atom type, finite atom sets, an abstract value interface, freshness
    helpers, and the [Stale] interface used by all later layers. *)

From stdpp Require Export gmap sets fin_sets fin_map_dom fin_maps countable.
From Corelib Require Export Program.Wf.
From Stdlib Require Export Lia.

(** ** Shared atom and freshness infrastructure *)

Definition atom : Type := positive.
#[global] Instance atom_eqdec     : EqDecision atom := _.
#[global] Instance atom_countable : Countable  atom := _.
#[global] Instance atom_infinite  : Infinite   atom := _.
Notation aset := (gset atom).

Lemma inter_self (X : aset) :
  X ∩ X = X.
Proof.
  set_solver.
Qed.

Lemma inter_union_singleton_l (X : aset) (ν : atom) :
  (X ∪ {[ν]}) ∩ X = X.
Proof.
  set_solver.
Qed.

Lemma inter_union_singleton_r_fresh (X : aset) (ν : atom) :
  ν ∉ X →
  (X ∪ {[ν]}) ∩ ({[ν]} : aset) = {[ν]}.
Proof.
  set_solver.
Qed.

Lemma set_difference_pull_singleton (X Y : aset) x :
  x ∈ X →
  x ∉ Y →
  X ∖ Y = (X ∖ ({[x]} ∪ Y)) ∪ {[x]}.
Proof.
  intros HxX HxY.
  apply set_eq. intros z.
  rewrite elem_of_difference, elem_of_union, elem_of_difference,
    elem_of_union, !elem_of_singleton.
  split.
  - intros [HzX HzY].
    destruct (decide (z = x)) as [->|Hzx].
    + right. reflexivity.
    + left. split; [exact HzX |].
      intros [Hzx'|HzY']; [congruence | contradiction].
  - intros [[HzX Hnot] | Hzx].
    + split; [exact HzX |].
      intros HzY. apply Hnot. right. exact HzY.
    + subst z. split; [exact HxX | exact HxY].
Qed.

(** Free-variable/resource-domain collection. *)
Class Stale A := stale : A → aset.

#[global] Instance stale_aset : Stale aset := id.

Notation "x '#' s" := (x ∉ stale s) (at level 40).

(** ** Polymorphic finite-map compatibility and restriction *)

Section dom_gmap_filter.
  Context `{Countable K} `{EqDecision A}.

  Lemma dom_gmap_filter_key_in (m : gmap K A) (X : gset K) :
    dom (filter (λ kv : K * A, kv.1 ∈ X) m) = dom m ∩ X.
  Proof.
    apply leibniz_equiv_iff. intros i.
    rewrite elem_of_intersection, !elem_of_dom.
    unfold is_Some.
    split.
    - intros [v Hfilter].
      apply map_lookup_filter_Some in Hfilter as [Hm Hi].
      split; [exists v; exact Hm | exact Hi].
    - intros [[v Hm] Hi].
      exists v. apply map_lookup_filter_Some_2; [exact Hm | exact Hi].
  Qed.

  Lemma gmap_filter_key_pair (m : gmap K A) (X : gset K) :
    filter (λ '(k, _), k ∈ X) m = filter (λ kv : K * A, kv.1 ∈ X) m.
  Proof.
    apply map_filter_strong_ext_1.
    intros i x. reflexivity.
  Qed.

  Corollary dom_gmap_filter_key_in_pair (m : gmap K A) (X : gset K) :
    dom (filter (λ '(k, _), k ∈ X) m) = dom m ∩ X.
  Proof.
    rewrite (f_equal dom (gmap_filter_key_pair m X)).
    apply dom_gmap_filter_key_in.
  Qed.

End dom_gmap_filter.

Section MapOps.

Context `{Countable K}.
Context {A : Type}.

Definition map_compat (m1 m2 : gmap K A) : Prop :=
  ∀ x v1 v2, m1 !! x = Some v1 → m2 !! x = Some v2 → v1 = v2.

Definition map_restrict (m : gmap K A) (X : gset K) : gmap K A :=
  filter (λ '(k, _), k ∈ X) m.

Lemma map_compat_refl m : map_compat m m.
Proof.
  unfold map_compat. intros x v1 v2 H1 H2. congruence.
Qed.

Lemma map_restrict_dom m X :
  dom (map_restrict m X) = dom m ∩ X.
Proof.
  unfold map_restrict. apply dom_gmap_filter_key_in_pair.
Qed.

Lemma map_restrict_idemp m X :
  dom m ⊆ X → map_restrict m X = m.
Proof.
  unfold map_restrict. intros Hsub. apply map_filter_id.
  intros i x Hx. apply elem_of_dom_2 in Hx. set_solver.
Qed.

Lemma map_restrict_restrict m X Y :
  map_restrict (map_restrict m X) Y = map_restrict m (X ∩ Y).
Proof.
  unfold map_restrict.
  setoid_rewrite map_filter_filter.
  apply map_filter_ext.
  intros i x Hx. apply elem_of_dom_2 in Hx. set_solver.
Qed.

Lemma map_restrict_lookup_some m X x y :
  map_restrict m X !! x = Some y → x ∈ X ∧ m !! x = Some y.
Proof.
  unfold map_restrict. intro Hlookup.
  apply map_lookup_filter_Some in Hlookup.
  destruct Hlookup as [H1 H2]. split; [exact H2 | exact H1].
Qed.

Lemma map_restrict_insert_in m X x v :
  x ∈ X →
  map_restrict (<[x := v]> m) X = <[x := v]> (map_restrict m X).
Proof.
  intros Hx. unfold map_restrict.
  apply map_filter_insert_True. exact Hx.
Qed.

Lemma map_restrict_insert_notin m X x v :
  x ∉ X →
  map_restrict (<[x := v]> m) X = map_restrict m X.
Proof.
  intros Hx. unfold map_restrict.
  apply map_filter_insert_not. intros _. exact Hx.
Qed.

Lemma map_restrict_agree (m1 m2 : gmap K A) X :
  (∀ x, x ∈ X → m1 !! x = m2 !! x) →
  map_restrict m1 X = map_restrict m2 X.
Proof.
  intros Hagree. apply map_eq. intros x.
  destruct (decide (x ∈ X)) as [Hx | Hx].
  - unfold map_restrict.
    destruct (m1 !! x) as [v1|] eqn:H1.
    + transitivity (Some v1).
      * apply map_lookup_filter_Some_2; [exact H1 | exact Hx].
      * symmetry. apply map_lookup_filter_Some_2; [rewrite <- (Hagree x Hx); exact H1 | exact Hx].
    + transitivity (@None A).
      * apply map_lookup_filter_None_2. left. exact H1.
      * symmetry. apply map_lookup_filter_None_2. left.
        rewrite <- (Hagree x Hx). exact H1.
  - unfold map_restrict.
    transitivity (@None A).
    + apply map_lookup_filter_None_2. right. intros v _ Hin. exact (Hx Hin).
    + symmetry. apply map_lookup_filter_None_2. right. intros v _ Hin. exact (Hx Hin).
Qed.

End MapOps.

Arguments map_compat {_ _ _} _ _ /.
Arguments map_restrict {_ _ _} _ _ /.

(** ** Generic swaps

    The low-level operation for names is a symmetric swap.  Locally-nameless
    opening is treated as the special case that swaps a bound key with a free
    key; the old one-sided "replace this bound key by this atom" operation is
    kept below only as a migration aid. *)
Class SwapSupport (A B : Type) `{Countable A} := swap_support : B → gset A.

Class SwapAction (A B : Type) := swap : A → A → B → B.

Definition eq_swap {A : Type} `{EqDecision A} (x y z : A) : A :=
  if decide (z = x) then y else if decide (z = y) then x else z.

Class LawfulSwapAction (A B : Type) `{Countable A}
    `{SwapSupport A B} `{SwapAction A A} `{SwapAction A B} := {
  swap_involutive : ∀ x y (b : B),
    @swap A B _ x y (@swap A B _ x y b) = b;
  swap_sym : ∀ x y (b : B),
    @swap A B _ x y b = @swap A B _ y x b;
  swap_conjugate : ∀ p q x y (z : B),
    @swap A B _ p q (@swap A B _ x y z) =
    @swap A B _ (@swap A A _ p q x) (@swap A A _ p q y)
      (@swap A B _ p q z);
  swap_conjugate_inv : ∀ p q x y (z : B),
    @swap A B _ x y (@swap A B _ p q z) =
    @swap A B _ p q
      (@swap A B _ (@swap A A _ p q x) (@swap A A _ p q y) z);
  swap_fresh : ∀ x y (b : B),
    x ∉ swap_support b →
    y ∉ swap_support b →
    @swap A B _ x y b = b
}.

#[global] Instance swap_support_self {A : Type} `{Countable A} : SwapSupport A A := singleton.

#[global] Instance swap_support_gset {A : Type} `{Countable A} :
  SwapSupport A (gset A) := id.

#[global] Instance swap_action_self {A : Type} `{EqDecision A} :
  SwapAction A A := eq_swap.

Lemma eq_swap_involutive {A : Type} `{EqDecision A} (x y z : A) :
  eq_swap x y (eq_swap x y z) = z.
Proof.
  unfold eq_swap. repeat destruct decide; congruence.
Qed.

Lemma eq_swap_sym {A : Type} `{EqDecision A} (x y z : A) :
  eq_swap x y z = eq_swap y x z.
Proof.
  unfold eq_swap. repeat destruct decide; congruence.
Qed.

Lemma eq_swap_fresh {A : Type} `{EqDecision A} (x y z : A) :
  z ≠ x →
  z ≠ y →
  eq_swap x y z = z.
Proof.
  unfold eq_swap. repeat destruct decide; congruence.
Qed.

Lemma eq_swap_l {A : Type} `{EqDecision A} (x y : A) :
  eq_swap x y x = y.
Proof.
  unfold eq_swap. destruct decide; congruence.
Qed.

Lemma eq_swap_r {A : Type} `{EqDecision A} (x y : A) :
  eq_swap x y y = x.
Proof.
  unfold eq_swap. repeat destruct decide; congruence.
Qed.

Lemma eq_swap_conjugate {A : Type} `{EqDecision A} (a b x y z : A) :
  eq_swap a b (eq_swap x y z) =
  eq_swap (eq_swap a b x) (eq_swap a b y) (eq_swap a b z).
Proof.
  unfold eq_swap. repeat destruct decide; congruence.
Qed.

Lemma eq_swap_conjugate_inv {A : Type} `{EqDecision A} (a b x y z : A) :
  eq_swap x y (eq_swap a b z) =
  eq_swap a b (eq_swap (eq_swap a b x) (eq_swap a b y) z).
Proof.
  unfold eq_swap. repeat destruct decide; congruence.
Qed.

Lemma eq_swap_inj {A : Type} `{EqDecision A} (x y : A) :
  Inj (=) (=) (eq_swap x y).
Proof.
  intros z1 z2 Heq.
  rewrite <- (eq_swap_involutive x y z1).
  rewrite <- (eq_swap_involutive x y z2).
  by rewrite Heq.
Qed.

(** The legacy key-swap names are kept as compatibility wrappers over the
    single generic swap operation. *)
Definition eq_key_swap {K : Type} `{EqDecision K} (x y z : K) : K :=
  eq_swap x y z.

Lemma eq_key_swap_involutive {K : Type} `{EqDecision K} (x y z : K) :
  eq_key_swap x y (eq_key_swap x y z) = z.
Proof. apply eq_swap_involutive. Qed.

Lemma eq_key_swap_fresh {K : Type} `{EqDecision K} (x y z : K) :
  z ≠ x →
  z ≠ y →
  eq_key_swap x y z = z.
Proof. apply eq_swap_fresh. Qed.

Lemma eq_key_swap_sym {K : Type} `{EqDecision K} (x y z : K) :
  eq_key_swap x y z = eq_key_swap y x z.
Proof. apply eq_swap_sym. Qed.

Lemma eq_key_swap_conjugate {K : Type} `{EqDecision K} (a b x y z : K) :
  eq_key_swap a b (eq_key_swap x y z) =
  eq_key_swap (eq_key_swap a b x) (eq_key_swap a b y) (eq_key_swap a b z).
Proof. apply eq_swap_conjugate. Qed.

Lemma eq_key_swap_conjugate_inv {K : Type} `{EqDecision K} (a b x y z : K) :
  eq_key_swap x y (eq_key_swap a b z) =
  eq_key_swap a b (eq_key_swap (eq_key_swap a b x) (eq_key_swap a b y) z).
Proof. apply eq_swap_conjugate_inv. Qed.

Lemma eq_key_swap_inj {K : Type} `{EqDecision K} (x y : K) :
  Inj (=) (=) (eq_key_swap x y).
Proof. apply eq_swap_inj. Qed.

#[global] Instance lawful_swap_action_self {A : Type} `{Countable A} :
  LawfulSwapAction A A.
Proof.
  split.
  - apply eq_swap_involutive.
  - apply eq_swap_sym.
  - apply eq_swap_conjugate.
  - apply eq_swap_conjugate_inv.
  - intros x y z Hx Hy. apply eq_swap_fresh.
    + intros ->. apply Hx. apply elem_of_singleton. reflexivity.
    + intros ->. apply Hy. apply elem_of_singleton. reflexivity.
Qed.

Class SwapKey (K : Type) `{Countable K} := {}.

#[global] Instance eq_swap_key (K : Type) `{Countable K} : SwapKey K := {}.

Definition key_swap {K : Type} `{Countable K} `{!SwapKey K}
    (x y z : K) : K :=
  @swap K K _ x y z.

Lemma key_swap_involutive {K : Type} `{Countable K} `{!SwapKey K} (x y z : K) :
  key_swap x y (key_swap x y z) = z.
Proof. apply swap_involutive. Qed.

Lemma key_swap_fresh {K : Type} `{Countable K} `{!SwapKey K} (x y z : K) :
  z ≠ x →
  z ≠ y →
  key_swap x y z = z.
Proof. apply eq_swap_fresh. Qed.

Lemma key_swap_sym {K : Type} `{Countable K} `{!SwapKey K} (x y z : K) :
  key_swap x y z = key_swap y x z.
Proof. apply swap_sym. Qed.

Lemma key_swap_conjugate {K : Type} `{Countable K} `{!SwapKey K} (a b x y z : K) :
  key_swap a b (key_swap x y z) =
  key_swap (key_swap a b x) (key_swap a b y) (key_swap a b z).
Proof. apply swap_conjugate. Qed.

Lemma key_swap_conjugate_inv {K : Type} `{Countable K} `{!SwapKey K} (a b x y z : K) :
  key_swap x y (key_swap a b z) =
  key_swap a b (key_swap (key_swap a b x) (key_swap a b y) z).
Proof. apply swap_conjugate_inv. Qed.

Lemma key_swap_inj {K : Type} `{Countable K} `{!SwapKey K} (x y : K) :
  Inj (=) (=) (key_swap x y).
Proof.
  intros z1 z2 Heq.
  rewrite <- (key_swap_involutive x y z1).
  rewrite <- (key_swap_involutive x y z2).
  by rewrite Heq.
Qed.

(** ** Generic shifts

    Shifts are key renamings for binder-depth structure.  On ordinary atom
    keys they are the identity; on locally-nameless keys they affect only the
    bound component. *)
Class ShiftKey (K : Type) := {
  key_shift : nat → K → K;
  key_shift_inj : ∀ k, Inj (=) (=) (key_shift k)
}.

Lemma atom_key_shift_inj (k : nat) : Inj (=) (=) (λ x : atom, x).
Proof.
  intros x y Heq. exact Heq.
Qed.

#[global] Instance atom_shift_key : ShiftKey atom := {
  key_shift := λ _ x, x;
  key_shift_inj := atom_key_shift_inj
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

Definition gset_swap {A : Type} `{Countable A} (x y : A) (D : gset A) : gset A :=
  set_map (eq_swap x y) D.

#[global] Instance swap_action_gset {A : Type} `{Countable A} :
  SwapAction A (gset A) := gset_swap.

Lemma gset_swap_elem {A : Type} `{Countable A} (x y z : A) (D : gset A) :
  z ∈ gset_swap x y D ↔ eq_swap x y z ∈ D.
Proof.
  unfold gset_swap. split.
  - intros [z0 [-> Hz0]]%elem_of_map.
    rewrite eq_swap_involutive. exact Hz0.
  - intros Hz.
    apply elem_of_map. exists (eq_swap x y z). split;
      [symmetry; apply eq_swap_involutive | exact Hz].
Qed.

Lemma gset_swap_involutive {A : Type} `{Countable A} (x y : A) (D : gset A) :
  gset_swap x y (gset_swap x y D) = D.
Proof.
  apply set_eq. intros z. rewrite gset_swap_elem, gset_swap_elem.
  rewrite eq_swap_involutive. reflexivity.
Qed.

Lemma gset_swap_sym {A : Type} `{Countable A} (x y : A) (D : gset A) :
  gset_swap x y D = gset_swap y x D.
Proof.
  apply set_eq. intros z.
  rewrite !gset_swap_elem, eq_swap_sym. reflexivity.
Qed.

Lemma gset_swap_fresh {A : Type} `{Countable A} (x y : A) (D : gset A) :
  x ∉ D →
  y ∉ D →
  gset_swap x y D = D.
Proof.
  intros Hx Hy.
  apply set_eq. intros z.
  unfold gset_swap. rewrite elem_of_map.
  split.
  - intros [z0 [-> HzD]].
    rewrite eq_swap_fresh; [exact HzD | intros ->; contradiction | intros ->; contradiction].
  - intros HzD.
    exists z. split; [|exact HzD].
    symmetry. apply eq_swap_fresh; intros ->; contradiction.
Qed.

Lemma elem_of_gset_swap {A : Type} `{Countable A} (x y z : A) (D : gset A) :
  z ∈ gset_swap x y D ↔ key_swap x y z ∈ D.
Proof.
  apply gset_swap_elem.
Qed.

Lemma gset_swap_conjugate {A : Type} `{Countable A} (a b x y : A) (D : gset A) :
  gset_swap a b (gset_swap x y D) =
  gset_swap (eq_swap a b x) (eq_swap a b y) (gset_swap a b D).
Proof.
  apply set_eq. intros z.
  rewrite !gset_swap_elem.
  rewrite eq_swap_conjugate_inv. reflexivity.
Qed.

Lemma gset_swap_conjugate_inv {A : Type} `{Countable A} (a b x y : A) (D : gset A) :
  gset_swap x y (gset_swap a b D) =
  gset_swap a b (gset_swap (eq_swap a b x) (eq_swap a b y) D).
Proof.
  apply set_eq. intros z.
  rewrite !gset_swap_elem.
  rewrite eq_swap_conjugate. reflexivity.
Qed.

Lemma gset_swap_empty {A : Type} `{Countable A} (x y : A) :
  gset_swap x y (∅ : gset A) = ∅.
Proof.
  apply set_eq. intros z.
  rewrite gset_swap_elem. set_solver.
Qed.

Lemma gset_swap_union {A : Type} `{Countable A} (x y : A) (X Y : gset A) :
  gset_swap x y (X ∪ Y) = gset_swap x y X ∪ gset_swap x y Y.
Proof.
  apply set_eq. intros z.
  rewrite elem_of_union, !gset_swap_elem, elem_of_union. reflexivity.
Qed.

Lemma gset_swap_intersection {A : Type} `{Countable A} (x y : A) (X Y : gset A) :
  gset_swap x y (X ∩ Y) = gset_swap x y X ∩ gset_swap x y Y.
Proof.
  apply set_eq. intros z.
  rewrite elem_of_intersection, !gset_swap_elem, elem_of_intersection. reflexivity.
Qed.

Lemma gset_swap_singleton {A : Type} `{Countable A} (x y z : A) :
  gset_swap x y ({[z]} : gset A) = {[key_swap x y z]}.
Proof.
  apply set_eq. intros u.
  rewrite gset_swap_elem, !elem_of_singleton.
  split; intro Hu.
  - rewrite <- Hu. symmetry. apply key_swap_involutive.
  - subst u. apply key_swap_involutive.
Qed.

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
      apply elem_of_map. exists u. split; [reflexivity | set_solver].
    + apply elem_of_map in Hz as [u [Heq Hu]]. subst z.
      apply elem_of_map. exists u. split; [reflexivity | set_solver].
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
    apply elem_of_map. exists u. split; [reflexivity | set_solver].
Qed.

#[global] Instance lawful_swap_action_gset {A : Type} `{Countable A} :
  LawfulSwapAction A (gset A).
Proof.
  split.
  - apply gset_swap_involutive.
  - apply gset_swap_sym.
  - apply gset_swap_conjugate.
  - apply gset_swap_conjugate_inv.
  - apply gset_swap_fresh.
Qed.

Definition swap_open {A B : Type} `{SwapAction A B} (x y : A) (b : B) : B :=
  swap x y b.

(** ** Atom-keyed swap wrappers *)

Definition atom_swap (x y z : atom) : atom :=
  eq_swap x y z.

Definition aset_swap (x y : atom) (X : aset) : aset :=
  gset_swap x y X.

Lemma atom_swap_involutive x y z :
  atom_swap x y (atom_swap x y z) = z.
Proof. apply eq_swap_involutive. Qed.

Lemma atom_swap_l x y :
  atom_swap x y x = y.
Proof. apply eq_swap_l. Qed.

Lemma atom_swap_r x y :
  atom_swap x y y = x.
Proof. apply eq_swap_r. Qed.

Lemma atom_swap_fresh x y z :
  z ≠ x →
  z ≠ y →
  atom_swap x y z = z.
Proof. apply eq_swap_fresh. Qed.

Lemma atom_swap_conjugate a b x y z :
  atom_swap a b (atom_swap x y z) =
  atom_swap (atom_swap a b x) (atom_swap a b y) (atom_swap a b z).
Proof. apply eq_swap_conjugate. Qed.

Lemma atom_swap_conjugate_inv a b x y z :
  atom_swap x y (atom_swap a b z) =
  atom_swap a b (atom_swap (atom_swap a b x) (atom_swap a b y) z).
Proof. apply eq_swap_conjugate_inv. Qed.

Lemma atom_swap_sym x y z :
  atom_swap x y z = atom_swap y x z.
Proof. apply eq_swap_sym. Qed.

Lemma atom_swap_inj x y : Inj (=) (=) (atom_swap x y).
Proof. apply eq_swap_inj. Qed.

Lemma elem_of_aset_swap x y z X :
  z ∈ aset_swap x y X ↔ atom_swap x y z ∈ X.
Proof.
  apply gset_swap_elem.
Qed.

Lemma aset_swap_involutive x y X :
  aset_swap x y (aset_swap x y X) = X.
Proof. apply gset_swap_involutive. Qed.

Lemma aset_swap_sym x y X :
  aset_swap x y X = aset_swap y x X.
Proof. apply gset_swap_sym. Qed.

Lemma aset_swap_fresh x y X :
  x ∉ X →
  y ∉ X →
  aset_swap x y X = X.
Proof. apply gset_swap_fresh. Qed.

Lemma aset_swap_union x y X Y :
  aset_swap x y (X ∪ Y) = aset_swap x y X ∪ aset_swap x y Y.
Proof.
  apply set_eq. intros z.
  rewrite elem_of_aset_swap, !elem_of_union.
  rewrite !elem_of_aset_swap.
  tauto.
Qed.

Lemma aset_swap_empty x y :
  aset_swap x y ∅ = ∅.
Proof. apply gset_swap_empty. Qed.

Lemma aset_swap_intersection x y X Y :
  aset_swap x y (X ∩ Y) = aset_swap x y X ∩ aset_swap x y Y.
Proof.
  apply set_eq. intros z.
  rewrite elem_of_aset_swap, !elem_of_intersection, !elem_of_aset_swap.
  tauto.
Qed.

Lemma aset_swap_disjoint x y X Y :
  aset_swap x y X ## aset_swap x y Y ↔ X ## Y.
Proof.
  unfold disjoint, set_disjoint_instance. split; intros Hdis z HzX HzY.
  - apply (Hdis (atom_swap x y z)).
    + rewrite elem_of_aset_swap, atom_swap_involutive. exact HzX.
    + rewrite elem_of_aset_swap, atom_swap_involutive. exact HzY.
  - rewrite elem_of_aset_swap in HzX.
    rewrite elem_of_aset_swap in HzY.
    exact (Hdis _ HzX HzY).
Qed.

Lemma aset_swap_singleton x y z :
  aset_swap x y ({[z]}) = {[atom_swap x y z]}.
Proof.
  apply set_eq. intros a.
  rewrite elem_of_aset_swap, !elem_of_singleton.
  split.
  - intros Ha.
    rewrite <- Ha. symmetry. apply atom_swap_involutive.
  - intros ->. apply atom_swap_involutive.
Qed.

Lemma aset_swap_conjugate a b x y X :
  aset_swap a b (aset_swap x y X) =
  aset_swap (atom_swap a b x) (atom_swap a b y) (aset_swap a b X).
Proof.
  apply set_eq. intros z.
  rewrite !elem_of_aset_swap.
  rewrite atom_swap_conjugate_inv. reflexivity.
Qed.

Lemma aset_swap_conjugate_inv a b x y X :
  aset_swap x y (aset_swap a b X) =
  aset_swap a b (aset_swap (atom_swap a b x) (atom_swap a b y) X).
Proof.
  apply set_eq. intros z.
  rewrite !elem_of_aset_swap.
  rewrite atom_swap_conjugate. reflexivity.
Qed.

Lemma aset_swap_difference_singleton x y z X :
  aset_swap x y (X ∖ {[z]}) =
  aset_swap x y X ∖ {[atom_swap x y z]}.
Proof.
  apply set_eq. intros a.
  rewrite elem_of_aset_swap, elem_of_difference, elem_of_singleton.
  rewrite elem_of_difference, elem_of_singleton, elem_of_aset_swap.
  split.
  - intros [Ha Hne]. split; [exact Ha |].
    intros Heq. apply Hne.
    rewrite <- (atom_swap_involutive x y z).
    by rewrite <- Heq.
  - intros [Ha Hne]. split; [exact Ha |].
    intros Heq. apply Hne.
    rewrite <- (atom_swap_involutive x y a).
    by rewrite Heq.
Qed.

Lemma aset_swap_difference x y X Y :
  aset_swap x y (X ∖ Y) =
  aset_swap x y X ∖ aset_swap x y Y.
Proof.
  apply set_eq. intros z.
  rewrite elem_of_aset_swap, !elem_of_difference, elem_of_aset_swap.
  split.
  - intros [HzX HzY]. split; [exact HzX |].
    intros HzswapY. apply HzY.
    rewrite elem_of_aset_swap in HzswapY.
    exact HzswapY.
  - intros [HzX HzY]. split; [exact HzX |].
    intros HzY'. apply HzY.
    rewrite elem_of_aset_swap.
    exact HzY'.
Qed.

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

Definition logic_var_support (v : logic_var) : lvset := {[v]}.

Definition lvars_fv (D : lvset) : aset :=
  set_fold (λ v acc, logic_var_fv v ∪ acc) ∅ D.

Definition lvars_bv (D : lvset) : gset nat :=
  set_fold (λ v acc, logic_var_bv v ∪ acc) ∅ D.

Lemma lvars_fv_elem D x :
  x ∈ lvars_fv D ↔ LVFree x ∈ D.
Proof.
  unfold lvars_fv.
  refine (set_fold_ind_L
    (fun acc D => ∀ x, x ∈ acc ↔ LVFree x ∈ D)
    (λ v acc, logic_var_fv v ∪ acc) ∅ _ _ D x).
  - intros y. set_solver.
  - intros v D' acc Hfresh IH z.
    destruct v as [k|a]; cbn [logic_var_fv];
      pose proof (IH z); set_solver.
Qed.

Lemma lvars_bv_elem D k :
  k ∈ lvars_bv D ↔ LVBound k ∈ D.
Proof.
  unfold lvars_bv.
  refine (set_fold_ind_L
    (fun acc D => ∀ k, k ∈ acc ↔ LVBound k ∈ D)
    (λ v acc, logic_var_bv v ∪ acc) ∅ _ _ D k).
  - intros j. set_solver.
  - intros v D' acc Hfresh IH j.
    destruct v as [i|y]; cbn [logic_var_bv];
      pose proof (IH j); set_solver.
Qed.

Definition logic_var_open_onesided (k : nat) (x : atom) (v : logic_var) : logic_var :=
  match v with
  | LVBound j => if decide (j = k) then LVFree x else LVBound j
  | LVFree y => LVFree y
  end.

Definition logic_var_open (k : nat) (x : atom) : logic_var → logic_var :=
  swap (LVBound k) (LVFree x).

Definition lvars_open (k : nat) (x : atom) (D : lvset) : lvset :=
  swap (LVBound k) (LVFree x) D.

Lemma logic_var_open_unfold k x v :
  logic_var_open k x v = eq_swap (LVBound k) (LVFree x) v.
Proof. reflexivity. Qed.

Lemma lvars_open_unfold k x D :
  lvars_open k x D = gset_swap (LVBound k) (LVFree x) D.
Proof. reflexivity. Qed.

Lemma logic_var_open_involutive k x v :
  logic_var_open k x (logic_var_open k x v) = v.
Proof.
  unfold logic_var_open. apply swap_involutive.
Qed.

Lemma lvars_open_involutive k x D :
  lvars_open k x (lvars_open k x D) = D.
Proof.
  unfold lvars_open. apply swap_involutive.
Qed.

Lemma logic_var_open_sym k x v :
  logic_var_open k x v = swap (LVFree x) (LVBound k) v.
Proof.
  unfold logic_var_open. apply swap_sym.
Qed.

Lemma lvars_open_sym k x D :
  lvars_open k x D = swap (LVFree x) (LVBound k) D.
Proof.
  unfold lvars_open. apply swap_sym.
Qed.

Lemma logic_var_open_onesided_eq_swap_fresh k x v :
  x ∉ logic_var_fv v →
  logic_var_open_onesided k x v = logic_var_open k x v.
Proof.
  destruct v as [j|y]; simpl.
  - unfold logic_var_open, swap, swap_action_self, eq_swap.
    repeat destruct decide; congruence.
  - intros Hfresh.
    unfold logic_var_open, swap, swap_action_self, eq_swap.
    rewrite not_elem_of_singleton in Hfresh.
    repeat destruct decide; congruence.
Qed.

Definition lvars_open_onesided (k : nat) (x : atom) (D : lvset) : lvset :=
  set_map (logic_var_open_onesided k x) D.

Lemma lvars_open_onesided_eq_swap_fresh k x D :
  x ∉ lvars_fv D →
  lvars_open_onesided k x D = lvars_open k x D.
Proof.
  intros Hfresh.
  apply set_eq. intros v.
  unfold lvars_open_onesided.
  rewrite lvars_open_unfold.
  unfold gset_swap.
  rewrite !elem_of_map.
  split.
  - intros [u [Hv Hu]]. exists u. split; [|exact Hu].
    rewrite Hv. apply logic_var_open_onesided_eq_swap_fresh.
    intros Hbad. apply Hfresh. apply lvars_fv_elem.
    destruct u as [j|y]; cbn [logic_var_fv] in Hbad;
      [set_solver | rewrite elem_of_singleton in Hbad; subst; exact Hu].
  - intros [u [Hv Hu]]. exists u. split; [|exact Hu].
    rewrite Hv. symmetry. apply logic_var_open_onesided_eq_swap_fresh.
    intros Hbad. apply Hfresh. apply lvars_fv_elem.
    destruct u as [j|y]; cbn [logic_var_fv] in Hbad;
      [set_solver | rewrite elem_of_singleton in Hbad; subst; exact Hu].
Qed.

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

Class IntoLVars A := into_lvars : A → lvset.

#[global] Instance into_lvars_aset : IntoLVars aset := lvars_of_atoms.
#[global] Instance into_lvars_lvset : IntoLVars lvset := id.

Lemma lvars_fv_of_atoms (X : aset) :
  lvars_fv (lvars_of_atoms X) = X.
Proof.
  apply set_eq. intros x.
  rewrite lvars_fv_elem.
  unfold lvars_of_atoms.
  rewrite elem_of_map.
  split.
  - intros [a [Heq Ha]]. inversion Heq. subst. exact Ha.
  - intros Hx. exists x. split; [reflexivity | exact Hx].
Qed.

Lemma lvars_bv_of_atoms (X : aset) :
  lvars_bv (lvars_of_atoms X) = ∅.
Proof.
  apply set_eq. intros k.
  rewrite lvars_bv_elem.
  unfold lvars_of_atoms.
  rewrite elem_of_empty, elem_of_map.
  split; [intros [a [Hbad _]]; discriminate | set_solver].
Qed.

Lemma lvars_open_of_atoms k x (X : aset) :
  x ∉ X →
  lvars_open k x (lvars_of_atoms X) = lvars_of_atoms X.
Proof.
  intros Hfresh.
  unfold lvars_open.
  apply gset_swap_fresh.
  - unfold lvars_of_atoms. intros Hin.
    apply elem_of_map in Hin as [a [Hbad _]]. discriminate.
  - unfold lvars_of_atoms. intros Hin.
    apply elem_of_map in Hin as [a [Heq Ha]].
    inversion Heq. subst. contradiction.
Qed.

Lemma lvars_fv_of_bvars (B : gset nat) :
  lvars_fv (lvars_of_bvars B) = ∅.
Proof.
  apply set_eq. intros x.
  rewrite lvars_fv_elem.
  unfold lvars_of_bvars.
  rewrite elem_of_empty, elem_of_map.
  split; [intros [k [Hbad _]]; discriminate | set_solver].
Qed.

Lemma lvars_fv_singleton_bound k :
  lvars_fv ({[LVBound k]} : lvset) = ∅.
Proof.
  apply set_eq. intros x.
  rewrite lvars_fv_elem.
  set_solver.
Qed.

Lemma lvars_fv_singleton_free x :
  lvars_fv ({[LVFree x]} : lvset) = {[x]}.
Proof.
  rewrite <- (lvars_fv_of_atoms ({[x]} : aset)).
  unfold lvars_of_atoms.
  rewrite set_map_singleton_L.
  reflexivity.
Qed.

Lemma lvars_fv_open k x (D : lvset) :
  lvars_fv (lvars_open k x D) =
  (lvars_fv D ∖ {[x]}) ∪
  (if decide (k ∈ lvars_bv D) then {[x]} else ∅).
Proof.
  apply set_eq. intros y.
  rewrite lvars_fv_elem.
  change (LVFree y ∈ gset_swap (LVBound k) (LVFree x) D ↔
    y ∈ (lvars_fv D ∖ {[x]}) ∪
      (if decide (k ∈ lvars_bv D) then {[x]} else ∅)).
  rewrite gset_swap_elem.
  destruct (decide (y = x)) as [->|Hyx].
  - rewrite eq_swap_r.
    destruct (decide (k ∈ lvars_bv D)) as [Hk|Hk].
    + rewrite elem_of_union, elem_of_difference, elem_of_singleton.
      rewrite lvars_bv_elem in Hk. tauto.
    + rewrite elem_of_union, elem_of_difference, elem_of_singleton.
      rewrite elem_of_empty. rewrite lvars_bv_elem in Hk. tauto.
  - rewrite eq_swap_fresh by congruence.
    destruct (decide (k ∈ lvars_bv D)); rewrite elem_of_union,
      elem_of_difference, !elem_of_singleton, ?elem_of_empty, lvars_fv_elem;
      tauto.
Qed.

Lemma lvars_bv_contains_bound_singleton k (D : lvset) :
  k ∈ lvars_bv (D ∪ {[LVBound k]}).
Proof.
  apply lvars_bv_elem. set_solver.
Qed.

Lemma lvars_fv_union (D1 D2 : lvset) :
  lvars_fv (D1 ∪ D2) = lvars_fv D1 ∪ lvars_fv D2.
Proof.
  apply set_eq. intros x.
  rewrite elem_of_union.
  rewrite !lvars_fv_elem.
  rewrite elem_of_union.
  tauto.
Qed.

Lemma logic_var_shift_inj : Inj (=) (=) logic_var_shift.
Proof.
  intros v1 v2 Heq.
  destruct v1 as [k1|x1], v2 as [k2|x2]; cbn in Heq; congruence.
Qed.

Lemma lvars_fv_shift D :
  lvars_fv (lvars_shift D) = lvars_fv D.
Proof.
  induction D as [|v D Hfresh IH] using set_ind_L.
  - unfold lvars_shift. rewrite set_map_empty. reflexivity.
  - unfold lvars_shift in *.
    rewrite set_map_union_L, set_map_singleton_L.
    rewrite !lvars_fv_union, IH.
    destruct v as [k|x]; cbn [logic_var_shift];
      rewrite ?lvars_fv_singleton_bound, ?lvars_fv_singleton_free;
      reflexivity.
Qed.

Lemma lvars_fv_open_atoms_with_bound k x (X : aset) :
  x ∉ X →
  lvars_fv (lvars_open k x (lvars_of_atoms X ∪ {[LVBound k]})) =
  X ∪ {[x]}.
Proof.
  intros Hfresh.
  rewrite lvars_fv_open.
  rewrite lvars_fv_union, lvars_fv_of_atoms, lvars_fv_singleton_bound.
  destruct (decide (k ∈ lvars_bv (lvars_of_atoms X ∪ {[LVBound k]}))) as [_|Hbad].
  - set_solver.
  - exfalso. apply Hbad. apply lvars_bv_contains_bound_singleton.
Qed.

Lemma logic_var_bv_swap x y v :
  logic_var_bv (logic_var_swap x y v) = logic_var_bv v.
Proof.
  destruct v; unfold logic_var_swap, swap, swap_action_self, eq_swap; simpl;
    repeat destruct decide; try congruence; reflexivity.
Qed.

Lemma lvars_bv_swap x y (D : lvset) :
  lvars_bv (lvars_swap x y D) = lvars_bv D.
Proof.
  apply set_eq. intros k.
  rewrite !lvars_bv_elem.
  change (LVBound k ∈ gset_swap (LVFree x) (LVFree y) D ↔ LVBound k ∈ D).
  rewrite gset_swap_elem.
  rewrite eq_swap_fresh by congruence.
  reflexivity.
Qed.

Lemma logic_var_swap_involutive x y v :
  logic_var_swap x y (logic_var_swap x y v) = v.
Proof.
  unfold logic_var_swap. apply swap_involutive.
Qed.

Lemma lvars_swap_involutive x y (D : lvset) :
  lvars_swap x y (lvars_swap x y D) = D.
Proof.
  unfold lvars_swap. apply swap_involutive.
Qed.

Lemma lvars_fv_open_subset k x (D : lvset) :
  lvars_fv (lvars_open k x D) ⊆ lvars_fv D ∪ {[x]}.
Proof.
  intros y Hy.
  rewrite lvars_fv_open in Hy.
  destruct (decide (k ∈ lvars_bv D)); set_solver.
Qed.

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

Lemma fv_subset_env_union_pair (X Y A B C D : aset) :
  A ⊆ X ∪ Y ∪ C →
  B ⊆ X ∪ Y ∪ D →
  X ∪ Y ∪ (A ∪ B) ⊆ X ∪ Y ∪ (C ∪ D).
Proof.
  set_solver.
Qed.

Ltac pick_fresh x s :=
  let a := fresh x in
  set (a := fresh_for s);
  assert (a ∉ s) by apply fresh_for_not_in.

#[global] Hint Unfold stale : class_simpl.
