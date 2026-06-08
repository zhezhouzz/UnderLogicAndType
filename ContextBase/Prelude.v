(** * ContextBase.Prelude

    Shared base infrastructure: stdpp exports, atoms, swaps, key shifts,
    finite-map helpers, value signatures, and freshness utilities. *)

From ContextBase.Swap Require Export SetSwap.
From Corelib Require Export Program.Wf.
From Stdlib Require Export Lia.


Definition atom : Type := positive.
#[global] Instance atom_eqdec     : EqDecision atom := _.
#[global] Instance atom_countable : Countable  atom := _.
#[global] Instance atom_infinite  : Infinite   atom := _.
Notation aset := (gset atom).

(** Free-variable/resource-domain collection. *)
Class Stale A := stale : A → aset.

#[global] Instance stale_aset : Stale aset := id.

Notation "'FV' '(' x ')'" := (stale x)
  (at level 10, x at level 9,
   format "FV ( x )").

Notation "x '#' s" := (x ∉ stale s) (at level 40).

(** Binder-depth shift.  This is the shift-side analogue of the generic
    [Open] interface used by locally-nameless syntax. *)
Class Shift A := shift_from : nat → A → A.

Notation "'↑{' k '}' x" := (shift_from k x)
  (at level 20, k constr, x at level 20,
   format "↑{ k }  x").

Notation "x '↑'" := (shift_from 0 x)
  (at level 20,
   format "x  ↑").


(** ** Generic key shifts *)

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

Lemma map_delete_insert_same (m : gmap K A) k v :
  delete k (<[k := v]> m) = delete k m.
Proof.
  apply map_eq. intros i.
  destruct (decide (i = k)) as [->|Hik].
  - rewrite !lookup_delete_eq. reflexivity.
  - rewrite !lookup_delete_ne by congruence.
    rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma map_delete_insert_ne (m : gmap K A) i k v :
  i ≠ k →
  delete i (<[k := v]> m) = <[k := v]> (delete i m).
Proof.
  intros Hik. apply map_eq. intros j.
  destruct (decide (j = i)) as [->|Hji].
  - rewrite lookup_delete_eq.
    rewrite lookup_insert_ne by congruence.
    rewrite lookup_delete_eq. reflexivity.
  - rewrite !lookup_delete_ne by congruence.
    destruct (decide (j = k)) as [->|Hjk].
    + rewrite !lookup_insert_eq. reflexivity.
    + rewrite !lookup_insert_ne by congruence.
      rewrite lookup_delete_ne by congruence. reflexivity.
Qed.

Lemma map_fold_ext_on_lookup
    {B : Type} (f g : K -> A -> B -> B) (b : B) (m : gmap K A) :
  (forall i x, m !! i = Some x -> forall acc, f i x acc = g i x acc) ->
  map_fold f b m = map_fold g b m.
Proof.
  intros Hext.
  rewrite !map_fold_foldr.
  assert (Haux : forall l,
    (forall i x, (i, x) ∈ l -> m !! i = Some x) ->
    foldr (uncurry f) b l = foldr (uncurry g) b l).
  {
    induction l as [|[i x] l IH]; intros Hl; simpl; [reflexivity|].
    rewrite Hext by (apply Hl; left; reflexivity).
    f_equal. apply IH. intros j y Hjy.
    apply Hl. right. exact Hjy.
  }
  apply Haux. intros i x Hin.
  rewrite <- elem_of_map_to_list. exact Hin.
Qed.

Lemma map_restrict_dom m X :
  dom (map_restrict m X) = dom m ∩ X.
Proof.
  unfold map_restrict. apply dom_gmap_filter_key_in_pair.
Qed.

Lemma map_restrict_lookup (m : gmap K A) X x :
  map_restrict m X !! x =
  if decide (x ∈ X) then m !! x else None.
Proof.
  unfold map_restrict.
  destruct (decide (x ∈ X)) as [Hx|Hx].
  - destruct (m !! x) eqn:Hm.
    + apply map_lookup_filter_Some_2; [exact Hm | exact Hx].
    + apply map_lookup_filter_None. left. exact Hm.
  - apply map_lookup_filter_None. right. intros v _ Hin. exact (Hx Hin).
Qed.

Lemma map_restrict_idemp m X :
  dom m ⊆ X → map_restrict m X = m.
Proof.
  unfold map_restrict. intros Hsub. apply map_filter_id.
  intros i x Hx. apply map_elem_of_dom_lookup_some in Hx.
  better_set_solver.
Qed.

Lemma map_restrict_restrict m X Y :
  map_restrict (map_restrict m X) Y = map_restrict m (X ∩ Y).
Proof.
  unfold map_restrict.
  setoid_rewrite map_filter_filter.
  apply map_filter_ext.
  intros i x Hx. apply map_elem_of_dom_lookup_some in Hx.
  better_set_solver.
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

(** ** Abstract store values

    The algebraic layers quantify over store values abstractly.  The
    Context type layer later instantiates this interface with CoreLang [value]s. *)
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
