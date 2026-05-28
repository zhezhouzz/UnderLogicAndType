(** * ContextBase.Prelude

    Top-level shared infrastructure for the concrete development.  This file
    deliberately sits below both CoreLang and ContextAlgebra: it provides the
    global atom type, finite atom sets, an abstract value interface, freshness
    helpers, and the [Stale] interface used by all later layers. *)

From ContextBase.Swap Require Export Atom.

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

Lemma fv_subset_env_union_pair (X Y A B C D : aset) :
  A ⊆ X ∪ Y ∪ C →
  B ⊆ X ∪ Y ∪ D →
  X ∪ Y ∪ (A ∪ B) ⊆ X ∪ Y ∪ (C ∪ D).
Proof.
  better_set_solver.
Qed.

Ltac pick_fresh x s :=
  let a := fresh x in
  set (a := fresh_for s);
  assert (a ∉ s) by apply fresh_for_not_in.

#[global] Hint Unfold stale : class_simpl.
