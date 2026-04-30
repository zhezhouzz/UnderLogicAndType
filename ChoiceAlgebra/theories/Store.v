From ChoiceAlgebra Require Import Prelude MapFilterDom.

(** * Stores  (Definition 1.1)

    A store is a finite partial map from variables to values.
    We use stdpp's [gmap] which requires [Countable Var] and [EqDecision Value].

    We call these "stores" rather than "substitutions" to avoid name clashes
    with the locally-nameless substitution machinery in CoreLang. *)

Section Store.

Context `{Countable Var} `{EqDecision Value} `{Inhabited Value}.

(** ** Basic type *)

Definition Store : Type := gmap Var Value.

(** ** Compatibility and restriction *)

(** Two stores are compatible when they agree on their common domain. *)
Definition store_compat (s1 s2 : Store) : Prop :=
  ∀ x v1 v2, s1 !! x = Some v1 → s2 !! x = Some v2 → v1 = v2.

(** Restriction of a store to a finite set of variables. *)
Definition store_restrict (s : Store) (X : gset Var) : Store :=
  filter (λ '(k, _), k ∈ X) s.

(** ** Lemmas *)

Lemma store_compat_refl s : store_compat s s.
Proof.
  unfold store_compat. intros x v1 v2 H1 H2. hauto.
Qed.

Lemma store_compat_sym s1 s2 :
  store_compat s1 s2 → store_compat s2 s1.
Proof. unfold store_compat. intros Hc x v1 v2 H1 H2. hauto. Qed.

Lemma store_compat_union s1 s2 :
  store_compat s1 s2 →
  store_compat (s1 ∪ s2) (s1 ∪ s2).
Proof. unfold store_compat. intros Hc x v1 v2 H1 H2. hauto. Qed.

Lemma store_restrict_dom s X :
  dom (store_restrict s X) = dom s ∩ X.
Proof.
  unfold store_restrict. apply dom_gmap_filter_key_in_pair.
Qed.

Lemma store_restrict_idemp s X :
  dom s ⊆ X → store_restrict s X = s.
Proof.
  unfold store_restrict. intros Hsub. apply map_filter_id.
  intros i x Hx. apply elem_of_dom_2 in Hx. set_solver.
Qed.

Lemma store_restrict_restrict s X Y :
  store_restrict (store_restrict s X) Y = store_restrict s (X ∩ Y).
Proof.
  unfold store_restrict.
  setoid_rewrite map_filter_filter.
  apply map_filter_ext.
  intros i x Hx. apply elem_of_dom_2 in Hx. set_solver.
Qed.

Lemma store_union_dom s1 s2 :
  store_compat s1 s2 →
  dom (s1 ∪ s2) = dom s1 ∪ dom s2.
Proof.
  intros Hcomp. setoid_rewrite dom_union_L. auto.
Qed.

Lemma store_restrict_induce_disjoint s1 s2 :
  s1 ##ₘ (store_restrict s2 (dom s2 ∖ dom s1)) ∧
  s1 ∪ s2 = s1 ∪ (store_restrict s2 (dom s2 ∖ dom s1)).
Proof.
  pose (s2' := store_restrict s2 (dom s2 ∖ dom s1)).
  split.
  - rewrite map_disjoint_alt. intros i.
    destruct (decide (i ∈ dom s1)).
    + right.
      apply map_lookup_filter_None_2. right.
      intros x Hx Hi%elem_of_difference.
      destruct Hi as [_ Hi']. by apply Hi'.
    + left. by apply not_elem_of_dom.
  - apply map_eq. intros i.
    destruct (s1 !! i) as [x|] eqn:E1.
    + rewrite (lookup_union_l' s1 s2 i) by (by exists x; exact E1).
      rewrite (lookup_union_l' s1 s2' i) by (by exists x; exact E1).
      reflexivity.
    + rewrite (lookup_union_r s1 s2 i) by done.
      rewrite (lookup_union_r s1 s2' i) by done.
      destruct (s2 !! i) as [y|] eqn:E2.
      * etrans.
        -- exact E2.
        -- symmetry. unfold s2', store_restrict.
           apply map_lookup_filter_Some_2; first exact E2.
           apply elem_of_difference. split.
           ++ by apply elem_of_dom; exists y.
           ++ by apply not_elem_of_dom.
      * apply eq_trans with (@None Value); first exact E2.
        symmetry. unfold s2', store_restrict.
        apply map_lookup_filter_None. left. exact E2.
Qed.

Lemma store_restrict_union s1 s2 X :
  store_compat s1 s2 →
  store_restrict (s1 ∪ s2) X = store_restrict s1 X ∪ store_restrict s2 X.
Proof.
  intros Hcomp.
  unfold store_restrict.
  setoid_rewrite gmap_filter_key_pair.
  apply map_eq. intros i.
  rewrite option_eq. intros x.
  setoid_rewrite map_lookup_filter_Some.
  setoid_rewrite lookup_union_Some_raw.
  setoid_rewrite map_lookup_filter_Some.
  setoid_rewrite map_lookup_filter_None.
  simpl. split.
  - intros [[H1|[H1 H2]] HP].
    + left. eauto.
    + right. split. { left. exact H1. } eauto.
  - intros [[H1 HP]|[[H1|H1] [H2 HP]]].
    + split. { left. exact H1. } exact HP.
    + split. { right. eauto. } exact HP.
    + destruct (s1 !! i) as [y|] eqn:Ey.
      * exfalso. exact (H1 y Ey HP).
      * split. { right. eauto. } exact HP.
Qed.

Lemma store_restrict_lookup_some s X x y :
  store_restrict s X !! x = Some y → x ∈ X ∧ s !! x = Some y.
Proof.
  unfold store_restrict. intro Hlookup.
  apply map_lookup_filter_Some in Hlookup.
  destruct Hlookup as [H1 H2]. split; [exact H2 | exact H1].
Qed.

Lemma store_compat_restrict s1 s2 X :
  store_compat s1 s2 → store_compat (store_restrict s1 X) (store_restrict s2 X).
Proof.
  unfold store_compat. intros Hcomp x y z H2 H3.
  apply store_restrict_lookup_some in H2.
  apply store_restrict_lookup_some in H3.
  hauto.
Qed.

Lemma store_compat_restrict_eq s1 s2 :
  store_compat s1 s2 →
  dom s1 ⊆ dom s2 →
  store_restrict s2 (dom s1) = s1.
Proof.
  unfold store_compat. intros Hcomp Hsub.
  unfold store_restrict.
  apply map_eq. intros i.
  destruct (decide (i ∈ dom s1)) as [Hin|Hnin].
  - assert (i ∈ dom s2) as Hin2 by set_solver.
    pose (lookup_lookup_total_dom _ _ Hin) as Hlookup1.
    pose (lookup_lookup_total_dom _ _ Hin2) as Hlookup2.
    rewrite Hlookup1.
    rewrite map_lookup_filter_Some.
    split; eauto.
    rewrite (Hcomp i (s1 !!! i) (s2 !!! i)); eauto.
  - assert (s1 !! i = None) as Hnone by (by apply not_elem_of_dom).
    setoid_rewrite Hnone.
    rewrite map_lookup_filter_None. hauto.
Qed.

End Store.

#[global] Instance stale_store {A} : Stale (gmap atom A) := dom.
Arguments stale_store /.
