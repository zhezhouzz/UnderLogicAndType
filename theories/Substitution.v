From UnderLogicAndType Require Import Prelude MapFilterDom.

(** * Substitutions  (Definition 1.1)

    A substitution is a finite partial map from variables to values.
    We use stdpp's [gmap] which requires [Countable Var] and [EqDecision Value]. *)

Section Substitution.

Context `{Countable Var} `{EqDecision Value} `{Inhabited Value}.

(** ** Basic type *)

Definition Subst : Type := gmap Var Value.

(** ** Domain, compatibility, restriction *)

(** Domain: inherited directly from [gmap]. *)
Notation subst_dom σ := (dom σ).

(** Compatibility: two substitutions agree on their common domain. *)
Definition subst_compat (σ1 σ2 : Subst) : Prop :=
  ∀ x v1 v2, σ1 !! x = Some v1 → σ2 !! x = Some v2 → v1 = v2.

(** Restriction of σ to a finite set of variables X. *)
Definition subst_restrict (σ : Subst) (X : gset Var) : Subst :=
  filter (λ '(k, _), k ∈ X) σ.

(** ** Semijoin of a set of substitutions with a single substitution  (Definition 1.5)

    Given a set [m : Subst → Prop] and σ, the semijoin [semijoin_set m σ]
    collects all σ' ∈ m whose restriction to dom(σ) equals σ. *)
Definition semijoin_set (m : Subst → Prop) (σ : Subst) : Subst → Prop :=
  λ σ', m σ' ∧ subst_restrict σ' (dom σ) = σ.

(** ** Lemmas *)

Lemma subst_compat_refl σ : subst_compat σ σ.
Proof. 
  unfold subst_compat. intros x v1 v2 H1 H2. hauto.
Qed.

Lemma subst_compat_sym σ1 σ2 :
  subst_compat σ1 σ2 → subst_compat σ2 σ1.
Proof. intros Hcompat. unfold subst_compat in Hcompat |- *. intros x v1 v2 H1 H2. hauto. Qed.

Lemma subst_compat_union σ1 σ2 :
  subst_compat σ1 σ2 →
  subst_compat (σ1 ∪ σ2) (σ1 ∪ σ2).
Proof. intros Hc. unfold subst_compat in * |- *. intros x v1 v2 H1 H2. hauto. Qed.

Lemma subst_restrict_dom σ X :
  dom (subst_restrict σ X) = dom σ ∩ X.
Proof.
  unfold subst_restrict. apply dom_gmap_filter_key_in_pair.
Qed.

Lemma subst_restrict_idemp σ X :
  dom σ ⊆ X → subst_restrict σ X = σ.
Proof.
  unfold subst_restrict. intros Hsub. apply map_filter_id.
  intros i x Hx. apply elem_of_dom_2 in Hx. set_solver.
Qed.

Lemma subst_restrict_restrict σ X Y :
  subst_restrict (subst_restrict σ X) Y = subst_restrict σ (X ∩ Y).
Proof.
  unfold subst_restrict.
  setoid_rewrite map_filter_filter.
  apply map_filter_ext.
  intros i x Hx. apply elem_of_dom_2 in Hx. set_solver.
Qed.

Lemma subst_union_dom σ1 σ2 :
  subst_compat σ1 σ2 →
  dom (σ1 ∪ σ2) = dom σ1 ∪ dom σ2.
Proof.
  intros Hcomp.
  setoid_rewrite dom_union_L. auto.
Qed.

Lemma subst_restrict_induce_disjoint σ1 σ2 :
  σ1 ##ₘ (subst_restrict σ2 (dom σ2 ∖ dom σ1)) /\ σ1 ∪ σ2 = σ1 ∪ (subst_restrict σ2 (dom σ2 ∖ dom σ1)).
Proof.
  pose (σ2' := subst_restrict σ2 (dom σ2 ∖ dom σ1)).
  split.
  - rewrite map_disjoint_alt. intros i.
    destruct (decide (i ∈ dom σ1)).
    + right.
      apply map_lookup_filter_None_2. right.
      intros x Hx Hi%elem_of_difference.
      destruct Hi as [_ Hi']. by apply Hi'.
    + left. by apply not_elem_of_dom.
  - apply map_eq. intros i.
    destruct (σ1 !! i) as [x|] eqn:E1.
    + rewrite (lookup_union_l' σ1 σ2 i) by (by exists x; exact E1).
      rewrite (lookup_union_l' σ1 σ2' i) by (by exists x; exact E1).
      reflexivity.
    + rewrite (lookup_union_r σ1 σ2 i) by done.
      rewrite (lookup_union_r σ1 σ2' i) by done.
      destruct (σ2 !! i) as [y|] eqn:E2.
      * etrans.
        -- exact E2.
        -- symmetry. unfold σ2', subst_restrict.
           apply map_lookup_filter_Some_2; first exact E2.
           apply elem_of_difference. split.
           ++ by apply elem_of_dom; exists y.
           ++ by apply not_elem_of_dom.
      * apply eq_trans with (@None Value); first exact E2.
        symmetry. unfold σ2', subst_restrict.
        apply map_lookup_filter_None. left. exact E2.
Qed.

(** Restriction distributes over union of compatible substitutions. *)
Lemma subst_restrict_union σ1 σ2 X :
  subst_compat σ1 σ2 →
  subst_restrict (σ1 ∪ σ2) X = subst_restrict σ1 X ∪ subst_restrict σ2 X.
Proof.
  intros Hcomp.
  unfold subst_restrict.
  (* Use projection form of predicate to avoid pattern-match lambda issues *)
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
    + destruct (σ1 !! i) as [y|] eqn:Ey.
      * exfalso. exact (H1 y Ey HP).
      * split. { right. eauto. } exact HP.
Qed.

Lemma subst_restrict_lookup_some σ X x y :
  subst_restrict σ X !! x = Some y -> x ∈ X /\ σ !! x = Some y.
Proof.
  unfold subst_restrict. intro Hlookup.
  apply map_lookup_filter_Some in Hlookup.
  destruct Hlookup as [H1 H2]. split; [exact H2 | exact H1].
Qed.

(** Compatibility is preserved under restriction. *)
Lemma subst_compat_restrict σ1 σ2 X :
  subst_compat σ1 σ2 → subst_compat (subst_restrict σ1 X) (subst_restrict σ2 X).
Proof.
  unfold subst_compat. intros Hcomp. 
  intros x y z H2 H3.
  apply subst_restrict_lookup_some in H2.
  apply subst_restrict_lookup_some in H3.
  hauto.
Qed.

(** If σ1 ↑ σ2 and dom(σ1) ⊆ dom(σ2), then σ1 = σ2|_{dom(σ1)}. *)
Lemma subst_compat_restrict_eq σ1 σ2 :
  subst_compat σ1 σ2 →
  dom σ1 ⊆ dom σ2 →
  subst_restrict σ2 (dom σ1) = σ1.
Proof.
  unfold subst_compat. intros Hcomp. intros Hsub.
  unfold subst_restrict.
  apply map_eq. intros i.
  destruct (decide (i ∈ subst_dom σ1)) as [Hin|Hnin]; subst.
  - assert (i ∈ subst_dom σ2) as Hin2 by set_solver.
    pose (lookup_lookup_total_dom _ _ Hin) as Hlookup1.
    pose (lookup_lookup_total_dom _ _ Hin2) as Hlookup2.
    rewrite Hlookup1.
    rewrite map_lookup_filter_Some.
    split; eauto.
    rewrite (Hcomp i (σ1 !!! i) (σ2 !!! i)); eauto.
  - assert (σ1 !! i = None) as Hnone by (by apply not_elem_of_dom).
    setoid_rewrite Hnone.
    rewrite map_lookup_filter_None. hauto.
Qed.

End Substitution.

(** Typeclass arguments from the Section are already maximally implicit;
    no Global Arguments override needed. *)
