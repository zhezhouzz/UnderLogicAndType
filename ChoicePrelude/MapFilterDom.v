(** * Reusable lemmas: [dom] vs [filter] on finite maps *)

From ChoicePrelude Require Export Prelude.
From stdpp Require Export fin_maps.

Section dom_gmap_filter.
  Context `{Countable K} `{EqDecision A}.

  Lemma dom_gmap_filter_key_in (m : gmap K A) (X : gset K) :
    dom (filter (λ kv : K * A, kv.1 ∈ X) m) = dom m ∩ X.
  Proof.
    apply leibniz_equiv_iff. intros i.
    rewrite elem_of_intersection, !elem_of_dom.
    unfold is_Some.
    setoid_rewrite map_lookup_filter_Some.
    naive_solver.
  Qed.

  Lemma gmap_filter_key_pair (m : gmap K A) (X : gset K) :
    filter (λ '(k, _), k ∈ X) m = filter (λ kv : K * A, kv.1 ∈ X) m.
  Proof.
    apply map_filter_strong_ext_1.
    intros i x. split; intros [H1 H2]; split; naive_solver.
  Qed.

  Corollary dom_gmap_filter_key_in_pair (m : gmap K A) (X : gset K) :
    dom (filter (λ '(k, _), k ∈ X) m) = dom m ∩ X.
  Proof.
    rewrite (f_equal dom (gmap_filter_key_pair m X)).
    apply dom_gmap_filter_key_in.
  Qed.

End dom_gmap_filter.
