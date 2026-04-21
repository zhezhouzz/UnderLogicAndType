(** * Reusable lemmas: [dom] vs [filter] on finite maps (stdpp [gmap])

    Moral proof pattern for "domain of a key-restricted submap":
    - relate lookups with [map_lookup_filter_Some];
    - then set extensionality ([leibniz_equiv_iff] + [elem_of_intersection] + …).

    For predicates written as [λ '(k,_), k ∈ X], use [dom_gmap_filter_key_in_pair]
    (built from [gmap_filter_key_pair] + [dom_gmap_filter_key_in]). *)

From UnderLogicAndType Require Export Prelude.
From stdpp Require Export fin_maps.

Section dom_gmap_filter.
  Context `{Countable K} `{EqDecision A}.

  (** Keys of the sub-map that keeps only bindings whose key lies in [X].

      Proof idea: set extensionality; an index is in [dom (filter P m)] iff
      [map_lookup_filter_Some] gives a witness in [m] satisfying [P]. *)
  Lemma dom_gmap_filter_key_in (m : gmap K A) (X : gset K) :
    dom (filter (λ kv : K * A, kv.1 ∈ X) m) = dom m ∩ X.
  Proof.
    apply leibniz_equiv_iff. intros i.
    rewrite elem_of_intersection, !elem_of_dom.
    unfold is_Some.
    setoid_rewrite map_lookup_filter_Some.
    naive_solver.
  Qed.

  (** [filter (λ '(k,_), k ∈ X)] is the same map as the [filter_dom_L]-friendly shape
      [(λ kv, kv.1 ∈ X)] (so [rewrite] with [filter_dom_L] sees the right head). *)
  Lemma gmap_filter_key_pair (m : gmap K A) (X : gset K) :
    filter (λ '(k, _), k ∈ X) m = filter (λ kv : K * A, kv.1 ∈ X) m.
  Proof.
    apply map_filter_strong_ext_1.
    intros i x. split; intros [H1 H2]; split; naive_solver.
  Qed.

  (** Convenient packaging for the common [λ '(k, _), k ∈ X] style (e.g. [subst_restrict]). *)
  Corollary dom_gmap_filter_key_in_pair (m : gmap K A) (X : gset K) :
    dom (filter (λ '(k, _), k ∈ X) m) = dom m ∩ X.
  Proof.
    rewrite (f_equal dom (gmap_filter_key_pair m X)).
    apply dom_gmap_filter_key_in.
  Qed.

End dom_gmap_filter.
