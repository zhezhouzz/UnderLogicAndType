(** * Generic stores: core definitions *)

From ChoicePrelude Require Export Prelude.

Section AbstractStoreCore.

Context {V : Type} `{ValueSig V}.

Definition StoreA (K : Type) `{Countable K} : Type := gmap K V.

Typeclasses Transparent StoreA.

Definition storeA_compat {K : Type} `{Countable K}
    (s1 s2 : StoreA K) : Prop :=
  map_compat V s1 s2.

Definition storeA_restrict {K : Type} `{Countable K}
    (s : StoreA K) (X : gset K) : StoreA K :=
  map_restrict V s X.

Definition storeA_swap {K : Type} `{Countable K} `{!SwapKey K}
    (x y : K) (s : StoreA K) : StoreA K :=
  kmap (key_swap x y) s.

Definition storeA_shift {K : Type} `{Countable K} `{!ShiftKey K}
    (k : nat) (s : StoreA K) : StoreA K :=
  kmap (key_shift k) s.

Definition storeA_bind {K : Type} `{Countable K}
    (s1 s2 s : StoreA K) : Prop :=
  dom s1 ## dom s2 ∧ s = @union (gmap K V) _ s1 s2.

Lemma storeA_map_eq {K : Type} `{Countable K} (s1 s2 : StoreA K) :
  (∀ x, s1 !! x = s2 !! x) →
  s1 = s2.
Proof.
  intros Hlook. apply (map_eq (M:=gmap K)). exact Hlook.
Qed.

Lemma storeA_elem_of_dom_lookup_some {K : Type} `{Countable K}
    (s : StoreA K) x v :
  s !! x = Some v →
  x ∈ dom s.
Proof.
  intros Hlook.
  change ((s : gmap K V) !! x = Some v) in Hlook.
  change (x ∈ dom (s : gmap K V)).
  by apply elem_of_dom_2 in Hlook.
Qed.

Lemma storeA_lookup_none_of_not_elem_dom {K : Type} `{Countable K}
    (s : StoreA K) x :
  x ∉ dom s →
  s !! x = None.
Proof.
  intros Hnot.
  destruct (s !! x) as [v|] eqn:Hlook; [| reflexivity].
  exfalso. apply Hnot. by eapply storeA_elem_of_dom_lookup_some.
Qed.

Lemma storeA_lookup_insert_ne {K : Type} `{Countable K}
    (s : StoreA K) x z v :
  z ≠ x →
  <[x := v]> s !! z = s !! z.
Proof.
  intros Hzx. apply (lookup_insert_ne (M:=gmap K) (A:=V)). done.
Qed.

Lemma storeA_lookup_union_Some_raw {K : Type} `{Countable K}
    (s1 s2 : StoreA K) i v :
  ((@union (gmap K V) _ s1 s2) !! i = Some v) ↔
    s1 !! i = Some v ∨ (s1 !! i = None ∧ s2 !! i = Some v).
Proof.
  apply (lookup_union_Some_raw (M:=gmap K) (A:=V)).
Qed.

Lemma storeA_bind_dom {K : Type} `{Countable K}
    (s1 s2 s : StoreA K) :
  storeA_bind s1 s2 s →
  dom s = dom s1 ∪ dom s2.
Proof.
  intros [_ ->].
  change (dom (@union (gmap K V) _ (s1 : gmap K V) (s2 : gmap K V)) =
    dom (s1 : gmap K V) ∪ dom (s2 : gmap K V)).
  apply dom_union_L.
Qed.

Lemma storeA_lookup_none_of_dom {K : Type} `{Countable K}
    (σ : StoreA K) (X : gset K) (x : K) :
  dom (σ : gmap K V) = X →
  x ∉ X →
  (σ : gmap K V) !! x = None.
Proof.
  intros Hdom Hx.
  destruct ((σ : gmap K V) !! x) as [v|] eqn:Hlookup; [| reflexivity].
  exfalso. apply Hx.
  rewrite <- Hdom. by apply elem_of_dom_2 in Hlookup.
Qed.

End AbstractStoreCore.
