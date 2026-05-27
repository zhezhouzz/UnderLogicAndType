(** * Generic stores: core definitions *)

From ContextPrelude Require Import Prelude.
From Stdlib Require Import Logic.ProofIrrelevance.

Section AbstractStoreCore.

Context {V : Type} `{ValueSig V}.

Definition StoreA (K : Type) `{Countable K} : Type := gmap K V.

Typeclasses Transparent StoreA.

Record StoreAOn {K : Type} `{Countable K} (D : gset K) : Type := {
  storeAO_store : StoreA K;
  storeAO_dom : dom (storeAO_store : StoreA K) = D;
}.

Local Arguments storeAO_store {_ _ _ _} _.
Local Arguments storeAO_dom {_ _ _ _} _.

Definition storeA_on_ext {K : Type} `{Countable K} (D : gset K)
    (s1 s2 : StoreAOn D) :
  storeAO_store s1 = storeAO_store s2 ->
  s1 = s2.
Proof.
  destruct s1 as [s1 H1], s2 as [s2 H2]. simpl.
  intros ->. f_equal. apply proof_irrelevance.
Qed.

Definition storeA_compat {K : Type} `{Countable K}
    (s1 s2 : StoreA K) : Prop :=
  map_compat V s1 s2.

Definition storeA_agree_on {K : Type} `{Countable K}
    (D : gset K) (s1 s2 : StoreA K) : Prop :=
  forall x, x ∈ D -> s1 !! x = s2 !! x.

Definition storeA_restrict {K : Type} `{Countable K}
    (s : StoreA K) (X : gset K) : StoreA K :=
  map_restrict V s X.

Definition storeA_rekey {K : Type} `{Countable K}
    (f : K → K) (s : StoreA K) : StoreA K :=
  kmap f s.

Definition storeA_map_key
    {K K' : Type} `{Countable K} `{Countable K'}
    (f : K → K') (s : StoreA K) : StoreA K' :=
  kmap f s.

Definition storeA_swap {K : Type} `{Countable K} `{!SwapKey K}
    (x y : K) (s : StoreA K) : StoreA K :=
  storeA_rekey (key_swap x y) s.

Definition storeA_shift {K : Type} `{Countable K} `{!ShiftKey K}
    (k : nat) (s : StoreA K) : StoreA K :=
  storeA_rekey (key_shift k) s.

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

Lemma storeA_lookup_insert {K : Type} `{Countable K}
    (s : StoreA K) x v :
  <[x := v]> s !! x = Some v.
Proof.
  change (((<[x := v]> (s : gmap K V)) : gmap K V) !! x = Some v).
  rewrite lookup_insert. destruct (decide (x = x)); congruence.
Qed.

Lemma storeA_agree_on_mono {K : Type} `{Countable K}
    D E (s1 s2 : StoreA K) :
  D ⊆ E ->
  storeA_agree_on E s1 s2 ->
  storeA_agree_on D s1 s2.
Proof.
  intros Hsub Hag x Hx. apply Hag, Hsub, Hx.
Qed.

Lemma storeA_agree_on_refl {K : Type} `{Countable K}
    D (s : StoreA K) :
  storeA_agree_on D s s.
Proof.
  intros x Hx. reflexivity.
Qed.

Lemma storeA_agree_on_sym {K : Type} `{Countable K}
    D (s1 s2 : StoreA K) :
  storeA_agree_on D s1 s2 ->
  storeA_agree_on D s2 s1.
Proof.
  intros Hag x Hx. symmetry. apply Hag, Hx.
Qed.

Lemma storeA_agree_on_union {K : Type} `{Countable K}
    D1 D2 (s1 s2 : StoreA K) :
  storeA_agree_on D1 s1 s2 ->
  storeA_agree_on D2 s1 s2 ->
  storeA_agree_on (D1 ∪ D2) s1 s2.
Proof.
  intros H1 H2 x Hx.
  apply elem_of_union in Hx as [Hx|Hx]; [apply H1|apply H2]; exact Hx.
Qed.

Lemma storeA_agree_on_insert_same {K : Type} `{Countable K}
    D (s1 s2 : StoreA K) x v :
  storeA_agree_on (D ∖ {[x]}) s1 s2 ->
  storeA_agree_on D (<[x := v]> s1) (<[x := v]> s2).
Proof.
  intros Hag y Hy.
  destruct (decide (y = x)) as [->|Hyx].
  - change ((<[x := v]> (s1 : gmap K V) !! x) =
      (<[x := v]> (s2 : gmap K V) !! x)).
    rewrite !lookup_insert. destruct (decide (x = x)); congruence.
  - change ((<[x := v]> (s1 : gmap K V) !! y) =
      (<[x := v]> (s2 : gmap K V) !! y)).
    rewrite !lookup_insert_ne by congruence.
    apply Hag. apply elem_of_difference. split; [exact Hy|set_solver].
Qed.

Lemma storeA_agree_on_insert_same_keep {K : Type} `{Countable K}
    D (s1 s2 : StoreA K) x v :
  storeA_agree_on D s1 s2 ->
  storeA_agree_on (D ∪ {[x]}) (<[x := v]> s1) (<[x := v]> s2).
Proof.
  intros Hag.
  apply storeA_agree_on_union.
  - intros y Hy.
    destruct (decide (y = x)) as [->|Hyx].
    + change ((<[x := v]> (s1 : gmap K V) !! x) =
        (<[x := v]> (s2 : gmap K V) !! x)).
      rewrite !lookup_insert. destruct (decide (x = x)); congruence.
    + change ((<[x := v]> (s1 : gmap K V) !! y) =
        (<[x := v]> (s2 : gmap K V) !! y)).
      rewrite !lookup_insert_ne by congruence. apply Hag, Hy.
  - intros y Hy.
    rewrite elem_of_singleton in Hy. subst y.
    change ((<[x := v]> (s1 : gmap K V) !! x) =
      (<[x := v]> (s2 : gmap K V) !! x)).
    rewrite !lookup_insert. destruct (decide (x = x)); congruence.
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

Arguments storeAO_store {_ _ _ _ _} _.
Arguments storeAO_dom {_ _ _ _ _} _.
