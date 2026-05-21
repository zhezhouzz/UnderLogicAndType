(** * Generic stores: key actions *)

From ChoicePrelude Require Export StoreCore.

Section AbstractStoreKeyAction.

Context {V : Type} `{ValueSig V}.

Lemma storeA_swap_lookup {K : Type} `{Countable K} `{!SwapKey K}
    (x y : K) (s : StoreA K) (z : K) :
  ((storeA_swap x y s : gmap K V) !! key_swap x y z) =
  ((s : gmap K V) !! z).
Proof.
  unfold storeA_swap.
  change (kmap (M2:=gmap K) (key_swap x y) s !! key_swap x y z = s !! z).
  pose proof (key_swap_inj x y) as Hinj.
  rewrite (lookup_kmap (M1:=gmap K) (M2:=gmap K)
    (Inj0:=Hinj) (key_swap x y) s z).
  reflexivity.
Qed.

Lemma storeA_swap_lookup_inv {K : Type} `{Countable K} `{!SwapKey K}
    (x y : K) (s : StoreA K) (z : K) :
  ((storeA_swap x y s : gmap K V) !! z) =
  ((s : gmap K V) !! key_swap x y z).
Proof.
  rewrite <- (key_swap_involutive x y z) at 1.
  apply storeA_swap_lookup.
Qed.

Lemma storeA_swap_dom {K : Type} `{Countable K} `{!SwapKey K}
    (x y : K) (s : StoreA K) :
  dom (@storeA_swap V K _ _ _ x y s) = gset_swap x y (dom s).
Proof.
  unfold storeA_swap, gset_swap.
  change (dom (kmap (M2:=gmap K) (key_swap x y) s) =
    set_map (key_swap x y) (dom s)).
  pose proof (key_swap_inj x y) as Hinj.
  rewrite (dom_kmap_L (M:=gmap K) (M2:=gmap K)
    (Inj0:=Hinj) (key_swap x y) s).
  reflexivity.
Qed.

Lemma storeA_swap_delete {K : Type} `{Countable K} `{!SwapKey K}
    (x y z : K) (s : StoreA K) :
  storeA_swap x y (delete z s) =
  delete (key_swap x y z) (storeA_swap x y s : gmap K V).
Proof.
  unfold storeA_swap.
  change (kmap (M2:=gmap K) (key_swap x y) (delete z (s : gmap K V)) =
    delete (key_swap x y z)
      (kmap (M2:=gmap K) (key_swap x y) (s : gmap K V))).
  refine (@kmap_delete K (gmap K) _ _ _ _ _ _ _ _ _
    K (gmap K) _ _ _ _ _ _ _ _ _
    (key_swap x y) _ V (s : gmap K V) z).
  apply key_swap_inj.
Qed.

Lemma storeA_swap_insert {K : Type} `{Countable K} `{!SwapKey K}
    (x y z : K) (v : V) (s : StoreA K) :
  storeA_swap x y (<[z := v]> s) =
  <[key_swap x y z := v]> (storeA_swap x y s : gmap K V).
Proof.
  unfold storeA_swap.
  change (kmap (key_swap x y) (<[z := v]> (s : gmap K V)) =
    (<[key_swap x y z := v]>
      (kmap (key_swap x y) (s : gmap K V)) : gmap K V)).
  refine (@kmap_insert K (gmap K) _ _ _ _ _ _ _ _ _
    K (gmap K) _ _ _ _ _ _ _ _ _
    (key_swap x y) _ V (s : gmap K V) z v).
  apply key_swap_inj.
Qed.

Lemma storeA_swap_union {K : Type} `{Countable K} `{!SwapKey K}
    (x y : K) (s1 s2 : StoreA K) :
  storeA_swap x y (@union (gmap K V) _ s1 s2) =
  @union (gmap K V) _ (storeA_swap x y s1 : gmap K V) (storeA_swap x y s2 : gmap K V).
Proof.
  unfold storeA_swap.
  change (kmap (key_swap x y) (@union (gmap K V) _ (s1 : gmap K V) (s2 : gmap K V)) =
    @union (gmap K V) _
      (kmap (key_swap x y) (s1 : gmap K V))
      (kmap (key_swap x y) (s2 : gmap K V))).
  refine (@kmap_union K (gmap K) _ _ _ _ _ _ _ _ _
    K (gmap K) _ _ _ _ _ _ _ _ _
    (key_swap x y) _ V (s1 : gmap K V) (s2 : gmap K V)).
  apply key_swap_inj.
Qed.

Lemma storeA_shift_lookup {K : Type} `{Countable K} `{!ShiftKey K}
    (k : nat) (s : StoreA K) (z : K) :
  ((storeA_shift k s : gmap K V) !! key_shift k z) =
  ((s : gmap K V) !! z).
Proof.
  unfold storeA_shift.
  rewrite (lookup_kmap (M1:=gmap K) (M2:=gmap K)
    (Inj0:=key_shift_inj k) (key_shift k) s z).
  reflexivity.
Qed.

Lemma storeA_shift_dom {K : Type} `{Countable K} `{!ShiftKey K}
    (k : nat) (s : StoreA K) :
  dom (@storeA_shift V K _ _ _ k s) = set_map (key_shift k) (dom s).
Proof.
  unfold storeA_shift.
  change (dom (kmap (M2:=gmap K) (key_shift k) (s : gmap K V)) =
    set_map (key_shift k) (dom (s : gmap K V))).
  rewrite (dom_kmap_L (M:=gmap K) (M2:=gmap K)
    (Inj0:=key_shift_inj k) (key_shift k) (s : gmap K V)).
  reflexivity.
Qed.

Lemma storeA_shift_empty {K : Type} `{Countable K} `{!ShiftKey K} k :
  storeA_shift k (∅ : StoreA K) = (∅ : gmap K V).
Proof.
  unfold storeA_shift.
  change (kmap (M2:=gmap K) (key_shift k) (∅ : gmap K V) =
    (∅ : gmap K V)).
  apply kmap_empty.
Qed.

Lemma storeA_shift_insert {K : Type} `{Countable K} `{!ShiftKey K}
    k z v (s : StoreA K) :
  storeA_shift k (<[z := v]> s) =
  <[key_shift k z := v]> (storeA_shift k s : gmap K V).
Proof.
  unfold storeA_shift.
  rewrite (kmap_insert (M1:=gmap K) (M2:=gmap K)
    (key_shift k) (Inj0:=key_shift_inj k) (A:=V) s z v).
  reflexivity.
Qed.

Lemma storeA_shift_union {K : Type} `{Countable K} `{!ShiftKey K}
    k (s1 s2 : StoreA K) :
  storeA_shift k (@union (gmap K V) _ (s1 : gmap K V) (s2 : gmap K V)) =
  (storeA_shift k s1 : gmap K V) ∪ (storeA_shift k s2 : gmap K V).
Proof.
  unfold storeA_shift.
  rewrite (kmap_union (M1:=gmap K) (M2:=gmap K)
    (key_shift k) (Inj0:=key_shift_inj k) (A:=V) s1 s2).
  reflexivity.
Qed.

End AbstractStoreKeyAction.
