(** * Concrete store lookup and swap interface lemmas *)

From ContextBase Require Import Prelude LogicVar.
From ContextStore Require Import StoreCore StoreKeyAction StoreRestrictCore StoreRestrictUnion StoreBind.
From ContextStore Require Export StoreInterfaceCore.

Section StoreInterface.

Context {V : Type} `{ValueSig V}.

Local Notation Store := (@StoreA V atom _ _) (only parsing).
Local Notation LStore := (@StoreA V logic_var _ _) (only parsing).

Lemma store_lookup_none_of_not_elem_dom (s : Store) x :
  x ∉ dom s →
  s !! x = None.
Proof.
  apply storeA_lookup_none_of_not_elem_dom.
Qed.

Lemma store_lookup_union_Some_raw (s1 s2 : Store) i v :
  ((@union (gmap atom V) _ (s1 : gmap atom V) (s2 : gmap atom V)) !! i = Some v) ↔
    s1 !! i = Some v ∨ (s1 !! i = None ∧ s2 !! i = Some v).
Proof.
  apply storeA_lookup_union_Some_raw.
Qed.

Lemma lstore_swap_fresh (a b : logic_var) (s : LStore) :
  a ∉ dom (s : LStore) ->
  b ∉ dom (s : LStore) ->
  lstore_swap a b s = s.
Proof.
  intros Ha Hb.
  unfold lstore_swap, lstore_rekey.
  change (@storeA_swap V logic_var _ _ a b s = s).
  apply storeA_swap_fresh; assumption.
Qed.

Lemma lstore_swap_commute_fresh
    (a b c d : logic_var) (s : LStore) :
  c <> a ->
  c <> b ->
  d <> a ->
  d <> b ->
  lstore_swap a b (lstore_swap c d s) =
  lstore_swap c d (lstore_swap a b s).
Proof.
  intros Hca Hcb Hda Hdb.
  unfold lstore_swap, lstore_rekey.
  change (@storeA_swap V logic_var _ _ a b
      (@storeA_swap V logic_var _ _ c d s) =
    @storeA_swap V logic_var _ _ c d
      (@storeA_swap V logic_var _ _ a b s)).
  rewrite storeA_swap_conjugate.
  replace (swap a b c) with c by (symmetry; apply swap_fresh; congruence).
  replace (swap a b d) with d by (symmetry; apply swap_fresh; congruence).
  reflexivity.
Qed.

End StoreInterface.
