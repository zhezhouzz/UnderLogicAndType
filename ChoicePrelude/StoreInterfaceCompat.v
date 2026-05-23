(** * Concrete store compatibility interface lemmas *)

From ChoicePrelude Require Import Prelude StoreCore StoreKeyAction StoreRestrict StoreBind.
From ChoicePrelude Require Export StoreInterfaceRestrict.

Section StoreInterface.

Context {V : Type} `{ValueSig V}.

Local Notation Store := (@StoreA V atom _ _) (only parsing).
Local Notation LStore := (@StoreA V logic_var _ _) (only parsing).

Lemma store_compat_refl (s : Store) : store_compat s s.
Proof.
  apply storeA_compat_refl.
Qed.

Lemma store_compat_sym (s1 s2 : Store) :
  store_compat s1 s2 → store_compat s2 s1.
Proof.
  apply storeA_compat_sym.
Qed.

Lemma store_compat_swap (x y : atom) (s1 s2 : Store) :
  store_compat (store_swap x y s1) (store_swap x y s2) ↔
  store_compat s1 s2.
Proof. apply storeA_compat_swap. Qed.

Lemma store_compat_union_inv_l (s1 s2 s3 : Store) :
  store_compat (s1 ∪ s2) s3 →
  store_compat s1 s3.
Proof. apply storeA_compat_union_inv_l. Qed.

Lemma store_compat_union_inv_r (s1 s2 s3 : Store) :
  store_compat s1 s2 →
  store_compat (s1 ∪ s2) s3 →
  store_compat s2 s3.
Proof. apply storeA_compat_union_inv_r. Qed.

Lemma store_compat_union_intro_r (s1 s2 s3 : Store) :
  store_compat s1 s2 →
  store_compat s1 s3 →
  store_compat s1 (s2 ∪ s3).
Proof. apply storeA_compat_union_intro_r. Qed.

Lemma store_union_comm (s1 s2 : Store) :
  store_compat s1 s2 →
  s1 ∪ s2 = s2 ∪ s1.
Proof. apply storeA_union_comm. Qed.

Lemma store_union_absorb_l (s1 s2 : Store) :
  store_compat s1 s2 →
  dom s2 ⊆ dom s1 →
  s1 ∪ s2 = s1.
Proof. apply storeA_union_absorb_l. Qed.

Lemma store_union_absorb_r (s1 s2 : Store) :
  store_compat s1 s2 →
  dom s1 ⊆ dom s2 →
  s1 ∪ s2 = s2.
Proof. apply storeA_union_absorb_r. Qed.

Lemma store_compat_insert_l_fresh (s1 s2 : Store) (x : atom) (v : V) :
  store_compat s1 s2 →
  x ∉ dom s2 →
  store_compat (<[x := v]> (s1 : gmap atom V)) s2.
Proof. apply storeA_compat_insert_l_fresh. Qed.

Lemma store_compat_insert_r_fresh (s1 s2 : Store) (x : atom) (v : V) :
  store_compat s1 s2 →
  x ∉ dom s1 →
  store_compat s1 (<[x := v]> (s2 : gmap atom V)).
Proof. apply storeA_compat_insert_r_fresh. Qed.

Lemma store_insert_union_l (s1 s2 : Store) (x : atom) (v : V) :
  (<[x := v]> s1 : gmap atom V) ∪ s2 = <[x := v]> (s1 ∪ s2).
Proof. apply storeA_insert_union_l. Qed.

Lemma store_insert_union_l_fresh (s1 s2 : Store) (x : atom) (v : V) :
  x ∉ dom s2 →
  (<[x := v]> s1 : gmap atom V) ∪ s2 = <[x := v]> (s1 ∪ s2).
Proof. apply storeA_insert_union_l_fresh. Qed.

Lemma store_insert_union_r_fresh (s1 s2 : Store) (x : atom) (v : V) :
  x ∉ dom s1 →
  s1 ∪ (<[x := v]> s2 : gmap atom V) = <[x := v]> (s1 ∪ s2).
Proof. apply storeA_insert_union_r_fresh. Qed.

Lemma store_union_singleton_insert_fresh (σ : Store) (x : atom) (v : V) :
  x ∉ dom σ →
  σ ∪ ({[x := v]} : Store) = <[x := v]> σ.
Proof. apply storeA_union_singleton_insert_fresh. Qed.

Lemma store_union_dom (s1 s2 : Store) :
  store_compat s1 s2 →
  dom (s1 ∪ s2) = dom s1 ∪ dom s2.
Proof. apply storeA_union_dom. Qed.

Lemma disj_dom_store_compat (s1 s2 : Store) :
  dom s1 ∩ dom s2 = ∅ → store_compat s1 s2.
Proof. apply storeA_disj_dom_compat. Qed.

Lemma store_compat_restrict_singleton_fresh (s1 s2 : Store) (y : atom) :
  y ∉ dom s1 →
  store_compat s1 (store_restrict s2 {[y]}).
Proof. apply storeA_compat_restrict_singleton_fresh. Qed.

Lemma store_compat_restrict (s1 s2 : Store) (X : aset) :
  store_compat s1 s2 →
  store_compat (store_restrict s1 X) (store_restrict s2 X).
Proof. apply storeA_compat_restrict. Qed.

Lemma store_compat_restrict_r (s1 s2 : Store) (X : aset) :
  store_compat s1 s2 → store_compat s1 (store_restrict s2 X).
Proof. apply storeA_compat_restrict_r. Qed.

Lemma store_compat_restrict_l_full_r (s1 s2 : Store) (X : aset) :
  dom s1 ⊆ X →
  store_compat s1 (store_restrict s2 X) →
  store_compat s1 s2.
Proof. apply storeA_compat_restrict_l_full_r. Qed.

Lemma store_compat_restrict_eq (s1 s2 : Store) :
  store_compat s1 s2 →
  dom s1 ⊆ dom s2 →
  store_restrict s2 (dom s1) = s1.
Proof. apply storeA_compat_restrict_eq. Qed.

Lemma store_compat_spec (s1 s2 : Store) :
  store_compat s1 s2 ↔
  store_restrict s1 (dom s1 ∩ dom s2) =
  store_restrict s2 (dom s1 ∩ dom s2).
Proof. apply storeA_compat_spec. Qed.

End StoreInterface.
