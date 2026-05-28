(** * Generic stores: partial key projection *)

From ContextBase Require Import Prelude LogicVar.
From ContextStore Require Import StoreCore StoreKeyAction.

Section StoreFilterMapKey.

Context {V : Type} `{ValueSig V}.

Definition storeA_filter_map_key
    {K K' : Type} `{Countable K} `{Countable K'}
    (f : K -> option K') (s : StoreA K) : StoreA K' :=
  map_fold (fun k v (acc : gmap K' V) =>
    match f k with
    | Some k' => <[k' := v]> acc
    | None => acc
    end) ∅ s.

Lemma storeA_filter_map_key_empty
    {K K' : Type} `{Countable K} `{Countable K'}
    (f : K -> option K') :
  storeA_filter_map_key f (∅ : StoreA K) = (∅ : StoreA K').
Proof.
  unfold storeA_filter_map_key. reflexivity.
Qed.

Definition AtomStore : Type := @StoreA V atom _ _.
Definition LVarStore : Type := @StoreA V logic_var _ _.

Definition atom_store_to_lvar_store (s : AtomStore) : LVarStore :=
  storeA_map_key LVFree s.

Definition lvar_to_atom (η : gmap nat atom) (v : logic_var) : option atom :=
  logic_var_to_atom η v.

Definition lvar_store_open (η : gmap nat atom) (s : LVarStore) : AtomStore :=
  storeA_filter_map_key (lvar_to_atom η) s.

Definition lvar_store_to_atom_store (s : LVarStore) : AtomStore :=
  lvar_store_open ∅ s.

End StoreFilterMapKey.
