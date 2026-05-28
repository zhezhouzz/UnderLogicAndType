(** * Concrete store compatibility interface lemmas *)

From ContextBase Require Import Prelude LogicVar.
From ContextStore Require Import StoreCore StoreKeyAction StoreRestrictCore StoreRestrictUnion StoreBind.
From ContextStore Require Export StoreInterfaceRestrict.

Section StoreInterface.

Context {V : Type} `{ValueSig V}.

Local Notation Store := (@StoreA V atom _ _) (only parsing).
Local Notation LStore := (@StoreA V logic_var _ _) (only parsing).

End StoreInterface.
