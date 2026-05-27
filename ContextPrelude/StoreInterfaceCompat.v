(** * Concrete store compatibility interface lemmas *)

From ContextPrelude Require Import Prelude StoreCore StoreKeyAction StoreRestrict StoreBind.
From ContextPrelude Require Export StoreInterfaceRestrict.

Section StoreInterface.

Context {V : Type} `{ValueSig V}.

Local Notation Store := (@StoreA V atom _ _) (only parsing).
Local Notation LStore := (@StoreA V logic_var _ _) (only parsing).

End StoreInterface.
