From ChoiceLogic Require Import Prelude.
From CoreLang Require Import Syntax.

(** * Logic qualifiers

    Logic qualifiers are resource-level atoms.  They carry:
    - a finite domain [d] of referenced variables;
    - a concrete store used to record the referenced variables' values;
    - a predicate over the domain-restricted store and world.

    We do not require [dom store = d] or [world_dom w = d].  Denotation
    restricts both inputs to [d] before calling the predicate. *)

Definition StoreT := (gmap atom value).
Definition RawWorldT := (@World atom _ _ value).
Definition WorldT := (@WfWorld atom _ _ value).

Inductive logic_qualifier : Type :=
  | lqual (d : aset) (store : StoreT) (prop : StoreT → WorldT → Prop).

Definition lqual_dom (q : logic_qualifier) : aset :=
  match q with
  | lqual d _ _ => d
  end.

Definition lqual_store (q : logic_qualifier) : StoreT :=
  match q with
  | lqual _ σ _ => σ
  end.

Definition lqual_prop (q : logic_qualifier) : StoreT → WorldT → Prop :=
  match q with
  | lqual _ _ p => p
  end.

#[global] Instance stale_logic_qualifier : Stale logic_qualifier := lqual_dom.
Arguments stale_logic_qualifier /.

Definition logic_qualifier_denote (q : logic_qualifier) (w : WorldT) : Prop :=
  match q with
  | lqual d σ p => p (store_restrict σ d) (res_restrict w d)
  end.

(** The expression atom is intentionally left abstract for now. *)
Parameter expr_logic_qual : tm → atom → logic_qualifier.
