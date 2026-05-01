From ChoiceLogic Require Import Prelude.
From CoreLang Require Import Syntax.

(** * Logic qualifiers

    Logic qualifiers are resource-level atoms.  They carry:
    - a finite domain [d] of referenced variables;
    - a predicate over the domain-restricted explicit store and world.

    We do not require [dom store = d] or [world_dom w = d].  Denotation
    restricts both inputs to [d] before calling the predicate. *)

Inductive logic_qualifier : Type :=
  | lqual (d : aset) (prop : Store → WfWorld → Prop).

Definition lqual_dom (q : logic_qualifier) : aset :=
  match q with
  | lqual d _ => d
  end.

Definition lqual_prop (q : logic_qualifier) : Store → WfWorld → Prop :=
  match q with
  | lqual _ p => p
  end.

#[global] Instance stale_logic_qualifier : Stale logic_qualifier := lqual_dom.
Arguments stale_logic_qualifier /.

Definition logic_qualifier_denote
    (q : logic_qualifier)
    (σ : Store)
    (w : WfWorld) : Prop :=
  match q with
  | lqual d p => p (store_restrict σ d) (res_restrict w d)
  end.

(** The expression atom is intentionally left abstract for now. *)
Parameter expr_logic_qual : tm → atom → logic_qualifier.
