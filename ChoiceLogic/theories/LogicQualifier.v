From ChoiceLogic Require Import Prelude.
From ChoicePrelude Require Export Qualifier.

(** * Logic qualifiers

    Logic qualifiers are resource-level atoms.  They carry:
    - a finite domain [d] of referenced variables;
    - a predicate over the domain-restricted explicit store and world.

    We do not require [dom store = d] or [world_dom w = d].  Denotation
    restricts both inputs to [d] before calling the predicate. *)

Section LogicQualifier.

Context {V : Type} `{ValueSig V}.

Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).

Definition logic_qualifier : Type := qualifier (V := V) (A := WfWorldT).

Definition logic_qualifier_denote
    (q : logic_qualifier)
    (bmap : gmap nat V)
    (σ : gmap atom V)
    (w : WfWorldT) : Prop :=
  qual_denote_with res_restrict q bmap σ w.

End LogicQualifier.
