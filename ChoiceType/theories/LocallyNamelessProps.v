(** * ChoiceType.LocallyNamelessProps

    Structural locally-nameless facts for choice types and tree-shaped
    contexts.  This file deliberately focuses on atom-open syntactic facts;
    paper-level typing and well-formedness remain in [ChoiceTyping].

    Choice types intentionally do not provide variable-to-value substitution:
    type qualifiers open locally-nameless binders to atoms, and future
    transport lemmas should use atom rename/swap rather than value
    substitution. *)

From LocallyNameless Require Import Classes.
From ChoiceType Require Export Syntax QualifierProps.
From ChoiceType Require Import QualifierInstances.
