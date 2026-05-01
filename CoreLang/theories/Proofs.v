(** * CoreLang.Proofs

    Aggregator for the CoreLang proof inventory imported from the HATs and
    UnderType developments:

    - locally-nameless helper facts,
    - basic typing facts,
    - operational semantics facts.

    Some deeper substitution/opening and decomposition lemmas are intentionally
    listed with [Admitted] proofs in their source files while the definition
    layer and theorem interfaces stabilize. *)

From CoreLang Require Export LocallyNamelessProps BasicTypingProps OperationalProps.
