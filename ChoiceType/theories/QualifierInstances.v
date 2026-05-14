(** * ChoiceType.QualifierInstances

    Locally-nameless theorem-class instances for shallow type qualifiers.

    Qualifiers open binders with atoms, not CoreLang values.  We therefore only
    register atom-open instances whose statements are syntactic/domain facts.
    The full [OpenSwap] instance is intentionally absent: shallow qualifier
    propositions may be equal only up to logical equivalence after reordering
    nested existential witnesses. *)

From LocallyNameless Require Import Classes.
From ChoiceType Require Import QualifierProps.

#[global] Instance OpenFv_qualifier : OpenFv atom type_qualifier.
Proof.
Admitted.

#[global] Instance OpenFvPrime_qualifier : OpenFvPrime atom type_qualifier.
Proof.
Admitted.

#[global] Instance OpenRecLc_qualifier : OpenRecLc atom type_qualifier.
Proof.
Admitted.

#[global] Instance OpenLcRespect_qualifier : OpenLcRespect atom type_qualifier.
Proof.
Admitted.

#[global] Instance OpenIdemp_qualifier : OpenIdemp atom type_qualifier.
Proof.
Admitted.
