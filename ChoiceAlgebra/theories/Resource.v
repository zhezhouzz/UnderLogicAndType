(** * ChoiceAlgebra.Resource

    Compatibility entry point for the atom-keyed resource interface.

    The old concrete resource development has been migrated into the
    abstract-key files and re-exported through [ResourceInterface].  Keep this
    file only so existing imports of [ChoiceAlgebra.Resource] continue to
    resolve while callers are moved to [ResourceInterface]. *)

From ChoiceAlgebra Require Export ResourceInterface ResourceExtensionCompat.
