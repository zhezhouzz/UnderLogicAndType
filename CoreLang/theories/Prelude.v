(** * CoreLang.Prelude

    Typeclass infrastructure and atom type, following the pattern of
    UnderType/BaseDef.v.  All locally-nameless operations (open, close,
    substitution, free-variable collection, local-closure) are given
    uniform classes and notations so that lemma statements are
    syntactically identical across syntactic categories. *)

From ChoicePrelude Require Export Prelude.
From stdpp Require Export fin vector.

(** ** Core typeclasses *)

(** Single-variable substitution: [atom → V → A → A].
    Named [SubstV] (variable substitution) to avoid clashing with
    [UnderLogicAndType.Substitution.Subst] which is a [Definition : Type]. *)
Class SubstV V A := subst_one : atom → V → A → A.

(** Opening: [nat → V → A → A]. *)
Class Open V A := open_one : nat → V → A → A.

(** Closing: [atom → nat → A → A]. *)
Class Close A := close_one : atom → nat → A → A.

(** Local closure predicate. *)
Class Lc A := is_lc : A → Prop.

(** Multi-variable substitution (apply a whole gmap): [V → A → A]. *)
Class SubstM V A := subst_map : V → A → A.

(** Standard typing and denotation classes. *)
Class Typing G E T := has_type : G → E → T → Prop.
Class Denotation A B := denote : A → B.

(** ** Uniform notations *)

Notation "'{' x ':=' v '}' e"  := (subst_one x v e)
  (at level 20, x constr, v constr, format "{ x := v } e").
Notation "'{' k '~>' v '}' e"  := (open_one k v e)
  (at level 20, k constr, format "{ k ~> v } e").
Notation "e '^^' x"            := (open_one 0 x e) (at level 20).
Notation "'{' k '<~' x '}' e"  := (close_one x k e)
  (at level 20, k constr, format "{ k <~ x } e").
Notation "x '\\' e"            := (close_one x 0 e) (at level 20).
Notation "Γ '⊢' e '⋮' T"      := (has_type Γ e T)
  (at level 20, e constr, T constr).
Notation "'⟦' a '⟧'"           := (denote a) (at level 20, format "⟦ a ⟧").
(** Multi-substitution: use [subst_map σ e] directly to avoid clashing with
    stdpp's singleton-set notation [{[ _ ]}] which has the same '{[' prefix. *)

(** ** Hint databases *)
#[global] Hint Unfold stale subst_one open_one close_one is_lc subst_map has_type denote : class_simpl.
