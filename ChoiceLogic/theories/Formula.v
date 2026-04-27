From ChoiceLogic Require Import Prelude.

(** * Choice Logic  (Definitions 1.8 and 1.9)

    We define the syntax of choice logic formulas and the satisfaction relation.

    Parameterization:
    - [A]           : type of atomic propositions
    - [interp]      : interpretation A → (Subst → Prop), maps atoms to sets of substs
    - [subst_atom]  : Subst → A → A, substitution action on atoms
                      (used in the [FForall] case to thread σ_X into the interpretation)

    The formula type [Formula A] contains:
    - standard connectives (⊤, ⊥, atoms, ∧, ∨, ⇒)
    - separation logic connectives (∗, −∗)
    - choice sum (⊕)
    - approximation modalities (o = over, u = under)
    - persistence modality (□)
    - universal modality (∀X. p): for each σ_X in proj(m, X), the fiber satisfies σ_X(p)  *)

Section ChoiceLogic.

Context `{Countable Var} `{EqDecision Value}.
Local Notation SubstT := (gmap Var Value) (only parsing).
Local Notation WorldT := (@World Var _ _ Value) (only parsing).

(** ** Formula syntax *)

Inductive Formula (A : Type) : Type :=
  | FTrue
  | FFalse
  | FAtom   (a : A)
  | FAnd    (p q : Formula A)
  | FOr     (p q : Formula A)
  | FImpl   (p q : Formula A)                   (* Kripke implication *)
  | FStar   (p q : Formula A)                   (* separating conjunction p ∗ q *)
  | FWand   (p q : Formula A)                   (* magic wand p −∗ q *)
  | FPlus   (p q : Formula A)                   (* choice sum p ⊕ q *)
  | FOver   (p : Formula A)                     (* overapproximation  o p *)
  | FUnder  (p : Formula A)                     (* underapproximation u p *)
  | FPers    (p : Formula A)                    (* persistence  □ p *)
  | FForall  (X : gset Var)                     (* universal modality  ∀X. p *)
             (p : Formula A).

(** Make [A] implicit inside the section so constructors can be written
    without an explicit type argument, e.g. [FTrue] not [FTrue A]. *)
Arguments FTrue  {A}.
Arguments FFalse {A}.
Arguments FAtom  {A} _.
Arguments FAnd   {A} _ _.
Arguments FOr    {A} _ _.
Arguments FImpl  {A} _ _.
Arguments FStar  {A} _ _.
Arguments FWand  {A} _ _.
Arguments FPlus  {A} _ _.
Arguments FOver  {A} _.
Arguments FUnder {A} _.
Arguments FPers   {A} _.
Arguments FForall {A} _ _.

(** ** Satisfaction relation

    [satisfies interp subst_atom m φ] is written [m ⊨ φ] below.

    Role of [subst_atom]:
    [subst_atom] is only *consumed* in the [FForall] case; every other case
    merely threads it through to recursive calls so it is available when a
    nested [FForall] is eventually reached.  It represents the substitution
    action on atomic propositions: when entering [∀X. p] under a witness σ_X,
    atoms that mention variables in X must be specialized to σ_X's values.
    If atoms are closed (contain no free variables), [subst_atom = λ σ a, a]
    is the correct instantiation and the threading is a no-op.

    Structural-Fixpoint trick for [FForall]:
    The semantics of [FForall X p] requires evaluating σ_X(p) — the formula p
    with every atom a replaced by [subst_atom σ_X a].  The direct approach
    would recurse on [formula_subst subst_atom σ p], but that is not a
    syntactic subterm of [FForall X p], so Rocq's structural [Fixpoint]
    checker rejects it.  Instead we thread σ into the interpretation function:
      [satisfies (λ a, interp (subst_atom σ a)) subst_atom (fiber m σ) p]
    Unfolding the definition confirms this is pointwise equal to evaluating
    the substituted formula, with [subst_atom] propagated so that any nested
    [FForall] can apply its own substitution on top. *)

Fixpoint satisfies {A}
    (interp     : A → WorldT)
    (subst_atom : SubstT → A → A)
    (m          : WorldT)
    (φ          : Formula A) : Prop :=
  match φ with

  (** Basic connectives (Definition 1.8) *)

  | FTrue  => True

  | FFalse => False

  | FAtom a =>
      (** m ⊨ a  iff  ⟦a⟧ ≤ᵣ m *)
      res_le (interp a) m

  | FAnd p q =>
      satisfies interp subst_atom m p ∧ satisfies interp subst_atom m q

  | FOr p q =>
      satisfies interp subst_atom m p ∨ satisfies interp subst_atom m q

  | FImpl p q =>
      (** Kripke implication: ∀ m' ≥ m. m' ⊨ p → m' ⊨ q *)
      ∀ m', res_le m m' → satisfies interp subst_atom m' p →
            satisfies interp subst_atom m' q

  | FStar p q =>
      (** m ⊨ p ∗ q  iff  ∃ m1 m2. m1 × m2 ≤ m  ∧  m1 ⊨ p  ∧  m2 ⊨ q *)
      ∃ m1 m2,
        res_le (res_product m1 m2) m ∧
        world_compat m1 m2 ∧
        satisfies interp subst_atom m1 p ∧
        satisfies interp subst_atom m2 q

  | FWand p q =>
      (** m ⊨ p −∗ q  iff  ∀ m'. m' ↑ m  →  m' ⊨ p  →  m' × m ⊨ q *)
      ∀ m',
        world_compat m' m →
        satisfies interp subst_atom m' p →
        satisfies interp subst_atom (res_product m' m) q

  | FPlus p q =>
      (** m ⊨ p ⊕ q  iff  ∃ m1 m2. m1 + m2 ≤ m  ∧  m1 ⊨ p  ∧  m2 ⊨ q *)
      ∃ m1 m2,
        res_le (res_sum m1 m2) m ∧
        res_sum_defined m1 m2 ∧
        satisfies interp subst_atom m1 p ∧
        satisfies interp subst_atom m2 q

  (** Approximation modalities (Definition 1.9) *)

  | FOver p =>
      (** m ⊨ o p  iff  ∃ m' ⊇ m. m' ⊨ p  (over-approximation: superset) *)
      ∃ m' : WorldT, (∀ σ, m σ → m' σ) ∧ satisfies interp subst_atom m' p

  | FUnder p =>
      (** m ⊨ u p  iff  ∃ m' ⊆ m. m' ⊨ p  (under-approximation: subset) *)
      ∃ m' : WorldT, (∀ σ, m' σ → m σ) ∧ satisfies interp subst_atom m' p

  | FPers p =>
      (** m ⊨ □ p  iff  ∀ σ ∈ m. {σ} ⊨ p *)
      ∀ σ, m σ →
        satisfies interp subst_atom
          {| world_dom := dom σ; world_stores := λ s, s = σ |} p

  | FForall X p =>
      (** m ⊨ ∀X. p  iff  ∀ σ_X ∈ proj(m, X).  fiber(m, σ_X) ⊨ σ_X(p)
          [subst_atom σ] is applied to every atom via the modified [interp];
          [subst_atom] itself is forwarded so nested [FForall]s can compose. *)
      ∀ σ,
        res_restrict m X σ →
        satisfies (λ a, interp (subst_atom σ a)) subst_atom (fiber m σ) p

  end.

(** Notation: [m ⊨[ interp , sa ] φ] *)
Local Notation "m ⊨[ interp , sa ] φ" :=
  (satisfies interp sa m φ) (at level 70, format "m  ⊨[ interp , sa ]  φ").

(** Entailment: φ ⊨ ψ holds when every world satisfying φ also satisfies ψ. *)
Definition entails {A} interp sa (φ ψ : Formula A) : Prop :=
  ∀ m, m ⊨[interp, sa] φ → m ⊨[interp, sa] ψ.

Local Notation "φ ⊢[ interp , sa ] ψ" :=
  (entails interp sa φ ψ) (at level 70, format "φ  ⊢[ interp , sa ]  ψ").

End ChoiceLogic.

(** After the section closes the section variables become explicit.
    Re-establish implicitness using positional underscores with [rename]
    to avoid name-mismatch errors. *)
Arguments FTrue  {_} {_} {_} {_} : rename.
Arguments FFalse {_} {_} {_} {_} : rename.
Arguments FAtom  {_} {_} {_} {_} _ : rename.
Arguments FAnd   {_} {_} {_} {_} _ _ : rename.
Arguments FOr    {_} {_} {_} {_} _ _ : rename.
Arguments FImpl  {_} {_} {_} {_} _ _ : rename.
Arguments FStar  {_} {_} {_} {_} _ _ : rename.
Arguments FWand  {_} {_} {_} {_} _ _ : rename.
Arguments FPlus  {_} {_} {_} {_} _ _ : rename.
Arguments FOver  {_} {_} {_} {_} _ : rename.
Arguments FUnder {_} {_} {_} {_} _ : rename.
Arguments FPers   {_} {_} {_} {_} _ : rename.
Arguments FForall {_} {_} {_} {_} _ _ : rename.
