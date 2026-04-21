From UnderLogicAndType Require Import Prelude Substitution Resource.

(** * Choice Logic  (Definitions 1.8 and 1.9)

    We define the syntax of choice logic formulas and the satisfaction relation.

    Parameterization:
    - [A]           : type of atomic propositions
    - [interp]      : interpretation A → (Subst → Prop), maps atoms to sets of substs
    - [subst_atom]  : Subst → A → A, substitution action on atoms
                      (used in the read modality to compute σ(p))

    The formula type [Formula A] contains:
    - standard connectives (⊤, ⊥, atoms, ∧, ∨, ⇒)
    - separation logic connectives (∗, −∗)
    - choice sum (⊕)
    - approximation modalities (o = over, u = under)
    - persistence modality (□)
    - read modality (X : φ ▷ p) where φ is a semantic guard [Subst → Prop]  *)

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
  | FPers   (p : Formula A)                     (* persistence  □ p *)
  | FRead   (X : gset Var)                      (* read modality  X:φ ▷ p *)
            (guard : SubstT → Prop)             (*   guard φ : set of substs *)
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
Arguments FPers  {A} _.
Arguments FRead  {A} _ _ _.

(** ** Substitution action on formulas

    [formula_subst subst_atom σ φ] applies σ to every atom in φ.
    For [FRead], the guard is already semantic so σ is not applied to it;
    σ is applied to the body. *)

Fixpoint formula_subst {A} (subst_atom : SubstT → A → A) (σ : SubstT) (φ : Formula A) : Formula A :=
  match φ with
  | FTrue        => FTrue
  | FFalse       => FFalse
  | FAtom a      => FAtom (subst_atom σ a)
  | FAnd p q     => FAnd   (formula_subst subst_atom σ p) (formula_subst subst_atom σ q)
  | FOr  p q     => FOr    (formula_subst subst_atom σ p) (formula_subst subst_atom σ q)
  | FImpl p q    => FImpl  (formula_subst subst_atom σ p) (formula_subst subst_atom σ q)
  | FStar p q    => FStar  (formula_subst subst_atom σ p) (formula_subst subst_atom σ q)
  | FWand p q    => FWand  (formula_subst subst_atom σ p) (formula_subst subst_atom σ q)
  | FPlus p q    => FPlus  (formula_subst subst_atom σ p) (formula_subst subst_atom σ q)
  | FOver p      => FOver  (formula_subst subst_atom σ p)
  | FUnder p     => FUnder (formula_subst subst_atom σ p)
  | FPers p      => FPers  (formula_subst subst_atom σ p)
  | FRead X g p  => FRead X g (formula_subst subst_atom σ p)
  end.

(** ** Formula size (used as termination measure for [satisfies]) *)

Fixpoint formula_size {A} (φ : Formula A) : nat :=
  match φ with
  | FTrue | FFalse | FAtom _ => 1
  | FAnd p q | FOr p q | FImpl p q
  | FStar p q | FWand p q | FPlus p q => 1 + formula_size p + formula_size q
  | FOver p | FUnder p | FPers p      => 1 + formula_size p
  | FRead _ _ p                       => 1 + formula_size p
  end.

(** Substitution preserves size (key lemma for termination). *)
Lemma formula_subst_size {A} (sa : SubstT → A → A) σ (φ : Formula A) :
  formula_size (formula_subst sa σ φ) = formula_size φ.
Proof.
  induction φ; simpl; try lia; try (rewrite IHφ1, IHφ2; lia); rewrite IHφ; lia.
Qed.

(** ** Satisfaction relation

    [satisfies interp subst_atom m φ] is written [m ⊨ φ] below.

    For the [FRead] case we need σ(p).  Instead of recursing on
    [formula_subst σ p] (not a syntactic subterm), we thread σ into
    [interp]: [satisfies (λ a, interp (subst_atom σ a)) subst_atom m' p].
    This is definitionally equivalent (see [satisfies_subst_eq] below) and
    keeps [satisfies] a plain structural [Fixpoint]. *)

Fixpoint satisfies {A}
    (interp     : A → (SubstT → Prop))
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
      ∃ m', (∀ σ, m σ → m' σ) ∧ satisfies interp subst_atom m' p

  | FUnder p =>
      (** m ⊨ u p  iff  ∃ m' ⊆ m. m' ⊨ p  (under-approximation: subset) *)
      ∃ m', (∀ σ, m' σ → m σ) ∧ satisfies interp subst_atom m' p

  | FPers p =>
      (** m ⊨ □ p  iff  |m| ≤ 1  ∧  m ⊨ p *)
      (∀ σ1 σ2, m σ1 → m σ2 → σ1 = σ2) ∧
      satisfies interp subst_atom m p

  | FRead X guard p =>
      (** m ⊨ X:φ ▷ p  iff
          ∀ σ. σ ∈ ⟦φ⟧  ∧  dom(σ) = X  ∧  m ⋉ σ ≠ ∅
               →  m ⋉ σ ⊨ σ(p)                               *)
      ∀ σ,
        guard σ →
        dom σ = X →
        (∃ σ', semijoin m σ σ') →
        (** Apply σ to [interp] rather than substituting into the formula;
            equivalent by [satisfies_subst_eq] below. *)
        satisfies (λ a, interp (subst_atom σ a)) subst_atom (semijoin m σ) p

  end.

(** Equivalence between the two views of σ-substitution in the semantics. *)
Lemma satisfies_subst_eq {A} (interp : A → SubstT → Prop) (sa : SubstT → A → A)
    σ (m : WorldT) (φ : Formula A) :
  satisfies interp sa m (formula_subst sa σ φ) ↔
  satisfies (λ a, interp (sa σ a)) sa m φ.
Proof. Admitted.

(** Notation: [m ⊨[ interp , sa ] φ] *)
Local Notation "m ⊨[ interp , sa ] φ" :=
  (satisfies interp sa m φ) (at level 70, format "m  ⊨[ interp , sa ]  φ").

(** Entailment: φ ⊨ ψ holds when every world satisfying φ also satisfies ψ. *)
Definition entails {A} interp sa (φ ψ : Formula A) : Prop :=
  ∀ m, m ⊨[interp, sa] φ → m ⊨[interp, sa] ψ.

Local Notation "φ ⊢[ interp , sa ] ψ" :=
  (entails interp sa φ ψ) (at level 70, format "φ  ⊢[ interp , sa ]  ψ").

End ChoiceLogic.

(** After the section closes, Var/EqDecision/Countable/Value become explicit
    arguments.  Make them all implicit so users can write [FOver p] rather
    than [@FOver Var _ _ Value A p]. *)
Arguments FTrue  {Var _ _ Value A}.
Arguments FFalse {Var _ _ Value A}.
Arguments FAtom  {Var _ _ Value A} _.
Arguments FAnd   {Var _ _ Value A} _ _.
Arguments FOr    {Var _ _ Value A} _ _.
Arguments FImpl  {Var _ _ Value A} _ _.
Arguments FStar  {Var _ _ Value A} _ _.
Arguments FWand  {Var _ _ Value A} _ _.
Arguments FPlus  {Var _ _ Value A} _ _.
Arguments FOver  {Var _ _ Value A} _.
Arguments FUnder {Var _ _ Value A} _.
Arguments FPers  {Var _ _ Value A} _.
Arguments FRead  {Var _ _ Value A} _ _ _.
