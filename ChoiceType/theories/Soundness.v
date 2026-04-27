(** * ChoiceType.Soundness

    The Fundamental Theorem (soundness) of the choice type system.

    For each typing derivation [Γ ⊢ᶜ e ⋮ τ] or [Γ ⊢ˢ e ⋮ τ], we show that
    the denotational semantics witnesses the judgment: every world satisfying
    the context denotation also satisfies the type denotation.

    Theorem statements (Definition 1.13 of the paper):
      Fundamental_comma : Γ ⊢ᶜ e ⋮ τ → ∀ m, m ⊨ ⟦Γ⟧ → m ⊨ ⟦τ⟧ e
      Fundamental_star  : Γ ⊢ˢ e ⋮ τ → ⟦Γ⟧ ⊫ ⟦τ⟧ e

    Proofs proceed by induction on the typing derivation.  All cases are
    Admitted in this skeleton; see the individual case comments for proof
    sketches.

    Corollaries instantiate the fundamental theorem to the five program
    verification conditions from the paper (§1.6). *)

From ChoiceType Require Export Typing.

(** ** Compatibility of satisfaction with monotone/antitone structure

    Note: satisfaction in Choice Logic is NOT uniformly Kripke-monotone.
    - [FImpl], [FForall], [FAnd], [FOr] are monotone (upward-closed) in m.
    - [FUnder] is *antitone* (downward-closed): m ⊨ FUnder φ ↔ ∃ m' ⊆ m, m' ⊨ φ.
    - [FOver] is *antitone* in the opposite direction.
    Therefore, we only state monotonicity for the sub-formulas where it holds. *)

(** FImpl is Kripke-monotone in [m]: satisfaction is preserved by [res_le]. *)
Lemma satisfies_impl_mono (φ ψ : FQ) (m m' : WorldT) :
  m ⊨ FImpl φ ψ →
  res_le (Var := atom) (Value := value) m m' →
  m' ⊨ FImpl φ ψ.
Proof. Admitted.

(** FAnd is monotone: both conjuncts preserved. *)
Lemma satisfies_and_mono (φ ψ : FQ) (m m' : WorldT) :
  m ⊨ FAnd φ ψ →
  res_le (Var := atom) (Value := value) m m' →
  m' ⊨ FAnd φ ψ.
Proof. Admitted.

(** ** Helper: context-split soundness

    If [ctx_split Γ Γ1 Γ2], then every world satisfying ⟦Γ⟧ can be split
    into two compatible worlds satisfying ⟦Γ1⟧ and ⟦Γ2⟧ respectively. *)

Lemma ctx_split_sound (Γ Γ1 Γ2 : ctx) (m : WorldT) :
  ctx_split Γ Γ1 Γ2 →
  m ⊨ ⟦Γ⟧ →
  ∃ m1 m2,
    res_le (Var := atom) (Value := value) (res_product m1 m2) m ∧
    world_compat (Var := atom) (Value := value) m1 m2 ∧
    m1 ⊨ ⟦Γ1⟧ ∧
    m2 ⊨ ⟦Γ2⟧.
Proof.
  (** Proof sketch:
      Induction on [ctx_split]:
        SpEmp   : m ⊨ FTrue; take m1 = m2 = res_unit.
        SpPers  : m ⊨ ⟦CTPers τ⟧(return x); share m between m1 and m2
                  using the persistence of CTPers.
        SpLeft  : take m1 = m, m2 = res_unit.
        SpRight : take m1 = res_unit, m2 = m.
        SpComma/SpStar : decompose m via the denotation of (⊗/,) and recurse. *)
  Admitted.

(** ** Fundamental Theorem *)

(** *** Comma-mode soundness

    [Γ ⊢ᶜ e ⋮ τ] implies [∀ m, m ⊨ ⟦Γ⟧ → m ⊨ ⟦τ⟧ e].

    Proof structure (by induction on the derivation):

    CT_Var    : ⟦CtxBind x τ⟧ = ⟦τ⟧ (return x) = ⟦τ⟧ e; immediate.

    CT_ConstO : ⟦CtxEmpty⟧ = FTrue; the over-denotation of (return c) with
                qualifier (ν = c) holds because c evaluates to c.

    CT_Lam    : unfold ⟦CTArrow x τx τ⟧ (return (λy.e)) to an FImpl;
                the IH gives the body proof from any Kripke extension.

    CT_Fix    : similar to CT_Lam; use IH on the body with self-reference.

    CT_Let_comma : apply IH for e1 to get ⟦τ1⟧ e1; bind the result ν and
                   apply IH for e2 to get ⟦τ2⟧ e2.

    CT_App_comma : unfold ⟦CTArrow x τx τ⟧ (return f), which is an FImpl;
                   apply it to the IH for the argument.

    CT_LetOp / CT_Match : similar let-style reasoning.

    CT_Inter  : by IH for both branches.
    CT_Union* : by IH for the chosen branch.
    CT_Pers   : use the persist_ctx semantics and FPers introduction.
    CT_Star   : ⟦CTStar τ⟧ e = FPers (⟦τ⟧ e); use FPers-intro.
    CT_Sub_comma : by the sub_comma hypothesis.
    CT_Weak   : use denot_ctx_mono_comma to extend the world.
    CT_Exchange : use commutativity of FAnd (⟦CtxComma⟧ = FAnd).
    CT_Mode_up  : lift the under-type to over-type semantically. *)

Theorem Fundamental_comma (Γ : ctx) (e : tm) (τ : choice_ty) :
  Γ ⊢ᶜ e ⋮ τ →
  ∀ m, m ⊨ ⟦Γ⟧ → m ⊨ ⟦τ⟧ e.
Proof. Admitted.

(** *** Star-mode soundness

    [Γ ⊢ˢ e ⋮ τ] implies [⟦Γ⟧ ⊫ ⟦τ⟧ e], i.e.,
    [∀ m, m ⊨ ⟦Γ⟧ → m ⊨ ⟦τ⟧ e].

    Proof structure (by induction on the derivation):

    CT_ConstU  : ⟦CtxEmpty⟧ = FTrue; the under-denotation of (return c) holds.

    CT_Wand    : unfold ⟦CTWand x τx τ⟧ to an FWand; use IH on the body.

    CT_Let_star : decompose the star context; use IH for e1 on m1 and e2 on m2.

    CT_App_star : apply the wand with the argument resource m2.

    CT_SumL/R  : build an FPlus witness using one of the parts.

    CT_Sub_star : apply sub_star = wand-entailment directly.

    CT_Sp       : use ctx_split_sound to get m1 and drop m2; apply IH on m1.

    CT_Mode_up  : impossible (CT_Mode_up is a comma rule). *)

Theorem Fundamental_star (Γ : ctx) (e : tm) (τ : choice_ty) :
  Γ ⊢ˢ e ⋮ τ →
  ⟦Γ⟧ ⊫ ⟦τ⟧ e.
Proof. Admitted.

(** ** Corollaries

    The five program-verification conditions from §1.6 of the paper.
    Each follows by specialising the Fundamental Theorem to a specific
    type, then unfolding the denotation. *)

(** *** Safety

    If e is closed and has over-type {ν:b | ⊤}, then e does not get stuck:
    every reachable term is either a value or can reduce further. *)
Corollary safety (e : tm) (b : base_ty) :
  CtxEmpty ⊢ᶜ e ⋮ CTOver b qual_top →
  ∀ e', steps e e' → is_val e' ∨ ∃ e'', step e' e''.
Proof.
  (** Sketch:
      Apply Fundamental_comma to get m ⊨ ⟦CTOver b ⊤⟧ e (with m = FTrue).
      Unfold the over-denotation: ∃ ν, e →* return ν  (by FOver semantics).
      Use progress (from CoreLang.Properties) for the basic type [erase_ty τ]. *)
  Admitted.

(** *** Coverage

    If e is closed and has under-type [ν:b | ⊤], then some execution terminates. *)
Corollary coverage (e : tm) (b : base_ty) :
  CtxEmpty ⊢ˢ e ⋮ CTUnder b qual_top →
  ∃ v, steps e (tret v).
Proof.
  (** Sketch:
      Apply Fundamental_star to get m ⊨ ⟦CTUnder b ⊤⟧ e.
      Unfold the under-denotation to get ∃ ν such that e →* return ν. *)
  Admitted.

(** *** Refinement (Hoare-style all-paths correctness)

    If e has over-type {ν:b | φ}, then *all* reachable values satisfy φ. *)
Corollary refinement (e : tm) (b : base_ty) (φ : qualifier) :
  CtxEmpty ⊢ᶜ e ⋮ CTOver b φ →
  ∀ v, steps e (tret v) →
       qual_interp ∅ ({0 ~> v} φ).
Proof.
  (** Sketch:
      Fundamental_comma gives m ⊨ ⟦CTOver b φ⟧ e.
      Unfold: ∀ ν result of e, ∀_{FV(φ)} ◁φ holds.
      For a concrete value v with e →* return v, instantiate ν = v. *)
  Admitted.

(** *** Incorrectness (under-approximation / reachability)

    If e has under-type [ν:b | φ], then *some* reachable value satisfies φ. *)
Corollary incorrectness (e : tm) (b : base_ty) (φ : qualifier) :
  CtxEmpty ⊢ˢ e ⋮ CTUnder b φ →
  ∃ v, steps e (tret v) ∧ qual_interp ∅ ({0 ~> v} φ).
Proof.
  (** Sketch:
      Fundamental_star gives m ⊨ ⟦CTUnder b φ⟧ e.
      Unfold: ∃ ν result of e, ▷φ witnesses ν.
      The under-approximation [▷] extracts a specific witness. *)
  Admitted.

(** *** Exact result

    If e has the singleton under-type [ν:b | ν = c], then e can produce c. *)
Corollary exact_result (e : tm) (b : base_ty) (c : constant) :
  CtxEmpty ⊢ˢ e ⋮ CTUnder b (b0:c= c) →
  steps e (tret (vconst c)).
Proof.
  (** Follows from [incorrectness] with φ = (ν = c):
      ∃ v, e →* return v ∧ v = c,  so e →* return c. *)
  Admitted.

(** ** Structural soundness lemmas

    These are used as lemmas inside the Fundamental Theorem proof.
    They are stated here with their proof obligations Admitted. *)

(** Context denotation of a comma-context distributes: ⟦Γ1,Γ2⟧ = ⟦Γ1⟧ ∧ ⟦Γ2⟧. *)
Lemma denot_ctx_comma_split (Γ1 Γ2 : ctx) (m : WorldT) :
  m ⊨ ⟦CtxComma Γ1 Γ2⟧ ↔ m ⊨ ⟦Γ1⟧ ∧ m ⊨ ⟦Γ2⟧.
Proof. simpl. reflexivity. Qed.

(** Context denotation of a star-context distributes via FStar. *)
Lemma denot_ctx_star_split (Γ1 Γ2 : ctx) (m : WorldT) :
  m ⊨ ⟦CtxStar Γ1 Γ2⟧ ↔
  ∃ m1 m2,
    res_le (Var := atom) (Value := value) (res_product m1 m2) m ∧
    world_compat (Var := atom) (Value := value) m1 m2 ∧
    m1 ⊨ ⟦Γ1⟧ ∧ m2 ⊨ ⟦Γ2⟧.
Proof. simpl. reflexivity. Qed.

(** FImpl introduction lemma: implies-in-all-Kripke-extensions. *)
Lemma satisfies_impl_intro (m : WorldT) (φ ψ : FQ) :
  (∀ m', res_le (Var := atom) (Value := value) m m' →
         m' ⊨ φ → m' ⊨ ψ) →
  m ⊨ FImpl φ ψ.
Proof. Admitted.

(** FForall introduction: universally quantified over σ-projections. *)
Lemma satisfies_forall_intro (m : WorldT) (X : aset) (φ : FQ) :
  (∀ σ,
     res_restrict (Var := atom) (Value := value) m X σ →
     fiber (Var := atom) (Value := value) m σ ⊨ φ) →
  m ⊨ FForall X φ.
Proof. Admitted.

(** FPers introduction: point-wise singleton satisfaction. *)
Lemma satisfies_pers_intro (m : WorldT) (φ : FQ) :
  (∀ σ, m σ →
        satisfies qual_interp_cl qual_subst (fun σ' => σ' = σ) φ) →
  m ⊨ FPers φ.
Proof. Admitted.

(** Persist_ctx semantics: ⟦persist_ctx Γ⟧ is the persistent version of ⟦Γ⟧. *)
Lemma denot_persist_ctx (Γ : ctx) (m : WorldT) :
  m ⊨ ⟦persist_ctx Γ⟧ →
  ∀ σ, m σ → (fun σ' => σ' = σ) ⊨ ⟦Γ⟧.
Proof. Admitted.

(** Entailment is upward-closed for monotone formulas (FImpl, FAnd, FOr, FAtom). *)
Lemma ctx_satisfies_mono (Γ : ctx) (m m' : WorldT) :
  m ⊨ ⟦Γ⟧ →
  res_le (Var := atom) (Value := value) m m' →
  m' ⊨ ⟦Γ⟧.
Proof. Admitted.
