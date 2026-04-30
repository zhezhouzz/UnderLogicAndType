(** * ChoiceType.Soundness

    Soundness skeleton for the single declarative typing judgment. *)

From ChoiceType Require Export Typing.

(** ** Compatibility of satisfaction with monotone/antitone structure *)

Lemma satisfies_impl_mono (φ ψ : FQ) (m m' : WorldT) :
  m ⊨ FImpl φ ψ →
  raw_le (Var := atom) (Value := value) m m' →
  m' ⊨ FImpl φ ψ.
Proof. Admitted.

Lemma satisfies_and_mono (φ ψ : FQ) (m m' : WorldT) :
  m ⊨ FAnd φ ψ →
  raw_le (Var := atom) (Value := value) m m' →
  m' ⊨ FAnd φ ψ.
Proof. Admitted.

(** ** Fundamental theorem *)

Theorem Fundamental (Γ : ctx) (e : tm) (τ : choice_ty) :
  Γ ⊢ e ⋮ τ →
  ⟦Γ⟧ ⊫ ⟦τ⟧ e.
Proof. Admitted.

(** ** Corollaries

    The theorem statements follow the single typing judgment.  The proof
    bodies remain as admitted skeletons while the definition layer is being
    aligned with the paper. *)

Corollary safety (e : tm) (b : base_ty) :
  CtxEmpty ⊢ e ⋮ CTOver b qual_top →
  ∀ e', steps e e' → is_val e' ∨ ∃ e'', step e' e''.
Proof. Admitted.

Corollary coverage (e : tm) (b : base_ty) :
  CtxEmpty ⊢ e ⋮ CTUnder b qual_top →
  ∃ v, steps e (tret v).
Proof. Admitted.

Corollary refinement (e : tm) (b : base_ty) (φ : qualifier) :
  CtxEmpty ⊢ e ⋮ CTOver b φ →
  ∀ v, steps e (tret v) →
       qual_interp ∅ ({0 ~> v} φ).
Proof. Admitted.

Corollary incorrectness (e : tm) (b : base_ty) (φ : qualifier) :
  CtxEmpty ⊢ e ⋮ CTUnder b φ →
  ∃ v, steps e (tret v) ∧ qual_interp ∅ ({0 ~> v} φ).
Proof. Admitted.

Corollary exact_result (e : tm) (b : base_ty) (c : constant) :
  CtxEmpty ⊢ e ⋮ CTUnder b (b0:c= c) →
  steps e (tret (vconst c)).
Proof. Admitted.

(** ** Structural soundness lemmas *)

Lemma denot_ctx_comma_split (Γ1 Γ2 : ctx) (m : WorldT) :
  m ⊨ ⟦CtxComma Γ1 Γ2⟧ ↔ m ⊨ ⟦Γ1⟧ ∧ m ⊨ ⟦Γ2⟧.
Proof. simpl. reflexivity. Qed.

Lemma denot_ctx_star_split (Γ1 Γ2 : ctx) (m : WorldT) :
  m ⊨ ⟦CtxStar Γ1 Γ2⟧ ↔
  ∃ m1 m2,
    raw_le (Var := atom) (Value := value) (raw_product m1 m2) m ∧
    world_compat (Var := atom) (Value := value) m1 m2 ∧
    m1 ⊨ ⟦Γ1⟧ ∧ m2 ⊨ ⟦Γ2⟧.
Proof. simpl. reflexivity. Qed.

Lemma satisfies_impl_intro (m : WorldT) (φ ψ : FQ) :
  (∀ m', raw_le (Var := atom) (Value := value) m m' →
         m' ⊨ φ → m' ⊨ ψ) →
  m ⊨ FImpl φ ψ.
Proof. Admitted.

Lemma satisfies_fib_intro (m : WorldT) (X : aset) (φ : FQ) :
  (∀ σ,
     raw_restrict (Var := atom) (Value := value) m X σ →
     raw_fiber (Var := atom) (Value := value) m σ ⊨ φ) →
  m ⊨ FFib X φ.
Proof. Admitted.

Lemma satisfies_forall_intro (m : WorldT) (x : atom) (φ : FQ) :
  (∀ m',
      world_dom m' = world_dom m ∪ {[x]} →
      raw_restrict (Var := atom) (Value := value) m' (world_dom m) = m →
      m' ⊨ φ) →
  m ⊨ FForall x φ.
Proof. Admitted.

Lemma satisfies_exists_intro (m m' : WorldT) (x : atom) (φ : FQ) :
  world_dom m' = world_dom m ∪ {[x]} →
  raw_restrict (Var := atom) (Value := value) m' (world_dom m) = m →
  m' ⊨ φ →
  m ⊨ FExists x φ.
Proof. Admitted.

Lemma ctx_satisfies_mono (Γ : ctx) (m m' : WorldT) :
  m ⊨ ⟦Γ⟧ →
  raw_le (Var := atom) (Value := value) m m' →
  m' ⊨ ⟦Γ⟧.
Proof. Admitted.
