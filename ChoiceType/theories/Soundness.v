(** * ChoiceType.Soundness

    Soundness skeleton for the single declarative typing judgment. *)

From ChoiceType Require Export Typing.

(** ** Compatibility of satisfaction with monotone/antitone structure *)

Lemma res_models_impl_mono (φ ψ : FQ) (m m' : WfWorld) :
  m ⊨ FImpl φ ψ →
  m ⊑ m' →
  m' ⊨ FImpl φ ψ.
Proof. Admitted.

Lemma res_models_and_mono (φ ψ : FQ) (m m' : WfWorld) :
  m ⊨ FAnd φ ψ →
  m ⊑ m' →
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

Corollary refinement (e : tm) (b : base_ty) (φ : type_qualifier) :
  CtxEmpty ⊢ e ⋮ CTOver b φ →
  ∀ v, steps e (tret v) →
       qual_interp ∅ ({0 ~> v} φ).
Proof. Admitted.

Corollary incorrectness (e : tm) (b : base_ty) (φ : type_qualifier) :
  CtxEmpty ⊢ e ⋮ CTUnder b φ →
  ∃ v, steps e (tret v) ∧ qual_interp ∅ ({0 ~> v} φ).
Proof. Admitted.

Corollary exact_result (e : tm) (b : base_ty) (c : constant) :
  CtxEmpty ⊢ e ⋮ CTUnder b (b0:c= c) →
  steps e (tret (vconst c)).
Proof. Admitted.

(** ** Structural soundness lemmas *)

Lemma denot_ctx_comma_split (Γ1 Γ2 : ctx) (m : WfWorld) :
  m ⊨ ⟦CtxComma Γ1 Γ2⟧ ↔ m ⊨ ⟦Γ1⟧ ∧ m ⊨ ⟦Γ2⟧.
Proof. Admitted.

Lemma denot_ctx_star_split (Γ1 Γ2 : ctx) (m : WfWorld) :
  m ⊨ ⟦CtxStar Γ1 Γ2⟧ ↔
  ∃ (m1 m2 : WfWorld) (Hc : world_compat m1 m2),
    res_product m1 m2 Hc ⊑ m ∧
    m1 ⊨ ⟦Γ1⟧ ∧ m2 ⊨ ⟦Γ2⟧.
Proof. Admitted.

Lemma res_models_impl_intro (m : WfWorld) (φ ψ : FQ) :
  (∀ m', m ⊑ m' →
         m' ⊨ φ → m' ⊨ ψ) →
  m ⊨ FImpl φ ψ.
Proof. Admitted.

Lemma res_models_fib_intro (m : WfWorld) (x : atom) (φ : FQ) :
  (∀ σ,
     ∀ Hproj : res_restrict m {[x]} σ,
     res_models_with_store σ
       (res_fiber_from_projection m {[x]} σ Hproj)
       φ) →
  m ⊨ FFib x φ.
Proof. Admitted.

Lemma res_models_forall_intro (m : WfWorld) (φ : FQ) :
  (∀ x : atom, x ∉ world_dom m →
  (∀ m' : WfWorld,
      world_dom m' = world_dom m ∪ {[x]} →
      res_restrict m' (world_dom m) = m →
      m' ⊨ formula_open 0 x φ)) →
  m ⊨ FForall φ.
Proof. Admitted.

Lemma res_models_exists_intro (m m' : WfWorld) (x : atom) (φ : FQ) :
  x ∉ world_dom m →
  world_dom m' = world_dom m ∪ {[x]} →
  res_restrict m' (world_dom m) = m →
  m' ⊨ formula_open 0 x φ →
  m ⊨ FExists φ.
Proof. Admitted.

Lemma ctx_res_models_mono (Γ : ctx) (m m' : WfWorld) :
  m ⊨ ⟦Γ⟧ →
  m ⊑ m' →
  m' ⊨ ⟦Γ⟧.
Proof. Admitted.
