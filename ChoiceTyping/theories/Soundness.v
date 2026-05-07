(** * ChoiceTyping.Soundness

    Soundness skeleton for the single declarative typing judgment. *)

From ChoiceTyping Require Export Typing.

(** ** Compatibility of satisfaction with monotone/antitone structure *)

Lemma res_models_impl_mono (φ ψ : FormulaQ) (m m' : WfWorld) :
  m ⊨ FImpl φ ψ →
  m ⊑ m' →
  m' ⊨ FImpl φ ψ.
Proof.
  intros Hmodel Hle.
  eapply res_models_kripke; eauto.
Qed.

Lemma res_models_and_mono (φ ψ : FormulaQ) (m m' : WfWorld) :
  m ⊨ FAnd φ ψ →
  m ⊑ m' →
  m' ⊨ FAnd φ ψ.
Proof.
  intros Hmodel Hle.
  eapply res_models_kripke; eauto.
Qed.

(** Kripke implication elimination at the current world. *)
Lemma res_models_impl_elim (m : WfWorld) (φ ψ : FormulaQ) :
  m ⊨ FImpl φ ψ →
  m ⊨ φ →
  m ⊨ ψ.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros [_ Himpl] Hφ.
  pose proof (res_models_with_store_fuel_irrel
    (formula_measure φ) (formula_measure φ + formula_measure ψ)
    ∅ m φ ltac:(lia) ltac:(simpl; lia) Hφ) as Hφ_big.
  pose proof (Himpl m ltac:(reflexivity) Hφ_big) as Hψ_big.
  eapply res_models_with_store_fuel_irrel; [| | exact Hψ_big]; simpl; lia.
Qed.

(** The semantic-subtyping case of the fundamental theorem. *)
Lemma fundamental_sub_case
    (Φ : primop_ctx) (Γ : ctx) (e : tm) (τ1 τ2 : choice_ty) :
  choice_typing_wf Γ e τ2 →
  sub_type Γ τ1 τ2 →
  (⟦Γ⟧ ⊫ ⟦τ1⟧ e) →
  ⟦Γ⟧ ⊫ ⟦τ2⟧ e.
Proof.
  intros Hwf Hsub IH m HΓ.
  destruct Hsub as [_ [_ [_ Hent]]].
  pose proof (choice_typing_wf_fv_tm_subset Γ e τ2 Hwf) as Hfv.
  pose proof (Hent e Hfv m HΓ) as Himpl.
  eapply res_models_impl_elim; [exact Himpl |].
  apply IH. exact HΓ.
Qed.

(** The context-subtyping case of the fundamental theorem. *)
Lemma fundamental_ctx_sub_case
    (Φ : primop_ctx) (Γ1 Γ2 : ctx) (e : tm) (τ : choice_ty) :
  ctx_sub (fv_tm e ∪ fv_cty τ) Γ1 Γ2 →
  (⟦Γ2⟧ ⊫ ⟦τ⟧ e) →
  ⟦Γ1⟧ ⊫ ⟦τ⟧ e.
Proof.
  intros Hsub IH m HΓ1.
  destruct Hsub as [_ [_ Hrestrict]].
  eapply res_models_kripke.
  - apply res_restrict_le.
  - apply IH. apply Hrestrict. exact HΓ1.
Qed.

(** The variable case is exactly the singleton context denotation. *)
Lemma fundamental_var_case (x : atom) (τ : choice_ty) :
  ⟦CtxBind x τ⟧ ⊫ ⟦τ⟧ (tret (vfvar x)).
Proof.
  intros m Hm. exact Hm.
Qed.

(** ** Fundamental theorem *)

Theorem Fundamental (Φ : primop_ctx) (Γ : ctx) (e : tm) (τ : choice_ty) :
  wf_primop_ctx Φ →
  has_choice_type Φ Γ e τ →
  ⟦Γ⟧ ⊫ ⟦τ⟧ e.
Proof. Admitted.

(** ** Corollaries

    The theorem statements follow the single typing judgment.  The proof
    bodies remain as admitted skeletons while the definition layer is being
    aligned with the paper. *)

Corollary safety (Φ : primop_ctx) (e : tm) (b : base_ty) :
  wf_primop_ctx Φ →
  has_choice_type Φ CtxEmpty e (CTOver b qual_top) →
  ∀ e', steps e e' → is_val e' ∨ ∃ e'', step e' e''.
Proof. Admitted.

Corollary coverage (Φ : primop_ctx) (e : tm) (b : base_ty) :
  wf_primop_ctx Φ →
  has_choice_type Φ CtxEmpty e (CTUnder b qual_top) →
  ∃ v, steps e (tret v).
Proof. Admitted.

Corollary refinement (Φ : primop_ctx) (e : tm) (b : base_ty) (φ : type_qualifier) :
  wf_primop_ctx Φ →
  has_choice_type Φ CtxEmpty e (CTOver b φ) →
  ∀ v, steps e (tret v) →
       ∃ x, qual_interp {[x := v]} (φ ^q^ x).
Proof. Admitted.

Corollary incorrectness (Φ : primop_ctx) (e : tm) (b : base_ty) (φ : type_qualifier) :
  wf_primop_ctx Φ →
  has_choice_type Φ CtxEmpty e (CTUnder b φ) →
  ∃ v x, steps e (tret v) ∧ qual_interp {[x := v]} (φ ^q^ x).
Proof. Admitted.

Corollary exact_result (Φ : primop_ctx) (e : tm) (b : base_ty) (c : constant) :
  wf_primop_ctx Φ →
  has_choice_type Φ CtxEmpty e (CTUnder b (b0:c= c)) →
  steps e (tret (vconst c)).
Proof. Admitted.

(** ** Structural soundness lemmas *)

Lemma denot_ctx_comma_split (Γ1 Γ2 : ctx) (m : WfWorld) :
  m ⊨ ⟦CtxComma Γ1 Γ2⟧ ↔ m ⊨ ⟦Γ1⟧ ∧ m ⊨ ⟦Γ2⟧.
Proof. apply denot_ctx_comma. Qed.

Lemma denot_ctx_star_split (Γ1 Γ2 : ctx) (m : WfWorld) :
  m ⊨ ⟦CtxStar Γ1 Γ2⟧ ↔
  ∃ (m1 m2 : WfWorld) (Hc : world_compat m1 m2),
    res_product m1 m2 Hc ⊑ m ∧
    m1 ⊨ ⟦Γ1⟧ ∧ m2 ⊨ ⟦Γ2⟧.
Proof. apply denot_ctx_star. Qed.

Lemma res_models_impl_intro (m : WfWorld) (φ ψ : FormulaQ) :
  formula_scoped_in_world ∅ m (FImpl φ ψ) →
  (∀ m', m ⊑ m' →
         m' ⊨ φ → m' ⊨ ψ) →
  m ⊨ FImpl φ ψ.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros Hscope Himpl. split; [exact Hscope |].
  intros m' Hle Hφ.
  pose proof (res_models_with_store_fuel_irrel
    (formula_measure φ + formula_measure ψ) (formula_measure φ)
    ∅ m' φ ltac:(simpl; lia) ltac:(lia) Hφ) as Hφ_exact.
  pose proof (Himpl m' Hle Hφ_exact) as Hψ_exact.
  eapply res_models_with_store_fuel_irrel; [| | exact Hψ_exact]; simpl; lia.
Qed.

Lemma res_models_fib_intro (m : WfWorld) (x : atom) (φ : FormulaQ) :
  formula_scoped_in_world ∅ m (FFib x φ) →
  (∀ σ,
     ∀ Hproj : res_restrict m {[x]} σ,
     res_models_with_store σ
       (res_fiber_from_projection m {[x]} σ Hproj)
       φ) →
  m ⊨ FFib x φ.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros Hscope Hfib. split; [exact Hscope |].
  split.
  - set_solver.
  - intros σ Hproj.
    rewrite map_empty_union.
    eapply res_models_with_store_fuel_irrel; [| | exact (Hfib σ Hproj)];
      simpl; lia.
Qed.

Lemma res_models_forall_intro (m : WfWorld) (x : atom) (φ : FormulaQ) :
  formula_scoped_in_world ∅ m (FForall x φ) →
  (∃ L : aset,
    world_dom m ⊆ L ∧
    ∀ y : atom,
      y ∉ L →
      ∀ m' : WfWorld,
        world_dom m' = world_dom m ∪ {[y]} →
        res_restrict m' (world_dom m) = m →
        m' ⊨ formula_rename_atom x y φ) →
  m ⊨ FForall x φ.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros Hscope [L [HL Hforall]]. split; [exact Hscope |].
  exists L. split; [exact HL |].
  intros y Hy m' Hdom Hrestr.
  eapply res_models_with_store_fuel_irrel; [| | exact (Hforall y Hy m' Hdom Hrestr)];
    rewrite ?formula_rename_preserves_measure; simpl; lia.
Qed.

Lemma res_models_exists_intro (m : WfWorld) (x : atom) (φ : FormulaQ) :
  formula_scoped_in_world ∅ m (FExists x φ) →
  (∃ L : aset,
    world_dom m ⊆ L ∧
    ∀ y : atom,
      y ∉ L →
      ∃ m' : WfWorld,
        world_dom m' = world_dom m ∪ {[y]} ∧
        res_restrict m' (world_dom m) = m ∧
        m' ⊨ formula_rename_atom x y φ) →
  m ⊨ FExists x φ.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros Hscope [L [HL Hexists]]. split; [exact Hscope |].
  exists L. split; [exact HL |].
  intros y Hy.
  destruct (Hexists y Hy) as [m' [Hdom [Hrestr Hφ]]].
  exists m'. split; [exact Hdom |]. split; [exact Hrestr |].
  eapply res_models_with_store_fuel_irrel; [| | exact Hφ];
    rewrite ?formula_rename_preserves_measure; simpl; lia.
Qed.

Lemma ctx_res_models_mono (Γ : ctx) (m m' : WfWorld) :
  m ⊨ ⟦Γ⟧ →
  m ⊑ m' →
  m' ⊨ ⟦Γ⟧.
Proof.
  intros Hmodel Hle.
  eapply res_models_kripke; eauto.
Qed.
