(** * ChoiceType.Denotation

    Denotational semantics for the choice type system (§1.5 of the paper).

    The interpretation is given as formulas in [Choice Logic] whose atoms are
    logic qualifiers.  Core expressions are embedded through
    [expr_logic_qual], and type qualifiers are embedded through
    [lift_type_qualifier_to_logic] after they have been opened to closed
    atom-based qualifiers.

    The satisfaction notation [m ⊨ φ] is the central judgment used by
    the typing rules and the fundamental theorem. *)

From ChoiceType Require Export Syntax.

(** ** ChoiceLogic satisfaction, instantiated for qualifiers *)

(** Local abbreviation for the ChoiceType formula instantiation.  The exported
    name from [Prelude] is [FormulaQ]. *)
Local Notation FQ := FormulaQ.

(** Satisfaction: [m ⊨ φ]  ↔  [res_models m φ] *)
Notation "m ⊨ φ" :=
  (res_models m φ)
  (at level 70, format "m  ⊨  φ").

(** Entailment shorthand: [φ ⊫ ψ]  ↔  [∀ m, m ⊨ φ → m ⊨ ψ] *)
Notation "φ ⊫ ψ" :=
  (entails φ ψ)
  (at level 85, ψ at level 84, no associativity).

(** ** Logic atoms and fresh variable helpers for denotation *)

Definition fib_vars (X : aset) (p : FQ) : FQ :=
  set_fold FFib p X.

Definition expr_logic_qual (e : tm) (ν : atom) : logic_qualifier :=
  lqual (stale e ∪ {[ν]}) (fun σ (w : WfWorld) =>
    ∀ σw,
      (w : World) σw →
      ∃ v,
        σw !! ν = Some v ∧
        subst_map σw (subst_map σ e) →* tret v).

(** ** Type measure for denotation fuel

    As in HATs' denotation, the first argument of [denot_ty_fuel] is an
    over-approximation of the syntactic size of the type.  This lets the
    denotation recurse on opened locally-nameless bodies such as
    [{0 ~> x} τ], which are not syntactic subterms accepted by Rocq's
    structural termination checker. *)
Fixpoint cty_measure (τ : choice_ty) : nat :=
  match τ with
  | CTOver _ _ | CTUnder _ _ => 1
  | CTInter τ1 τ2
  | CTUnion τ1 τ2
  | CTSum τ1 τ2
  | CTArrow τ1 τ2
  | CTWand τ1 τ2 => 1 + cty_measure τ1 + cty_measure τ2
  end.

Lemma cty_measure_gt_0 τ : cty_measure τ > 0.
Proof. induction τ; simpl; lia. Qed.

Lemma cty_open_preserves_measure τ k x :
  cty_measure ({k ~> x} τ) = cty_measure τ.
Proof. induction τ in k |- *; simpl; eauto; lia. Qed.

(** ** Type denotation

    [denot_ty_fuel gas D τ e] encodes the proposition "expression [e] has
    type [τ]" as a Choice Logic formula.  The finite set [D] is an avoidance
    set for generated binder representatives.  These names only make the
    syntax concrete: [FForall]'s cofinite semantics interprets each binder by
    renaming the representative to every sufficiently fresh atom. *)

Fixpoint denot_ty_fuel (gas : nat) (D : aset) (τ : choice_ty) (e : tm) : FQ :=
  match gas with
  | 0 => FFalse
  | S gas' =>
  match τ with

  (** {ν:b | φ}  ≝  ∀ν. ⟦e⟧_ν ⇒ ∀_{FV(φ)} ◁φ
      [fib_vars (fv φ)] iterates the single-variable fiber modality over
      φ's free variables. *)
  | CTOver b φ =>
      fresh_forall (D ∪ fv_tm e ∪ qual_dom φ) (fun ν =>
      let φν := qual_open_atom 0 ν φ in
        (FImpl (FAtom (expr_logic_qual e ν))
               (fib_vars (qual_dom φν) (FOver (FAtom (lift_type_qualifier_to_logic φν))))))

  (** [ν:b | φ]  ≝  ∀ν. ⟦e⟧_ν ⇒ ∀_{FV(φ)} ▷φ *)
  | CTUnder b φ =>
      fresh_forall (D ∪ fv_tm e ∪ qual_dom φ) (fun ν =>
      let φν := qual_open_atom 0 ν φ in
        (FImpl (FAtom (expr_logic_qual e ν))
               (fib_vars (qual_dom φν) (FUnder (FAtom (lift_type_qualifier_to_logic φν))))))

  (** τ1 ⊓ τ2  ≝  ⟦τ1⟧ e ∧ ⟦τ2⟧ e *)
  | CTInter τ1 τ2 =>
      FAnd (denot_ty_fuel gas' D τ1 e) (denot_ty_fuel gas' D τ2 e)

  (** τ1 ⊔ τ2  ≝  ⟦τ1⟧ e ∨ ⟦τ2⟧ e *)
  | CTUnion τ1 τ2 =>
      FOr (denot_ty_fuel gas' D τ1 e) (denot_ty_fuel gas' D τ2 e)

  (** τ1 ⊕ τ2  ≝  ⟦τ1⟧ e ⊕ ⟦τ2⟧ e *)
  | CTSum τ1 τ2 =>
      FPlus (denot_ty_fuel gas' D τ1 e) (denot_ty_fuel gas' D τ2 e)

  (** τ_x →, τ  ≝  ∀y. ⟦e⟧_y ⇒ ∀{y}.∀x.(⟦τ_x⟧ x ⇒ ⟦τ[x]⟧ (y x)). *)
  | CTArrow τx τ =>
      let Dy := D ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ in
      fresh_forall Dy (fun y =>
      let Dx := {[y]} ∪ Dy in
        (FImpl
          (FAtom (expr_logic_qual e y))
          (fresh_forall Dx (fun x =>
          let D2 := {[x]} ∪ Dx in
            FFib y
              (FImpl
                (denot_ty_fuel gas' D2 τx (tret (vfvar x)))
                (denot_ty_fuel gas' D2 ({0 ~> x} τ)
                   (tapp (vfvar y) (vfvar x))))))))

  (** τ_x ⊸ τ  ≝  ∀y. ⟦e⟧_y ⇒ ∀{y}.∀x.(⟦τ_x⟧ x −∗ ⟦τ[x]⟧ (y x)). *)
  | CTWand τx τ =>
      let Dy := D ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ in
      fresh_forall Dy (fun y =>
      let Dx := {[y]} ∪ Dy in
        (FImpl
          (FAtom (expr_logic_qual e y))
          (fresh_forall Dx (fun x =>
          let D2 := {[x]} ∪ Dx in
            FFib y
              (FWand
                (denot_ty_fuel gas' D2 τx (tret (vfvar x)))
                (denot_ty_fuel gas' D2 ({0 ~> x} τ)
                   (tapp (vfvar y) (vfvar x))))))))

  end
  end.

Definition denot_ty_avoiding (D : aset) (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_fuel (cty_measure τ) D τ e.

Definition denot_ty (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_avoiding (fv_cty τ ∪ fv_tm e) τ e.

(** ** Context denotation

    [denot_ctx Γ : FQ] is the formula that holds when [Γ] is "satisfied". *)
Fixpoint denot_ctx (Γ : ctx) : FQ :=
  match Γ with
  | CtxEmpty        => FTrue
  | CtxBind x τ    => denot_ty τ (tret (vfvar x))
  | CtxComma Γ1 Γ2 => FAnd  (denot_ctx Γ1) (denot_ctx Γ2)
  | CtxStar  Γ1 Γ2 => FStar (denot_ctx Γ1) (denot_ctx Γ2)
  | CtxSum   Γ1 Γ2 => FPlus (denot_ctx Γ1) (denot_ctx Γ2)
  end.

(** ** Typeclass instances for [⟦⟧] notation *)

#[global] Instance denot_cty_inst :
    Denotation choice_ty (tm → FQ) := denot_ty.
#[global] Instance denot_ctx_inst :
    Denotation ctx FQ := denot_ctx.
Arguments denot_cty_inst /.
Arguments denot_ctx_inst /.

(** With these instances:
      [⟦τ⟧ e]  unfolds to [denot_ty τ e]
      [⟦Γ⟧]    unfolds to [denot_ctx Γ]              *)

(** ** Key semantic lemmas *)

Local Ltac solve_ctx_fuel Γ1 Γ2 :=
  unfold denote, denot_ctx_inst in *;
  simpl;
  repeat rewrite Nat.add_0_l;
  repeat rewrite Nat.add_0_r;
  pose proof (formula_measure_pos (denot_ctx Γ1));
  pose proof (formula_measure_pos (denot_ctx Γ2));
  lia.

Local Ltac change_ctx_fuel H Γ1 Γ2 :=
  match type of H with
  | res_models_with_store_fuel ?gas ?ρ ?m ?φ =>
      eapply (res_models_with_store_fuel_irrel gas _ ρ m φ);
      [solve_ctx_fuel Γ1 Γ2 | solve_ctx_fuel Γ1 Γ2 | exact H]
  end.

(** Monotonicity: if m ⊨ ⟦Γ⟧ and m ≤ m', then m' ⊨ ⟦Γ⟧ for comma contexts. *)
Lemma denot_ctx_mono_comma (Γ : ctx) m m' :
  m ⊨ ⟦Γ⟧ →
  m ⊑ m' →
  m' ⊨ ⟦Γ⟧.
Proof.
  unfold denot_ctx_inst, res_models, res_models_with_store.
  intros Hmodels Hle. eapply res_models_with_store_fuel_kripke; eauto.
Qed.

(** The context denotation of a comma-context distributes over conjunction. *)
Lemma denot_ctx_comma Γ1 Γ2 m :
  m ⊨ ⟦CtxComma Γ1 Γ2⟧ ↔ m ⊨ ⟦Γ1⟧ ∧ m ⊨ ⟦Γ2⟧.
Proof.
  unfold denot_ctx_inst, res_models, res_models_with_store. simpl.
  split.
  - intros [Hscope [HΓ1 HΓ2]]. split.
    + change_ctx_fuel HΓ1 Γ1 Γ2.
    + change_ctx_fuel HΓ2 Γ1 Γ2.
  - intros [HΓ1 HΓ2]. split.
    + unfold formula_scoped_in_world in *. simpl.
      pose proof (res_models_with_store_fuel_scoped _ ∅ m (denot_ctx Γ1) HΓ1).
      pose proof (res_models_with_store_fuel_scoped _ ∅ m (denot_ctx Γ2) HΓ2).
      set_solver.
    + split.
      * change_ctx_fuel HΓ1 Γ1 Γ2.
      * change_ctx_fuel HΓ2 Γ1 Γ2.
Qed.

(** The context denotation of a star-context distributes over FStar. *)
Lemma denot_ctx_star Γ1 Γ2 m :
  m ⊨ ⟦CtxStar Γ1 Γ2⟧ ↔
  ∃ (m1 m2 : WfWorld) (Hc : world_compat m1 m2),
    res_product m1 m2 Hc ⊑ m ∧
    m1 ⊨ ⟦Γ1⟧ ∧ m2 ⊨ ⟦Γ2⟧.
Proof.
  unfold denot_ctx_inst, res_models, res_models_with_store. simpl.
  split.
  - intros [_ [m1 [m2 [Hc [Hprod [HΓ1 HΓ2]]]]]].
    exists m1, m2, Hc. split; [exact Hprod |]. split.
    + change_ctx_fuel HΓ1 Γ1 Γ2.
    + change_ctx_fuel HΓ2 Γ1 Γ2.
  - intros [m1 [m2 [Hc [Hprod [HΓ1 HΓ2]]]]].
    split.
    + unfold formula_scoped_in_world in *. simpl.
      pose proof (res_models_with_store_fuel_scoped _ ∅ m1 (denot_ctx Γ1) HΓ1).
      pose proof (res_models_with_store_fuel_scoped _ ∅ m2 (denot_ctx Γ2) HΓ2).
      pose proof (raw_le_dom _ _ Hprod). set_solver.
    + exists m1, m2, Hc. split; [exact Hprod |]. split.
      * change_ctx_fuel HΓ1 Γ1 Γ2.
      * change_ctx_fuel HΓ2 Γ1 Γ2.
Qed.

(** The context denotation of a sum-context distributes over FPlus. *)
Lemma denot_ctx_sum Γ1 Γ2 m :
  m ⊨ ⟦CtxSum Γ1 Γ2⟧ ↔
  ∃ (m1 m2 : WfWorld) (Hdef : raw_sum_defined m1 m2),
    res_sum m1 m2 Hdef ⊑ m ∧
    m1 ⊨ ⟦Γ1⟧ ∧ m2 ⊨ ⟦Γ2⟧.
Proof.
  unfold denot_ctx_inst, res_models, res_models_with_store. simpl.
  split.
  - intros [_ [m1 [m2 [Hdef [Hsum [HΓ1 HΓ2]]]]]].
    exists m1, m2, Hdef. split; [exact Hsum |]. split.
    + change_ctx_fuel HΓ1 Γ1 Γ2.
    + change_ctx_fuel HΓ2 Γ1 Γ2.
  - intros [m1 [m2 [Hdef [Hsum [HΓ1 HΓ2]]]]].
    split.
    + unfold formula_scoped_in_world in *. simpl.
      pose proof (res_models_with_store_fuel_scoped _ ∅ m1 (denot_ctx Γ1) HΓ1) as Hscope1.
      pose proof (res_models_with_store_fuel_scoped _ ∅ m2 (denot_ctx Γ2) HΓ2) as Hscope2.
      pose proof (raw_le_dom _ _ Hsum) as Hdom_sum_m.
      unfold raw_sum_defined in Hdef. simpl in Hdom_sum_m.
      intros z Hz. apply elem_of_union in Hz as [Hzempty | Hzfv]; [set_solver |].
      apply elem_of_union in Hzfv as [Hz | Hz].
      * apply Hdom_sum_m. apply Hscope1. set_solver.
      * apply Hdom_sum_m. rewrite Hdef. apply Hscope2. set_solver.
    + exists m1, m2, Hdef. split; [exact Hsum |]. split.
      * change_ctx_fuel HΓ1 Γ1 Γ2.
      * change_ctx_fuel HΓ2 Γ1 Γ2.
Qed.

(** [⟦CtxBind x τ⟧] is [⟦τ⟧ (return x)]. *)
Lemma denot_ctx_bind x τ m :
  m ⊨ ⟦CtxBind x τ⟧ ↔ m ⊨ denot_ty τ (tret (vfvar x)).
Proof. reflexivity. Qed.
