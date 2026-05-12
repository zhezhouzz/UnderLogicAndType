(** * ChoiceType.DenotationType

    Choice-type denotation and formula-locality lemmas. *)

From LocallyNameless Require Import Tactics.
From CoreLang Require Import Instantiation InstantiationProps LocallyNamelessProps
  OperationalProps Sugar.
From ChoiceType Require Export DenotationExprProps.
From ChoiceType Require Import BasicStore BasicTyping LocallyNamelessProps.

Local Notation FQ := FormulaQ.

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

Lemma cty_swap_preserves_measure x y τ :
  cty_measure (cty_swap_atom x y τ) = cty_measure τ.
Proof. induction τ; simpl; eauto; lia. Qed.

(** ** Type denotation

    [denot_ty_fuel_result gas Σ τ e] packages the meta-level obligations and
    the Choice Logic formula for "expression [e] has type [τ]" under erased
    basic environment [Σ].

    The field [denot_ty_formula] is the old formula denotation.  The other
    fields deliberately remain at the Rocq [Prop] level: they are needed by
    recursive proof obligations such as [tlet], but encoding strong totality
    inside Choice Logic would make the logic depend on the full operational
    semantics.

    [denot_ty_fuel gas Σ τ e] is kept below as a projection to
    [denot_ty_formula], preserving the existing formula-level interface.
    Expression-result atoms and fresh representatives are driven by [dom Σ].
    The regularity assumptions that [fv_tm e] and [fv_cty τ] are contained in
    [dom Σ] live at the Rocq [Prop] level, not inside the logic. *)

Record denot_ty_result := {
  basic_typing : Prop;
  closed_resource : WfWorld → Prop;
  strong_total : WfWorld → Prop;
  denot_ty_formula : FQ;
}.

Definition mk_denot_ty_result
    (Σ : gmap atom ty) (τ : choice_ty) (e : tm) (φ : FQ)
    : denot_ty_result := {|
  basic_typing := basic_choice_ty (dom Σ) τ ∧ Σ ⊢ₑ e ⋮ erase_ty τ;
  closed_resource := fun m => world_closed_on (dom Σ) m;
  strong_total := fun m => expr_total_on (dom Σ) e m;
  denot_ty_formula := φ;
|}.

Definition denot_ty_result_models (R : denot_ty_result) (m : WfWorld) : Prop :=
  basic_typing R ∧ closed_resource R m ∧ strong_total R m ∧
  m ⊨ denot_ty_formula R.

Fixpoint denot_ty_fuel_result
    (gas : nat) (Σ : gmap atom ty) (τ : choice_ty) (e : tm)
    : denot_ty_result :=
  match gas with
  | 0 => mk_denot_ty_result Σ τ e FFalse
  | S gas' =>
  match τ with

  (** {ν:b | φ}  ≝  ∀ν. ⟦e⟧_ν ⇒ ∀_{FV(φ)} ◁φ
      [fib_vars (fv φ)] iterates the single-variable fiber modality over
      φ's free variables. *)
  | CTOver b φ =>
      mk_denot_ty_result Σ τ e (FExprContIn Σ e (fun ν =>
      let φν := qual_open_atom 0 ν φ in
        FAnd
          (basic_world_formula (<[ν := TBase b]> Σ) ({[ν]} ∪ qual_dom φν))
          (fib_vars (qual_dom φν)
            (FOver (FTypeQualifier φν)))))

  (** [ν:b | φ]  ≝  ∀ν. ⟦e⟧_ν ⇒ ∀_{FV(φ)} ▷φ *)
  | CTUnder b φ =>
      mk_denot_ty_result Σ τ e (FExprContIn Σ e (fun ν =>
      let φν := qual_open_atom 0 ν φ in
        FAnd
          (basic_world_formula (<[ν := TBase b]> Σ) ({[ν]} ∪ qual_dom φν))
          (fib_vars (qual_dom φν)
            (FUnder (FTypeQualifier φν)))))

  (** τ1 ⊓ τ2  ≝  ⟦τ1⟧ e ∧ ⟦τ2⟧ e *)
  | CTInter τ1 τ2 =>
      let R1 := denot_ty_fuel_result gas' Σ τ1 e in
      let R2 := denot_ty_fuel_result gas' Σ τ2 e in
      mk_denot_ty_result Σ τ e
        (FAnd (denot_ty_formula R1) (denot_ty_formula R2))

  (** τ1 ⊔ τ2  ≝  ⟦τ1⟧ e ∨ ⟦τ2⟧ e *)
  | CTUnion τ1 τ2 =>
      let R1 := denot_ty_fuel_result gas' Σ τ1 e in
      let R2 := denot_ty_fuel_result gas' Σ τ2 e in
      mk_denot_ty_result Σ τ e
        (FOr (denot_ty_formula R1) (denot_ty_formula R2))

  (** τ1 ⊕ τ2  ≝  ⟦τ1⟧ e ⊕ ⟦τ2⟧ e *)
  | CTSum τ1 τ2 =>
      let R1 := denot_ty_fuel_result gas' Σ τ1 e in
      let R2 := denot_ty_fuel_result gas' Σ τ2 e in
      mk_denot_ty_result Σ τ e
        (FPlus (denot_ty_formula R1) (denot_ty_formula R2))

  (** τ_x →, τ  ≝  ∀x.(⟦τ_x⟧ x ⇒ ⟦τ[x]⟧ (e x)).

      The application [e x] is represented by the derived core term
      [tapp_tm e (vfvar x)], which first evaluates [e] to a function value and
      then applies it to [x].  We intentionally do not allocate a separate
      logic coordinate for the function result here. *)
  | CTArrow τx τ =>
      mk_denot_ty_result Σ (CTArrow τx τ) e (fresh_forall (dom Σ) (fun x =>
        let Σx := <[x := erase_ty τx]> Σ in
        let Rarg := denot_ty_fuel_result gas' Σx τx (tret (vfvar x)) in
        let Rbody := denot_ty_fuel_result gas' Σx ({0 ~> x} τ)
          (tapp_tm e (vfvar x)) in
          FImpl
            (denot_ty_formula Rarg)
            (denot_ty_formula Rbody)))

  (** τ_x ⊸ τ  ≝  ∀x.(⟦τ_x⟧ x −∗ ⟦τ[x]⟧ (e x)). *)
  | CTWand τx τ =>
      mk_denot_ty_result Σ (CTWand τx τ) e (fresh_forall (dom Σ) (fun x =>
        let Σx := <[x := erase_ty τx]> Σ in
        let Rarg := denot_ty_fuel_result gas' Σx τx (tret (vfvar x)) in
        let Rbody := denot_ty_fuel_result gas' Σx ({0 ~> x} τ)
          (tapp_tm e (vfvar x)) in
          FWand
            (denot_ty_formula Rarg)
            (denot_ty_formula Rbody)))

  end
  end.

Definition denot_ty_fuel
    (gas : nat) (Σ : gmap atom ty) (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_formula (denot_ty_fuel_result gas Σ τ e).

Lemma denot_ty_fuel_result_basic_typing gas Σ τ e :
  basic_typing (denot_ty_fuel_result gas Σ τ e) ↔
  basic_choice_ty (dom Σ) τ ∧ Σ ⊢ₑ e ⋮ erase_ty τ.
Proof.
  destruct gas as [|gas]; [reflexivity |].
  destruct τ; reflexivity.
Qed.

Lemma denot_ty_fuel_result_closed_resource gas Σ τ e m :
  closed_resource (denot_ty_fuel_result gas Σ τ e) m ↔
  world_closed_on (dom Σ) m.
Proof.
  destruct gas as [|gas]; [reflexivity |].
  destruct τ; reflexivity.
Qed.

Lemma denot_ty_fuel_result_strong_total gas Σ τ e m :
  strong_total (denot_ty_fuel_result gas Σ τ e) m ↔
  expr_total_on (dom Σ) e m.
Proof.
  destruct gas as [|gas]; [reflexivity |].
  destruct τ; reflexivity.
Qed.

Lemma denot_ty_fuel_result_formula gas Σ τ e :
  denot_ty_formula (denot_ty_fuel_result gas Σ τ e) =
  denot_ty_fuel gas Σ τ e.
Proof. reflexivity. Qed.

Definition denot_ty_on
    (Σ : gmap atom ty) (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_fuel (cty_measure τ) Σ τ e.

Definition denot_ty_under (Σ : gmap atom ty) (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_on Σ τ e.

Definition denot_ty (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_under ∅ τ e.

Definition denot_ty_in_ctx (Γ : ctx) (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_under (erase_ctx Γ) τ e.

Definition erase_ctx_under (Σ : gmap atom ty) (Γ : ctx) : gmap atom ty :=
  Σ ∪ erase_ctx Γ.

Definition denot_ty_in_ctx_under
    (Σ : gmap atom ty) (Γ : ctx) (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_on (erase_ctx_under Σ Γ) τ e.

Definition denot_ty_total_in_ctx_under
    (Σ : gmap atom ty) (Γ : ctx) (τ : choice_ty) (e : tm)
    (m : WfWorld) : Prop :=
  m ⊨ denot_ty_in_ctx_under Σ Γ τ e ∧
  expr_total_on (dom (erase_ctx_under Σ Γ)) e m.

Definition entails_total (φ : FQ) (P : WfWorld → Prop) : Prop :=
  ∀ m, m ⊨ φ → P m.

Lemma denot_ty_total_formula Σ Γ τ e m :
  denot_ty_total_in_ctx_under Σ Γ τ e m →
  m ⊨ denot_ty_in_ctx_under Σ Γ τ e.
Proof. intros [H _]. exact H. Qed.

Lemma denot_ty_total_expr_total Σ Γ τ e m :
  denot_ty_total_in_ctx_under Σ Γ τ e m →
  expr_total_on (dom (erase_ctx_under Σ Γ)) e m.
Proof. intros [_ H]. exact H. Qed.

Definition ty_env_agree_on (X : aset) (Σ1 Σ2 : gmap atom ty) : Prop :=
  ∀ x, x ∈ X → Σ1 !! x = Σ2 !! x.

Lemma ty_env_agree_on_mono X Y Σ1 Σ2 :
  X ⊆ Y →
  ty_env_agree_on Y Σ1 Σ2 →
  ty_env_agree_on X Σ1 Σ2.
Proof. unfold ty_env_agree_on. hauto. Qed.

Lemma ty_env_agree_on_insert_same X Σ1 Σ2 x T :
  ty_env_agree_on (X ∖ {[x]}) Σ1 Σ2 →
  ty_env_agree_on X (<[x := T]> Σ1) (<[x := T]> Σ2).
Proof.
  intros Hagree z Hz.
  destruct (decide (z = x)) as [->|Hne].
  - rewrite !(lookup_insert_eq _ x T). reflexivity.
  - rewrite !lookup_insert_ne by congruence.
    apply Hagree. set_solver.
Qed.

Lemma ty_env_agree_on_insert_same_keep X Σ1 Σ2 x T :
  ty_env_agree_on X Σ1 Σ2 →
  ty_env_agree_on (X ∪ {[x]}) (<[x := T]> Σ1) (<[x := T]> Σ2).
Proof.
  intros Hagree.
  apply ty_env_agree_on_insert_same.
  intros z Hz. apply Hagree. set_solver.
Qed.

Lemma ty_env_agree_on_open_qual_result D Σ1 Σ2 b φ ν :
  ty_env_agree_on (D ∪ qual_dom φ) Σ1 Σ2 →
  ty_env_agree_on ({[ν]} ∪ qual_dom (qual_open_atom 0 ν φ))
    (<[ν := TBase b]> Σ1) (<[ν := TBase b]> Σ2).
Proof.
  intros Hagree z Hz.
  destruct (decide (z = ν)) as [->|Hne].
  - rewrite !(lookup_insert_eq _ ν (TBase b)). reflexivity.
  - rewrite !lookup_insert_ne by congruence.
    apply Hagree.
    pose proof (qual_open_atom_dom_subset 0 ν φ z) as Hdom.
    set_solver.
Qed.

Definition formula_equiv (φ ψ : FQ) : Prop :=
  (φ ⊫ ψ) ∧ (ψ ⊫ φ).

Notation "φ '⊣⊢' ψ" := (formula_equiv φ ψ)
  (at level 85, no associativity).

Definition formula_store_equiv (φ ψ : FQ) : Prop :=
  ∀ ρ m, res_models_with_store ρ m φ ↔ res_models_with_store ρ m ψ.

Lemma formula_equiv_refl φ : φ ⊣⊢ φ.
Proof. unfold formula_equiv, entails. hauto. Qed.

Lemma formula_equiv_sym φ ψ :
  φ ⊣⊢ ψ → ψ ⊣⊢ φ.
Proof. unfold formula_equiv. hauto. Qed.

Lemma formula_equiv_trans φ ψ χ :
  φ ⊣⊢ ψ → ψ ⊣⊢ χ → φ ⊣⊢ χ.
Proof. unfold formula_equiv, entails. hauto. Qed.

Lemma formula_store_equiv_refl φ : formula_store_equiv φ φ.
Proof. unfold formula_store_equiv. hauto. Qed.

Lemma formula_store_equiv_sym φ ψ :
  formula_store_equiv φ ψ → formula_store_equiv ψ φ.
Proof. unfold formula_store_equiv. hauto. Qed.

Lemma formula_store_equiv_trans φ ψ χ :
  formula_store_equiv φ ψ →
  formula_store_equiv ψ χ →
  formula_store_equiv φ χ.
Proof. unfold formula_store_equiv. hauto. Qed.

Lemma formula_store_equiv_and φ1 φ2 ψ1 ψ2 :
  formula_fv φ1 = formula_fv ψ1 →
  formula_fv φ2 = formula_fv ψ2 →
  formula_store_equiv φ1 ψ1 →
  formula_store_equiv φ2 ψ2 →
  formula_store_equiv (FAnd φ1 φ2) (FAnd ψ1 ψ2).
Proof.
  intros Hfv1 Hfv2 H1 H2 ρ m.
  unfold res_models_with_store. simpl. split; intros [Hscope Hmodel]; split.
  - unfold formula_scoped_in_world in *. simpl in *.
    rewrite <- Hfv1, <- Hfv2. exact Hscope.
  - destruct Hmodel as [Hφ1 Hφ2]. split.
    + pose proof (proj1 (H1 ρ m)) as H.
      assert (Hφ1_exact : res_models_with_store ρ m φ1).
      { models_fuel_irrel Hφ1. }
      models_fuel_irrel (H Hφ1_exact).
    + pose proof (proj1 (H2 ρ m)) as H.
      assert (Hφ2_exact : res_models_with_store ρ m φ2).
      { models_fuel_irrel Hφ2. }
      models_fuel_irrel (H Hφ2_exact).
  - unfold formula_scoped_in_world in *. simpl in *.
    rewrite Hfv1, Hfv2. exact Hscope.
  - destruct Hmodel as [Hψ1 Hψ2]. split.
    + pose proof (proj2 (H1 ρ m)) as H.
      assert (Hψ1_exact : res_models_with_store ρ m ψ1).
      { models_fuel_irrel Hψ1. }
      models_fuel_irrel (H Hψ1_exact).
    + pose proof (proj2 (H2 ρ m)) as H.
      assert (Hψ2_exact : res_models_with_store ρ m ψ2).
      { models_fuel_irrel Hψ2. }
      models_fuel_irrel (H Hψ2_exact).
Qed.

Lemma formula_store_equiv_over φ ψ :
  formula_fv φ = formula_fv ψ →
  formula_store_equiv φ ψ →
  formula_store_equiv (FOver φ) (FOver ψ).
Proof.
  intros Hfv Heq ρ m.
  unfold res_models_with_store. simpl. split; intros [Hscope [m0 [Hsub Hφ]]]; split.
  - unfold formula_scoped_in_world in *. simpl in *. rewrite <- Hfv. exact Hscope.
  - exists m0. split; [exact Hsub |].
    pose proof (proj1 (Heq ρ m0)) as H.
    assert (Hφ_exact : res_models_with_store ρ m0 φ).
    { models_fuel_irrel Hφ. }
    models_fuel_irrel (H Hφ_exact).
  - unfold formula_scoped_in_world in *. simpl in *. rewrite Hfv. exact Hscope.
  - exists m0. split; [exact Hsub |].
    pose proof (proj2 (Heq ρ m0)) as H.
    assert (Hψ_exact : res_models_with_store ρ m0 ψ).
    { models_fuel_irrel Hφ. }
    models_fuel_irrel (H Hψ_exact).
Qed.

Lemma formula_store_equiv_under φ ψ :
  formula_fv φ = formula_fv ψ →
  formula_store_equiv φ ψ →
  formula_store_equiv (FUnder φ) (FUnder ψ).
Proof.
  intros Hfv Heq ρ m.
  unfold res_models_with_store. simpl. split; intros [Hscope [m0 [Hsub Hφ]]]; split.
  - unfold formula_scoped_in_world in *. simpl in *. rewrite <- Hfv. exact Hscope.
  - exists m0. split; [exact Hsub |].
    pose proof (proj1 (Heq ρ m0)) as H.
    assert (Hφ_exact : res_models_with_store ρ m0 φ).
    { models_fuel_irrel Hφ. }
    models_fuel_irrel (H Hφ_exact).
  - unfold formula_scoped_in_world in *. simpl in *. rewrite Hfv. exact Hscope.
  - exists m0. split; [exact Hsub |].
    pose proof (proj2 (Heq ρ m0)) as H.
    assert (Hψ_exact : res_models_with_store ρ m0 ψ).
    { models_fuel_irrel Hφ. }
    models_fuel_irrel (H Hψ_exact).
Qed.

Lemma formula_store_equiv_fib x φ ψ :
  formula_fv φ = formula_fv ψ →
  formula_store_equiv φ ψ →
  formula_store_equiv (FFib x φ) (FFib x ψ).
Proof.
  intros Hfv Heq ρ m.
  unfold res_models_with_store. simpl. split; intros [Hscope [Hdisj Hfib]]; split.
  - unfold formula_scoped_in_world in *. simpl in *. rewrite <- Hfv. exact Hscope.
  - split; [exact Hdisj |].
    intros σ Hproj.
    pose proof (Hfib σ Hproj) as Hφ.
    pose proof (proj1 (Heq (ρ ∪ σ)
      (res_fiber_from_projection m {[x]} σ Hproj))) as H.
    assert (Hφ_exact : res_models_with_store (ρ ∪ σ)
      (res_fiber_from_projection m {[x]} σ Hproj) φ).
    { models_fuel_irrel Hφ. }
    models_fuel_irrel (H Hφ_exact).
  - unfold formula_scoped_in_world in *. simpl in *. rewrite Hfv. exact Hscope.
  - split; [exact Hdisj |].
    intros σ Hproj.
    pose proof (Hfib σ Hproj) as Hψ.
    pose proof (proj2 (Heq (ρ ∪ σ)
      (res_fiber_from_projection m {[x]} σ Hproj))) as H.
    assert (Hψ_exact : res_models_with_store (ρ ∪ σ)
      (res_fiber_from_projection m {[x]} σ Hproj) ψ).
    { models_fuel_irrel Hψ. }
    models_fuel_irrel (H Hψ_exact).
Qed.

Lemma formula_store_equiv_fib_commute_dir x y (φ : FQ) ρ m :
  x ≠ y →
  res_models_with_store ρ m (FFib x (FFib y φ)) →
  res_models_with_store ρ m (FFib y (FFib x φ)).
Proof.
  intros Hxy Hm.
  unfold res_models_with_store in Hm. simpl in Hm.
  destruct Hm as [Hscope [Hdisj Hfib]].
  assert (Hxdom : x ∈ world_dom (m : World)).
  { unfold formula_scoped_in_world in Hscope. simpl in Hscope. set_solver. }
  assert (Hydom : y ∈ world_dom (m : World)).
  { unfold formula_scoped_in_world in Hscope. simpl in Hscope. set_solver. }
  set (R := fun ρ m => res_models_with_store ρ m φ).
  assert (Hoblxy : fib_vars_obligation_step x (fib_vars_obligation_step y R) ρ m).
  {
    unfold fib_vars_obligation_step. split; [exact Hdisj |].
    intros σx Hprojx.
    specialize (Hfib σx Hprojx).
    unfold R, res_models_with_store in Hfib. simpl in Hfib.
    destruct Hfib as [_ Hstep].
    exact Hstep.
  }
  pose proof (fib_vars_obligation_step_commute y x R ρ m
    ltac:(congruence) Hydom Hxdom Hoblxy) as Hoblyx.
  unfold fib_vars_obligation_step in Hoblyx.
  destruct Hoblyx as [Hdisjy Hfibyx].
  unfold res_models_with_store. simpl.
  split.
  - unfold formula_scoped_in_world in *. simpl in *. set_solver.
  - split; [exact Hdisjy |].
    intros σy Hprojy.
    specialize (Hfibyx σy Hprojy).
    unfold fib_vars_obligation_step in Hfibyx.
    destruct Hfibyx as [Hdisjx Hfibx].
    unfold res_models_with_store. simpl.
    split.
    + unfold formula_scoped_in_world in *.
      simpl in *.
      pose proof (wfworld_store_dom (res_restrict m {[y]}) σy Hprojy) as Hdomσy.
      simpl in Hdomσy.
      rewrite dom_union_L.
      intros z Hz.
      apply elem_of_union in Hz as [Hzρσ|Hzφ].
      * apply elem_of_union in Hzρσ as [Hzρ|Hzσ].
        -- apply Hscope. set_solver.
        -- rewrite Hdomσy in Hzσ. apply Hscope. set_solver.
      * apply Hscope. set_solver.
    + split; [exact Hdisjx |].
      intros σx Hprojx.
      specialize (Hfibx σx Hprojx).
      unfold R, res_models_with_store in Hfibx.
      exact Hfibx.
Qed.

Lemma formula_store_equiv_fib_commute x y (φ : FQ) :
  x ≠ y →
  formula_store_equiv (FFib x (FFib y φ)) (FFib y (FFib x φ)).
Proof.
  intros Hxy ρ m. split.
  - apply formula_store_equiv_fib_commute_dir. exact Hxy.
  - apply formula_store_equiv_fib_commute_dir. congruence.
Qed.

Lemma foldr_fib_store_equiv xs φ ψ :
  formula_fv φ = formula_fv ψ →
  formula_store_equiv φ ψ →
  formula_fv (foldr FFib φ xs) = formula_fv (foldr FFib ψ xs) ∧
  formula_store_equiv (foldr FFib φ xs) (foldr FFib ψ xs).
Proof.
  induction xs as [|x xs IH]; simpl; intros Hfv Heq.
  - split; [exact Hfv | exact Heq].
  - destruct (IH Hfv Heq) as [Hfv' Heq'].
    split.
    + simpl. rewrite Hfv'. reflexivity.
    + apply formula_store_equiv_fib; assumption.
Qed.

Lemma fib_vars_store_equiv X φ ψ :
  formula_fv φ = formula_fv ψ →
  formula_store_equiv φ ψ →
  formula_fv (fib_vars X φ) = formula_fv (fib_vars X ψ) ∧
  formula_store_equiv (fib_vars X φ) (fib_vars X ψ).
Proof.
  intros Hfv Heq.
  unfold fib_vars, fib_vars_acc, set_fold.
  simpl.
  rewrite !foldr_fib_vars_acc_fst.
  apply foldr_fib_store_equiv; assumption.
Qed.

Lemma foldr_fib_formula_fv xs (φ : FQ) :
  formula_fv (foldr FFib φ xs) = list_to_set xs ∪ formula_fv φ.
Proof.
  induction xs as [|x xs IH]; simpl.
  - set_solver.
  - rewrite IH. set_solver.
Qed.

Lemma list_to_set_permutation_aset (xs ys : list atom) :
  xs ≡ₚ ys →
  (list_to_set xs : aset) = list_to_set ys.
Proof.
  intros Hperm.
  apply set_eq. intros z.
  rewrite !elem_of_list_to_set.
  by rewrite Hperm.
Qed.

Lemma foldr_fib_store_equiv_permutation xs ys (φ : FQ) :
  xs ≡ₚ ys →
  formula_store_equiv (foldr FFib φ xs) (foldr FFib φ ys).
Proof.
  intros Hperm.
  induction Hperm.
  - apply formula_store_equiv_refl.
  - apply formula_store_equiv_fib.
    + rewrite !(foldr_fib_formula_fv _ φ).
      rewrite (list_to_set_permutation_aset _ _ Hperm).
      reflexivity.
    + exact IHHperm.
  - destruct (decide (x = y)) as [->|Hxy].
    + apply formula_store_equiv_refl.
    + apply formula_store_equiv_fib_commute. congruence.
  - eapply formula_store_equiv_trans; eauto.
Qed.

Lemma fib_vars_insert_store_equiv x X (φ : FQ) :
  x ∉ X →
  formula_store_equiv (fib_vars ({[x]} ∪ X) φ) (FFib x (fib_vars X φ)).
Proof.
  intros Hx.
  unfold fib_vars, fib_vars_acc, set_fold.
  simpl.
  rewrite !foldr_fib_vars_acc_fst.
  change (formula_store_equiv
    (foldr FFib φ (elements ({[x]} ∪ X)))
    (foldr FFib φ (x :: elements X))).
  apply foldr_fib_store_equiv_permutation.
  apply NoDup_Permutation.
  - apply NoDup_elements.
  - constructor.
    + rewrite elem_of_elements. exact Hx.
    + apply NoDup_elements.
  - intros z.
    rewrite elem_of_elements, elem_of_cons, elem_of_elements.
    set_solver.
Qed.

Lemma res_models_of_formula_store_equiv φ ψ (m : WfWorld) :
  formula_store_equiv φ ψ →
  m ⊨ φ ↔ m ⊨ ψ.
Proof. intros Heq. unfold res_models. apply Heq. Qed.

Lemma fib_vars_insert_rename_res_models x y X (φ : FQ) (m : WfWorld) :
  x ∉ X →
  y ∉ X →
  m ⊨ formula_rename_atom x y (fib_vars ({[x]} ∪ X) φ) ↔
  m ⊨ fib_vars ({[y]} ∪ X) (formula_rename_atom x y φ).
Proof.
  intros Hx Hy.
  rewrite res_models_swap.
  transitivity
    (res_swap x y m ⊨ FFib x (fib_vars X φ)).
  - apply res_models_of_formula_store_equiv.
    apply fib_vars_insert_store_equiv. exact Hx.
  - transitivity
      (m ⊨ formula_rename_atom x y (FFib x (fib_vars X φ))).
    + symmetry. apply res_models_swap.
    + simpl.
      replace (atom_swap x y x) with y
        by (unfold atom_swap; repeat destruct decide; congruence).
      rewrite <- formula_rename_atom_fib_vars_fresh by assumption.
      symmetry.
      apply res_models_of_formula_store_equiv.
      apply fib_vars_insert_store_equiv. exact Hy.
Qed.

Lemma fib_vars_insert_rename_store_equiv x y X (φ : FQ) :
  x ∉ X →
  y ∉ X →
  formula_store_equiv
    (formula_rename_atom x y (fib_vars ({[x]} ∪ X) φ))
    (fib_vars ({[y]} ∪ X) (formula_rename_atom x y φ)).
Proof.
  intros Hx Hy ρ m.
  rewrite res_models_with_store_swap.
  transitivity
    (res_models_with_store (store_swap x y ρ) (res_swap x y m)
      (FFib x (fib_vars X φ))).
  - apply fib_vars_insert_store_equiv. exact Hx.
  - transitivity
      (res_models_with_store ρ m
        (formula_rename_atom x y (FFib x (fib_vars X φ)))).
    + symmetry. apply res_models_with_store_swap.
    + simpl.
      replace (atom_swap x y x) with y
        by (unfold atom_swap; repeat destruct decide; congruence).
      rewrite <- formula_rename_atom_fib_vars_fresh by assumption.
      symmetry.
      apply fib_vars_insert_store_equiv. exact Hy.
Qed.

Lemma store_swap_restrict_fresh x y (s : Store) X :
  x ∉ X →
  y ∉ X →
  store_swap x y (store_restrict s X) = store_restrict s X.
Proof.
  intros Hx Hy.
  apply (map_eq (M := gmap atom)). intros z.
  rewrite store_swap_lookup_inv, !store_restrict_lookup.
  destruct (decide (z ∈ X)) as [Hz|Hz];
    destruct (decide (atom_swap x y z ∈ X)) as [Hzs|Hzs].
  - rewrite atom_swap_fresh by set_solver. reflexivity.
  - exfalso. apply Hzs.
    rewrite atom_swap_fresh by set_solver. exact Hz.
  - exfalso. apply Hz.
    assert (Hzz : atom_swap x y (atom_swap x y z) ∈ X).
    {
      assert (Hsx : atom_swap x y z ≠ x).
      { intros Heq. apply Hx. rewrite <- Heq. exact Hzs. }
      assert (Hsy : atom_swap x y z ≠ y).
      { intros Heq. apply Hy. rewrite <- Heq. exact Hzs. }
      rewrite atom_swap_fresh by assumption.
      exact Hzs.
    }
    rewrite atom_swap_involutive in Hzz. exact Hzz.
  - reflexivity.
Qed.

Lemma res_models_rename_atom_fresh x y (φ : FQ) (m : WfWorld) :
  x ∉ formula_fv φ →
  y ∉ formula_fv φ →
  m ⊨ formula_rename_atom x y φ ↔ m ⊨ φ.
Proof.
  intros Hx Hy.
  rewrite res_models_swap.
  transitivity (res_restrict (res_swap x y m) (formula_fv φ) ⊨ φ).
  - apply res_models_minimal_on. reflexivity.
  - transitivity (res_restrict m (formula_fv φ) ⊨ φ).
    + assert (Hrestrict :
        res_restrict (res_swap x y m) (formula_fv φ) =
        res_restrict m (formula_fv φ)).
      {
        rewrite <- (aset_swap_fresh x y (formula_fv φ)) at 1 by assumption.
        rewrite res_restrict_swap.
        apply wfworld_ext. apply world_ext.
        - simpl. rewrite aset_swap_fresh by set_solver. reflexivity.
        - intros σ. simpl. split.
          + intros [σ0 [[σm [Hσm Hswap]] Hσ0]].
            subst σ0.
            exists σm. split; [exact Hσm |].
            rewrite <- Hσ0.
            rewrite store_swap_restrict_fresh by assumption.
            reflexivity.
          + intros [σm [Hσm Hrestrict]].
            exists (store_restrict σm (formula_fv φ)).
            split.
            * exists σm. split; [exact Hσm | reflexivity].
            * rewrite <- Hrestrict.
              rewrite store_swap_restrict_fresh by assumption.
              reflexivity.
      }
      rewrite Hrestrict. reflexivity.
    + symmetry. apply res_models_minimal_on. reflexivity.
Qed.

Lemma denot_ty_fuel_env_agree gas Σ1 Σ2 τ e :
  dom Σ1 = dom Σ2 →
  ty_env_agree_on (fv_cty τ) Σ1 Σ2 →
  denot_ty_fuel gas Σ1 τ e = denot_ty_fuel gas Σ2 τ e.
Proof.
Admitted.

Lemma denot_ty_under_env_agree Σ1 Σ2 τ e :
  dom Σ1 = dom Σ2 →
  ty_env_agree_on (fv_cty τ) Σ1 Σ2 →
  denot_ty_under Σ1 τ e = denot_ty_under Σ2 τ e.
Proof.
  intros Hdom Hagree.
  unfold denot_ty_under, denot_ty_on.
  apply denot_ty_fuel_env_agree; assumption.
Qed.

Lemma denot_ty_under_env_equiv Σ1 Σ2 τ e :
  dom Σ1 = dom Σ2 →
  ty_env_agree_on (fv_cty τ) Σ1 Σ2 →
  denot_ty_under Σ1 τ e ⊣⊢ denot_ty_under Σ2 τ e.
Proof.
  intros Hdom Hagree.
  rewrite (denot_ty_under_env_agree Σ1 Σ2 τ e Hdom Hagree).
  apply formula_equiv_refl.
Qed.

Lemma denot_ty_in_ctx_env_agree Γ1 Γ2 τ e :
  dom (erase_ctx Γ1) = dom (erase_ctx Γ2) →
  ty_env_agree_on (fv_cty τ) (erase_ctx Γ1) (erase_ctx Γ2) →
  denot_ty_in_ctx Γ1 τ e = denot_ty_in_ctx Γ2 τ e.
Proof.
  intros Hdom Hagree. unfold denot_ty_in_ctx.
  apply denot_ty_under_env_agree.
  - exact Hdom.
  - exact Hagree.
Qed.

Lemma denot_ty_in_ctx_env_equiv Γ1 Γ2 τ e :
  dom (erase_ctx Γ1) = dom (erase_ctx Γ2) →
  ty_env_agree_on (fv_cty τ) (erase_ctx Γ1) (erase_ctx Γ2) →
  denot_ty_in_ctx Γ1 τ e ⊣⊢ denot_ty_in_ctx Γ2 τ e.
Proof.
  intros Hdom Hagree. unfold denot_ty_in_ctx.
  apply denot_ty_under_env_equiv.
  - exact Hdom.
  - exact Hagree.
Qed.

(** ** Denotation scoping regularity

    These syntactic facts isolate the variable-accounting needed by semantic
    subtyping reflexivity.  They are intentionally stated at the denotation
    layer: typing proofs should consume these regularity lemmas rather than
    unfolding the formula generated for each type constructor. *)

Lemma fresh_forall_formula_fv_subset
    (D S : aset) (Q : atom → FQ) :
  D ⊆ S →
  (∀ x, x ∉ D → formula_fv (Q x) ⊆ S ∪ {[x]}) →
  formula_fv (fresh_forall D Q) ⊆ S.
Proof.
  intros HDS HQ.
  unfold fresh_forall.
  set (x := fresh_for D).
  simpl.
  pose proof (fresh_for_not_in D) as Hfresh.
  fold x in Hfresh.
  pose proof (HQ x Hfresh) as HQx.
  set_solver.
Qed.

Lemma FExprContIn_formula_fv_subset
    (Σ : gmap atom ty) e (S : aset) (Q : atom → FQ) :
  dom Σ ⊆ S →
  (∀ ν, ν ∉ dom Σ → formula_fv (Q ν) ⊆ S ∪ {[ν]}) →
  formula_fv (FExprContIn Σ e Q) ⊆ S.
Proof.
  intros Hdom HQ.
  unfold FExprContIn.
  apply fresh_forall_formula_fv_subset; first exact Hdom.
  intros ν Hν.
  simpl. rewrite FExprResultOn_fv.
  pose proof (HQ ν Hν) as HQν.
  set_solver.
Qed.

Lemma denot_ty_fuel_formula_fv_subset gas Σ τ e :
  cty_measure τ <= gas →
  formula_fv (denot_ty_fuel gas Σ τ e) ⊆ dom Σ ∪ fv_cty τ.
Proof.
  revert Σ τ e.
  induction gas as [|gas IH]; intros Σ τ e Hgas.
  - pose proof (cty_measure_gt_0 τ). lia.
  - destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τ|τx τ];
      cbn [denot_ty_fuel denot_ty_fuel_result denot_ty_formula
        mk_denot_ty_result cty_measure fv_cty] in *.
    + apply FExprContIn_formula_fv_subset; first set_solver.
      intros ν _.
      cbn [formula_fv].
      rewrite basic_world_formula_fv.
      rewrite fib_vars_formula_fv.
      destruct φ as [B d p].
      unfold qual_open_atom, FTypeQualifier, qual_dom in *; simpl in *.
      destruct (decide (0 ∈ B)); simpl.
      all: unfold stale, stale_logic_qualifier; simpl; set_solver.
    + apply FExprContIn_formula_fv_subset; first set_solver.
      intros ν _.
      cbn [formula_fv].
      rewrite basic_world_formula_fv.
      rewrite fib_vars_formula_fv.
      destruct φ as [B d p].
      unfold qual_open_atom, FTypeQualifier, qual_dom in *; simpl in *.
      destruct (decide (0 ∈ B)); simpl.
      all: unfold stale, stale_logic_qualifier; simpl; set_solver.
    + pose proof (IH Σ τ1 e ltac:(lia)) as H1.
      pose proof (IH Σ τ2 e ltac:(lia)) as H2.
      set_solver.
    + pose proof (IH Σ τ1 e ltac:(lia)) as H1.
      pose proof (IH Σ τ2 e ltac:(lia)) as H2.
      set_solver.
    + pose proof (IH Σ τ1 e ltac:(lia)) as H1.
      pose proof (IH Σ τ2 e ltac:(lia)) as H2.
      set_solver.
    + apply fresh_forall_formula_fv_subset
        with (S := dom Σ ∪ (fv_cty τx ∪ fv_cty τ)).
      * set_solver.
      * intros x Hx.
        set (Σx := <[x:=erase_ty τx]> Σ).
        pose proof (IH Σx τx (tret (vfvar x)) ltac:(lia)) as Harg.
        pose proof (IH Σx ({0 ~> x} τ)
          (tapp_tm e (vfvar x)) ltac:(rewrite cty_open_preserves_measure; lia))
          as Hres.
        pose proof (cty_open_fv_subset 0 x τ) as Hopen.
        unfold Σx in *.
        rewrite !dom_insert_L in *.
        set_solver.
    + apply fresh_forall_formula_fv_subset
        with (S := dom Σ ∪ (fv_cty τx ∪ fv_cty τ)).
      * set_solver.
      * intros x Hx.
        set (Σx := <[x:=erase_ty τx]> Σ).
        pose proof (IH Σx τx (tret (vfvar x)) ltac:(lia)) as Harg.
        pose proof (IH Σx ({0 ~> x} τ)
          (tapp_tm e (vfvar x)) ltac:(rewrite cty_open_preserves_measure; lia))
          as Hres.
        pose proof (cty_open_fv_subset 0 x τ) as Hopen.
        unfold Σx in *.
        rewrite !dom_insert_L in *.
        set_solver.
Qed.

Lemma denot_ty_formula_fv_subset τ e :
  formula_fv (denot_ty τ e) ⊆ fv_cty τ.
Proof.
  unfold denot_ty, denot_ty_under, denot_ty_on.
  pose proof (denot_ty_fuel_formula_fv_subset
    (cty_measure τ) ∅ τ e ltac:(lia)) as Hfv.
  intros z Hz. apply Hfv in Hz. set_solver.
Qed.

Lemma denot_ty_fuel_formula_fv_env_agree gas Σ1 Σ2 τ e :
  dom Σ1 = dom Σ2 →
  formula_fv (denot_ty_fuel gas Σ1 τ e) =
  formula_fv (denot_ty_fuel gas Σ2 τ e).
Proof.
Admitted.

Lemma denot_ty_under_formula_fv_subset Σ τ e :
  formula_fv (denot_ty_under Σ τ e) ⊆ dom Σ ∪ fv_cty τ.
Proof.
  unfold denot_ty_under, denot_ty_on.
  pose proof (denot_ty_fuel_formula_fv_subset
    (cty_measure τ) Σ τ e ltac:(lia)) as Hfv.
  intros z Hz. apply Hfv in Hz. set_solver.
Qed.

Lemma denot_ty_on_formula_fv_subset Σ τ e :
  formula_fv (denot_ty_on Σ τ e) ⊆ dom Σ ∪ fv_cty τ.
Proof.
  apply denot_ty_under_formula_fv_subset.
Qed.

Lemma denot_ty_in_ctx_under_formula_fv_subset Σ Γ τ e :
  formula_fv (denot_ty_in_ctx_under Σ Γ τ e) ⊆
    dom (erase_ctx_under Σ Γ) ∪ fv_cty τ.
Proof.
  unfold denot_ty_in_ctx_under.
  apply denot_ty_on_formula_fv_subset.
Qed.

Lemma denot_ty_fuel_env_fv_subset gas Σ τ e :
  cty_measure τ <= gas →
  dom Σ ⊆ formula_fv (denot_ty_fuel gas Σ τ e).
Proof.
  revert Σ τ e.
  induction gas as [|gas IH]; intros Σ τ e Hgas.
  - pose proof (cty_measure_gt_0 τ). lia.
  - destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τ|τx τ];
      cbn [denot_ty_fuel denot_ty_fuel_result denot_ty_formula
        mk_denot_ty_result cty_measure fv_cty] in *.
    + unfold FExprContIn, fresh_forall.
      cbn [formula_fv].
      rewrite FExprResultOn_fv.
      pose proof (fresh_for_not_in (dom Σ)) as Hfresh.
      set_solver.
    + unfold FExprContIn, fresh_forall.
      cbn [formula_fv].
      rewrite FExprResultOn_fv.
      pose proof (fresh_for_not_in (dom Σ)) as Hfresh.
      set_solver.
    + pose proof (IH Σ τ1 e ltac:(lia)) as H1. set_solver.
    + pose proof (IH Σ τ1 e ltac:(lia)) as H1. set_solver.
    + pose proof (IH Σ τ1 e ltac:(lia)) as H1. set_solver.
    + unfold fresh_forall.
      cbn [formula_fv].
      set (x := fresh_for (dom Σ)).
      set (Σx := <[x:=erase_ty τx]> Σ).
      assert (Hx : x ∉ dom Σ) by (subst x; apply fresh_for_not_in).
      pose proof (IH Σx τx (tret (vfvar x)) ltac:(lia)) as Harg.
      unfold Σx in Harg. rewrite dom_insert_L in Harg.
      intros z Hz.
      apply elem_of_difference. split.
      * apply elem_of_union_l. apply Harg. set_solver.
      * set_solver.
    + unfold fresh_forall.
      cbn [formula_fv].
      set (x := fresh_for (dom Σ)).
      set (Σx := <[x:=erase_ty τx]> Σ).
      assert (Hx : x ∉ dom Σ) by (subst x; apply fresh_for_not_in).
      pose proof (IH Σx τx (tret (vfvar x)) ltac:(lia)) as Harg.
      unfold Σx in Harg. rewrite dom_insert_L in Harg.
      intros z Hz.
      apply elem_of_difference. split.
      * apply elem_of_union_l. apply Harg. set_solver.
      * set_solver.
Qed.

Lemma denot_ty_under_result_atom_fv Σ x τ :
  x ∈ dom Σ →
  x ∈ formula_fv (denot_ty_under Σ τ (tret (vfvar x))).
Proof.
  intros Hx.
  unfold denot_ty_under, denot_ty_on.
  pose proof (denot_ty_fuel_env_fv_subset
    (cty_measure τ) Σ τ (tret (vfvar x)) ltac:(lia)) as Hfv.
  apply Hfv. exact Hx.
Qed.

Lemma denot_ty_on_result_atom_fv Σ x τ :
  x ∈ dom Σ →
  x ∈ formula_fv (denot_ty_on Σ τ (tret (vfvar x))).
Proof.
  apply denot_ty_under_result_atom_fv.
Qed.

Lemma denot_ty_restrict_fv τ e m :
  m ⊨ denot_ty τ e →
  res_restrict m (fv_cty τ) ⊨ denot_ty τ e.
Proof.
  intros Hm.
  eapply res_models_kripke.
  - apply res_restrict_mono. apply denot_ty_formula_fv_subset.
  - apply res_models_restrict_fv. exact Hm.
Qed.

Lemma denot_ty_under_restrict_fv Σ τ e m :
  m ⊨ denot_ty_under Σ τ e →
  res_restrict m (dom Σ ∪ fv_cty τ) ⊨ denot_ty_under Σ τ e.
Proof.
  intros Hm.
  eapply res_models_kripke.
  - apply res_restrict_mono. apply denot_ty_under_formula_fv_subset.
  - apply res_models_restrict_fv. exact Hm.
Qed.

(** ** Context denotation

    [denot_ctx_under Σ Γ] is the formula that holds when [Γ] is satisfied
    under the ambient erased basic environment [Σ].  The public
    [denot_ctx Γ] instantiates [Σ] with [erase_ctx Γ], so later binders in a
    comma context can be checked against earlier erased bindings. *)
