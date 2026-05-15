(** * ChoiceType.DenotationType

    Choice-type denotation and formula-locality lemmas. *)

From LocallyNameless Require Import Tactics.
From CoreLang Require Import Instantiation InstantiationProps LocallyNamelessProps
  OperationalProps StrongNormalization Sugar.
From ChoiceType Require Export DenotationFormulaEquiv.
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

Definition lty_env : Type := gmap logic_var ty.

Definition lty_env_closed (Σ : lty_env) : Prop :=
  lvars_bv (dom Σ) = ∅.

Definition atom_env_to_lty_env (Σ : gmap atom ty) : lty_env :=
  map_fold (fun x T acc => <[LVFree x := T]> acc) ∅ Σ.

Definition lvar_to_atom (η : gmap nat atom) (v : logic_var) : option atom :=
  match v with
  | LVFree x => Some x
  | LVBound k => η !! k
  end.

Definition lty_env_open (η : gmap nat atom) (Σ : lty_env) : gmap atom ty :=
  map_fold (fun v T acc =>
    match lvar_to_atom η v with
    | Some x => <[x := T]> acc
    | None => acc
    end) ∅ Σ.

Definition open_cty_env (η : gmap nat atom) (τ : choice_ty) : choice_ty :=
  map_fold (fun k x acc => cty_open k x acc) τ η.

Definition lty_env_atom_dom (Σ : lty_env) : aset :=
  lvars_fv (dom Σ).

Definition lty_env_bvar_scope (Σ : lty_env) : lvset :=
  lvars_of_bvars (lvars_bv (dom Σ)).

Lemma atom_env_to_lty_env_dom Σ :
  dom (atom_env_to_lty_env Σ) = lvars_of_atoms (dom Σ).
Proof.
  unfold atom_env_to_lty_env, lvars_of_atoms.
  refine (fin_maps.map_fold_ind
    (fun Σ => dom (map_fold
        (fun (x : atom) (T : ty) (acc : lty_env) => <[LVFree x := T]> acc)
        (∅ : lty_env) Σ)
      = set_map LVFree (dom Σ)) _ _ Σ).
  - rewrite dom_empty_L. rewrite set_map_empty. reflexivity.
  - intros x T Σ' Hfresh Hfold IH.
    rewrite Hfold.
	    replace (dom (map_fold
	        (fun (x : atom) (T : ty) (acc : lty_env) => <[LVFree x := T]> acc)
	        (∅ : lty_env) Σ'))
	      with (set_map (C:=aset) (D:=lvset) LVFree (dom Σ'))
	      by exact (eq_sym IH).
	    rewrite dom_insert_L.
	    rewrite set_map_union_L, set_map_singleton_L.
    set_solver.
Qed.

Lemma atom_env_to_lty_env_closed Σ :
  lty_env_closed (atom_env_to_lty_env Σ).
Proof.
  unfold lty_env_closed.
  rewrite atom_env_to_lty_env_dom.
  apply lvars_bv_of_atoms.
Qed.

Lemma atom_env_to_lty_env_atom_dom Σ :
  lty_env_atom_dom (atom_env_to_lty_env Σ) = dom Σ.
Proof.
  unfold lty_env_atom_dom. rewrite atom_env_to_lty_env_dom.
  apply lvars_fv_of_atoms.
Qed.

Lemma lty_env_open_atom_env_empty Σ :
  lty_env_open ∅ (atom_env_to_lty_env Σ) = Σ.
Proof.
Admitted.

Lemma lty_env_open_atom_env η Σ :
  lty_env_open η (atom_env_to_lty_env Σ) = Σ.
Proof.
Admitted.

Lemma open_cty_env_empty τ :
  open_cty_env ∅ τ = τ.
Proof.
  reflexivity.
Qed.

Lemma open_tm_env_empty e :
  open_tm_env ∅ e = e.
Proof.
  reflexivity.
Qed.

Lemma FExprContIn_atom_env_to_lty_env Σ e (Q : FQ) :
  FExprContIn (atom_env_to_lty_env Σ) e Q = FExprContIn Σ e Q.
Proof.
  unfold FExprContIn, FExprResultOn, into_lvars, into_lvars_lvset,
    into_lvars_aset.
  rewrite atom_env_to_lty_env_dom.
  reflexivity.
Qed.

(** ** Type denotation

    [denot_ty_fuel gas Σ τ e] is the recursive semantic content of
    "expression [e] has type [τ]" under erased basic environment [Σ],
    including the obligations every denotation needs: basic typing, closed
    resources, and deterministic result reachability.

    Keeping the obligations in the recursive formula itself avoids the previous
    record-wrapper style: recursive calls are ordinary full
    formulas, and helper lemmas can reason with Choice Logic connectives
    directly.  [denot_ty_fuel_body] is only a one-step view used by proofs to
    peel the outer obligation layer; it is not recursive by itself.
    Expression-result atoms and fresh representatives are driven by [dom Σ].
    The regularity assumptions that [fv_tm e] and [fv_cty τ] are contained in
    [dom Σ] are supplied by the basic typing conjunct. *)

Definition expr_total_with_store (X : aset) (e : tm)
    (ρ : Store) (m : WfWorld) : Prop :=
  (∀ σ, (m : World) σ → store_closed (store_restrict (ρ ∪ σ) X)) ∧
  ∀ σ, (m : World) σ →
    ∃ vx, subst_map (store_restrict (ρ ∪ σ) X) e →* tret vx.

Definition FBasicTypingIn (Σe Στ : lty_env) (τ : choice_ty) (e : tm) : FQ :=
  FStoreResourceAtom (dom Σe ∪ dom Στ)
    (fun η _ _ =>
      let Γe := lty_env_open η Σe in
      let Γτ := lty_env_open η Στ in
      let τη := open_cty_env η τ in
      let eη := open_tm_env η e in
      basic_choice_ty (dom Γτ) τη ∧ Γe ⊢ₑ eη ⋮ erase_ty τη).

Definition FClosedResourceIn (Σ : lty_env) : FQ :=
  FResourceAtom (dom Σ) (world_closed_on (lty_env_atom_dom Σ)).

Definition FStrongTotalIn (Σ : lty_env) (e : tm) : FQ :=
  FStoreResourceAtom (dom Σ)
    (fun η ρ m =>
      expr_total_with_store (lty_env_atom_dom Σ) (open_tm_env η e) ρ m).

Definition FResultBasicWorld
    (Σ : lty_env) (b : base_ty) (D : lvset) : FQ :=
  FStoreResourceAtom (lty_env_bvar_scope Σ ∪ D ∪ {[LVBound 0]})
    (fun η _ m =>
      match η !! 0 with
      | Some ν =>
          world_has_type_on (<[ν := TBase b]> (lty_env_open η Σ))
            (lvars_fv D ∪ {[ν]}) m
      | None => False
      end).

Definition denot_ty_obligations
    (Σe Στ : lty_env) (τ : choice_ty) (e : tm) (φ : FQ) : FQ :=
  FAnd (FBasicTypingIn Σe Στ τ e)
    (FAnd (FClosedResourceIn Σe)
      (FAnd (FStrongTotalIn Σe e) φ)).

Lemma formula_fv_FResultBasicWorld Σ b D :
  formula_fv (FResultBasicWorld Σ b D) =
  lvars_fv (lty_env_bvar_scope Σ ∪ D ∪ {[LVBound 0]}).
Proof.
  unfold FResultBasicWorld.
  apply formula_fv_FStoreResourceAtom_lvars.
Qed.

Lemma formula_fv_FResultBasicWorld_atom_env_subset Σ b D :
  lvars_fv D ⊆ dom Σ →
  formula_fv (FResultBasicWorld (atom_env_to_lty_env Σ) b D) ⊆ dom Σ.
Proof.
  intros HD.
  rewrite formula_fv_FResultBasicWorld.
  unfold lty_env_bvar_scope.
  rewrite atom_env_to_lty_env_dom.
  rewrite lvars_bv_of_atoms.
  rewrite lvars_fv_union, lvars_fv_union.
  rewrite lvars_fv_of_bvars, lvars_fv_singleton_bound.
  set_solver.
Qed.

Lemma formula_fv_FResultBasicWorld_atom_env Σ b D :
  formula_fv (FResultBasicWorld (atom_env_to_lty_env Σ) b D) = lvars_fv D.
Proof.
  rewrite formula_fv_FResultBasicWorld.
  unfold lty_env_bvar_scope.
  rewrite atom_env_to_lty_env_dom.
  rewrite lvars_bv_of_atoms.
  rewrite lvars_fv_union, lvars_fv_union.
  rewrite lvars_fv_of_bvars, lvars_fv_singleton_bound.
  set_solver.
Qed.

Lemma FResultBasicWorld_open_domain_atom_env Σ D ν :
  lvars_fv
    (lvars_open 0 ν
      (lty_env_bvar_scope (atom_env_to_lty_env Σ) ∪ D ∪ {[LVBound 0]})) =
  lvars_fv D ∪ {[ν]}.
Proof.
  rewrite lvars_fv_open.
  unfold lty_env_bvar_scope.
  rewrite atom_env_to_lty_env_dom.
  rewrite lvars_bv_of_atoms.
  rewrite ?lvars_fv_union.
  rewrite ?lvars_fv_of_bvars.
  rewrite ?lvars_fv_union.
  rewrite ?lvars_fv_singleton_bound.
  destruct decide as [_|Hnot].
  - set_solver.
  - exfalso.
    apply Hnot.
    replace (lvars_of_bvars ∅ ∪ D ∪ {[LVBound 0]})
      with ((lvars_of_bvars ∅ ∪ D) ∪ {[LVBound 0]}) by set_solver.
    apply lvars_bv_contains_bound_singleton.
Qed.

Lemma FResultBasicWorld_open_domain_atom_env_into Σ D ν :
  lvars_fv
    (lvars_open 0 ν
      (into_lvars
        (lty_env_bvar_scope (atom_env_to_lty_env Σ) ∪ D ∪ {[LVBound 0]}))) =
  lvars_fv D ∪ {[ν]}.
Proof.
  cbn [into_lvars into_lvars_lvset].
  apply FResultBasicWorld_open_domain_atom_env.
Qed.

Lemma formula_store_equiv_FResultBasicWorld_atom_env_insert_fresh_open
    Σ x T b D ν :
  x ∉ dom Σ ∪ lvars_fv D →
  formula_store_equiv
    (formula_open 0 ν
      (FResultBasicWorld (atom_env_to_lty_env (<[x := T]> Σ)) b D))
    (formula_open 0 ν
      (FResultBasicWorld (atom_env_to_lty_env Σ) b D)).
Proof.
  intros Hx ρ m.
  unfold FResultBasicWorld, FStoreResourceAtom.
  cbn [formula_open formula_fv lqual_open lqual_dom into_lvars
    into_lvars_lvset stale stale_logic_qualifier].
  unfold res_models_with_store.
  cbn [formula_measure res_models_with_store_fuel formula_scoped_in_world
    formula_fv lqual_dom logic_qualifier_denote lqual_prop].
  rewrite !FResultBasicWorld_open_domain_atom_env_into.
  rewrite !lty_env_open_atom_env.
  rewrite lookup_insert_eq.
  split; intros [Hscope [m0 [Hscope0 [Htyped Hle]]]]; split.
  - unfold formula_scoped_in_world in *.
    cbn [formula_fv lqual_dom stale stale_logic_qualifier] in *.
    rewrite !FResultBasicWorld_open_domain_atom_env_into in *.
    exact Hscope.
  - exists m0. split.
    + unfold formula_scoped_in_world in *.
      cbn [formula_fv lqual_dom stale stale_logic_qualifier] in *.
      rewrite !FResultBasicWorld_open_domain_atom_env_into in *.
      exact Hscope0.
    + split; [| exact Hle].
      pose proof (world_has_type_on_insert_under_result_irrel
        Σ (lvars_fv D) (res_restrict m0 (lvars_fv D ∪ {[ν]}))
        x T ν b ltac:(set_solver)) as Hiff.
      exact (proj1 Hiff Htyped).
  - unfold formula_scoped_in_world in *.
    cbn [formula_fv lqual_dom stale stale_logic_qualifier] in *.
    rewrite !FResultBasicWorld_open_domain_atom_env_into in *.
    exact Hscope.
  - exists m0. split.
    + unfold formula_scoped_in_world in *.
      cbn [formula_fv lqual_dom stale stale_logic_qualifier] in *.
      rewrite !FResultBasicWorld_open_domain_atom_env_into in *.
      exact Hscope0.
    + split; [| exact Hle].
      pose proof (world_has_type_on_insert_under_result_irrel
        Σ (lvars_fv D) (res_restrict m0 (lvars_fv D ∪ {[ν]}))
        x T ν b ltac:(set_solver)) as Hiff.
      exact (proj2 Hiff Htyped).
Qed.

Lemma formula_fv_FResultBasicWorld_atom_env_insert_fresh_open
    Σ x T b D ν :
  x ∉ dom Σ ∪ lvars_fv D →
  formula_fv
    (formula_open 0 ν
      (FResultBasicWorld (atom_env_to_lty_env (<[x := T]> Σ)) b D)) =
  formula_fv
    (formula_open 0 ν
      (FResultBasicWorld (atom_env_to_lty_env Σ) b D)).
Proof.
  intros _.
  unfold FResultBasicWorld, FStoreResourceAtom.
  cbn [formula_open formula_fv lqual_open lqual_dom into_lvars
    into_lvars_lvset stale stale_logic_qualifier].
  rewrite !FResultBasicWorld_open_domain_atom_env_into.
  reflexivity.
Qed.

Lemma expr_total_with_store_empty_restrict X e m :
  world_closed_on X m →
  expr_total_on X e m →
  expr_total_with_store X e ∅ (res_restrict m X).
Proof.
  intros Hclosed [_ Htotal].
  split.
  - intros σ Hσ.
    destruct (res_restrict_lift_store m X σ Hσ) as [σm [Hσm Hrestrict]].
    assert (Heq : store_restrict ((∅ : Store) ∪ σ) X = store_restrict σm X).
    { rewrite map_empty_union.
      rewrite <- Hrestrict.
      rewrite store_restrict_restrict.
      replace (X ∩ X) with X by set_solver.
      reflexivity. }
    rewrite Heq. apply Hclosed. exact Hσm.
  - intros σ Hσ.
    destruct (res_restrict_lift_store m X σ Hσ) as [σm [Hσm Hrestrict]].
    assert (Heq : store_restrict ((∅ : Store) ∪ σ) X = store_restrict σm X).
    { rewrite map_empty_union.
      rewrite <- Hrestrict.
      rewrite store_restrict_restrict.
      replace (X ∩ X) with X by set_solver.
      reflexivity. }
    rewrite Heq. apply Htotal. exact Hσm.
Unshelve.
  all: try typeclasses eauto; try set_solver.
Qed.

Lemma formula_fv_FOver_FTypeQualifier q :
  formula_fv (FOver (FTypeQualifier q)) = qual_dom q.
Proof.
  cbn [formula_fv]. apply formula_fv_FTypeQualifier.
Qed.

Lemma formula_fv_FUnder_FTypeQualifier q :
  formula_fv (FUnder (FTypeQualifier q)) = qual_dom q.
Proof.
  cbn [formula_fv]. apply formula_fv_FTypeQualifier.
Qed.

Fixpoint denot_ty_fuel_body_lvar
    (gas : nat) (Σe Στ : lty_env) (τ : choice_ty) (e : tm) : FQ :=
  match gas with
  | 0 => FFalse
  | S gas' =>
  match τ with
  | CTOver b φ =>
      FExprContIn Σe e (
        FAnd
          (FResultBasicWorld Στ b (qual_vars φ))
          (FFibVars (qual_vars φ)
       (FOver (FTypeQualifier φ))))
  | CTUnder b φ =>
      FExprContIn Σe e (
        FAnd
          (FResultBasicWorld Στ b (qual_vars φ))
          (FFibVars (qual_vars φ)
       (FUnder (FTypeQualifier φ))))
  | CTInter τ1 τ2 =>
      FAnd
        (denot_ty_obligations Σe Στ τ1 e
          (denot_ty_fuel_body_lvar gas' Σe Στ τ1 e))
        (denot_ty_obligations Σe Στ τ2 e
          (denot_ty_fuel_body_lvar gas' Σe Στ τ2 e))
  | CTUnion τ1 τ2 =>
      FOr
        (denot_ty_obligations Σe Στ τ1 e
          (denot_ty_fuel_body_lvar gas' Σe Στ τ1 e))
        (denot_ty_obligations Σe Στ τ2 e
          (denot_ty_fuel_body_lvar gas' Σe Στ τ2 e))
  | CTSum τ1 τ2 =>
      FPlus
        (denot_ty_obligations Σe Στ τ1 e
          (denot_ty_fuel_body_lvar gas' Σe Στ τ1 e))
        (denot_ty_obligations Σe Στ τ2 e
          (denot_ty_fuel_body_lvar gas' Σe Στ τ2 e))
  | CTArrow τx τ =>
      FForall (
        let Σex := <[LVBound 0 := erase_ty τx]> Σe in
        let Στx := <[LVBound 0 := erase_ty τx]> Στ in
          FImpl
            (denot_ty_obligations Σex Στ τx (tret (vbvar 0))
              (denot_ty_fuel_body_lvar gas' Σex Στ τx (tret (vbvar 0))))
            (denot_ty_obligations Σex Στx τ (tapp_tm e (vbvar 0))
              (denot_ty_fuel_body_lvar gas' Σex Στx τ
                (tapp_tm e (vbvar 0)))))
  | CTWand τx τ =>
      FForall (
        let Σex := <[LVBound 0 := erase_ty τx]> Σe in
        let Στx := <[LVBound 0 := erase_ty τx]> Στ in
          FWand
            (denot_ty_obligations Σex Στ τx (tret (vbvar 0))
              (denot_ty_fuel_body_lvar gas' Σex Στ τx (tret (vbvar 0))))
            (denot_ty_obligations Σex Στx τ (tapp_tm e (vbvar 0))
              (denot_ty_fuel_body_lvar gas' Σex Στx τ
                (tapp_tm e (vbvar 0)))))
  end
  end.

Definition denot_ty_fuel_lvar
    (gas : nat) (Σe Στ : lty_env) (τ : choice_ty) (e : tm)
    : FQ :=
  denot_ty_obligations Σe Στ τ e
    (denot_ty_fuel_body_lvar gas Σe Στ τ e).

Definition denot_ty_fuel
    (gas : nat) (Σ : gmap atom ty) (τ : choice_ty) (e : tm) : FQ :=
  let Σl := atom_env_to_lty_env Σ in
  denot_ty_fuel_lvar gas Σl Σl τ e.

Definition denot_ty_fuel_body
    (gas : nat) (Σ : gmap atom ty) (τ : choice_ty) (e : tm) : FQ :=
  let Σl := atom_env_to_lty_env Σ in
  denot_ty_fuel_body_lvar gas Σl Σl τ e.

Lemma denot_ty_fuel_unfold gas Σ τ e :
  denot_ty_fuel gas Σ τ e =
  let Σl := atom_env_to_lty_env Σ in
  denot_ty_obligations Σl Σl τ e (denot_ty_fuel_body gas Σ τ e).
Proof.
  unfold denot_ty_fuel, denot_ty_fuel_body.
  destruct gas as [|gas]; reflexivity.
Qed.

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

Lemma denot_ty_fuel_env_agree gas Σ1 Σ2 τ e :
  dom Σ1 = dom Σ2 →
  ty_env_agree_on (fv_cty τ ∪ fv_tm e) Σ1 Σ2 →
  denot_ty_fuel gas Σ1 τ e = denot_ty_fuel gas Σ2 τ e.
Proof.
Admitted.

Lemma denot_ty_under_env_agree Σ1 Σ2 τ e :
  dom Σ1 = dom Σ2 →
  ty_env_agree_on (fv_cty τ ∪ fv_tm e) Σ1 Σ2 →
  denot_ty_under Σ1 τ e = denot_ty_under Σ2 τ e.
Proof.
  intros Hdom Hagree.
  unfold denot_ty_under, denot_ty_on.
  apply denot_ty_fuel_env_agree; assumption.
Qed.

Lemma denot_ty_under_env_equiv Σ1 Σ2 τ e :
  dom Σ1 = dom Σ2 →
  ty_env_agree_on (fv_cty τ ∪ fv_tm e) Σ1 Σ2 →
  denot_ty_under Σ1 τ e ⊣⊢ denot_ty_under Σ2 τ e.
Proof.
  intros Hdom Hagree.
  rewrite (denot_ty_under_env_agree Σ1 Σ2 τ e Hdom Hagree).
  apply formula_equiv_refl.
Qed.

Lemma denot_ty_in_ctx_env_agree Γ1 Γ2 τ e :
  dom (erase_ctx Γ1) = dom (erase_ctx Γ2) →
  ty_env_agree_on (fv_cty τ ∪ fv_tm e) (erase_ctx Γ1) (erase_ctx Γ2) →
  denot_ty_in_ctx Γ1 τ e = denot_ty_in_ctx Γ2 τ e.
Proof.
  intros Hdom Hagree. unfold denot_ty_in_ctx.
  apply denot_ty_under_env_agree.
  - exact Hdom.
  - exact Hagree.
Qed.

Lemma denot_ty_in_ctx_env_equiv Γ1 Γ2 τ e :
  dom (erase_ctx Γ1) = dom (erase_ctx Γ2) →
  ty_env_agree_on (fv_cty τ ∪ fv_tm e) (erase_ctx Γ1) (erase_ctx Γ2) →
  denot_ty_in_ctx Γ1 τ e ⊣⊢ denot_ty_in_ctx Γ2 τ e.
Proof.
  intros Hdom Hagree. unfold denot_ty_in_ctx.
  apply denot_ty_under_env_equiv.
  - exact Hdom.
  - exact Hagree.
Qed.

Lemma formula_fv_FResultBasicWorld_lvar_subset Σ b D :
  formula_fv (FResultBasicWorld Σ b D) ⊆ lvars_fv D.
Proof.
  rewrite formula_fv_FResultBasicWorld.
  unfold lty_env_bvar_scope.
  rewrite lvars_fv_union, lvars_fv_union.
  rewrite lvars_fv_of_bvars, lvars_fv_singleton_bound.
  set_solver.
Qed.

Lemma FExprContIn_lty_env_formula_fv_subset
    (Σ : lty_env) e (Q : FQ) :
  formula_fv (FExprContIn Σ e Q) ⊆ lty_env_atom_dom Σ ∪ formula_fv Q.
Proof.
  unfold FExprContIn.
  cbn [formula_fv].
  denot_lvars_norm.
  rewrite FExprResultOn_lvars_fv.
  unfold lty_env_atom_dom.
  set_solver.
Qed.

Lemma lty_env_atom_dom_insert_bound Σ k T :
  lty_env_atom_dom (<[LVBound k := T]> Σ) = lty_env_atom_dom Σ.
Proof.
  unfold lty_env_atom_dom.
  rewrite (dom_insert_L (M:=gmap logic_var) (A:=ty) Σ (LVBound k) T).
  rewrite lvars_fv_union, lvars_fv_singleton_bound.
  set_solver.
Qed.

(** ** Denotation scoping regularity

    These syntactic facts isolate the variable-accounting needed by semantic
    subtyping reflexivity.  They are intentionally stated at the denotation
    layer: typing proofs should consume these regularity lemmas rather than
    unfolding the formula generated for each type constructor. *)

Lemma denot_ty_obligations_formula_fv_subset (Σe Στ : lty_env) τ e φ S :
  lty_env_atom_dom Σe ∪ lty_env_atom_dom Στ ∪ formula_fv φ ⊆ S →
  formula_fv (denot_ty_obligations Σe Στ τ e φ) ⊆ S.
Proof.
  intros Hsub.
  unfold denot_ty_obligations.
  unfold FBasicTypingIn, FClosedResourceIn, FStrongTotalIn,
    FStoreResourceAtom, FResourceAtom.
  cbn [formula_fv stale stale_logic_qualifier lqual_dom].
  denot_lvars_norm.
  rewrite lvars_fv_union.
  unfold lty_env_atom_dom.
  set_solver.
Qed.

Lemma denot_ty_fuel_lvar_formula_fv_subset gas Σe Στ τ e :
  cty_measure τ <= gas →
  formula_fv (denot_ty_fuel_lvar gas Σe Στ τ e) ⊆
    lty_env_atom_dom Σe ∪ lty_env_atom_dom Στ ∪ fv_cty τ.
Proof.
  induction gas as [|gas IH] in Σe, Στ, τ, e |- *; intros Hgas.
  - pose proof (cty_measure_gt_0 τ). lia.
  - destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τ|τx τ];
      cbn [cty_measure fv_cty denot_ty_fuel_lvar] in *;
      apply denot_ty_obligations_formula_fv_subset; simpl.
    + destruct φ as [D p]. cbn [qual_vars qual_dom].
      pose proof (FExprContIn_lty_env_formula_fv_subset Σe e
        (FAnd (FResultBasicWorld Στ b (qual_vars (qual D p)))
          (FFibVars (qual_vars (qual D p))
            (FOver (FTypeQualifier (qual D p)))))) as Hcont.
      cbn [qual_vars qual_dom] in Hcont.
      cbn [formula_fv] in Hcont.
      rewrite formula_fv_FResultBasicWorld in Hcont.
      unfold lty_env_bvar_scope in Hcont.
      rewrite !lvars_fv_union, lvars_fv_of_bvars,
        lvars_fv_singleton_bound in Hcont.
      rewrite formula_fv_FTypeQualifier in Hcont.
      cbn [qual_dom] in Hcont.
      set_solver.
    + destruct φ as [D p]. cbn [qual_vars qual_dom].
      pose proof (FExprContIn_lty_env_formula_fv_subset Σe e
        (FAnd (FResultBasicWorld Στ b (qual_vars (qual D p)))
          (FFibVars (qual_vars (qual D p))
            (FUnder (FTypeQualifier (qual D p)))))) as Hcont.
      cbn [qual_vars qual_dom] in Hcont.
      cbn [formula_fv] in Hcont.
      rewrite formula_fv_FResultBasicWorld in Hcont.
      unfold lty_env_bvar_scope in Hcont.
      rewrite !lvars_fv_union, lvars_fv_of_bvars,
        lvars_fv_singleton_bound in Hcont.
      rewrite formula_fv_FTypeQualifier in Hcont.
      cbn [qual_dom] in Hcont.
      set_solver.
    + pose proof (IH Σe Στ τ1 e ltac:(lia)) as H1.
      pose proof (IH Σe Στ τ2 e ltac:(lia)) as H2.
      set_solver.
    + pose proof (IH Σe Στ τ1 e ltac:(lia)) as H1.
      pose proof (IH Σe Στ τ2 e ltac:(lia)) as H2.
      set_solver.
    + pose proof (IH Σe Στ τ1 e ltac:(lia)) as H1.
      pose proof (IH Σe Στ τ2 e ltac:(lia)) as H2.
      set_solver.
    + set (Σex := <[LVBound 0:=erase_ty τx]>Σe).
      set (Στx := <[LVBound 0:=erase_ty τx]>Στ).
      pose proof (IH Σex Στ τx (tret (vbvar 0)) ltac:(lia)) as Hx.
      pose proof (IH Σex Στx τ (tapp_tm e (vbvar 0)) ltac:(lia)) as Hbody.
      subst Σex Στx.
      rewrite !lty_env_atom_dom_insert_bound in Hx.
      rewrite !lty_env_atom_dom_insert_bound in Hbody.
      cbn [formula_fv].
      transitivity
        (lty_env_atom_dom Σe ∪ lty_env_atom_dom Στ ∪
          (fv_cty τx ∪ fv_cty τ)).
      { set_solver. }
      set_solver.
    + set (Σex := <[LVBound 0:=erase_ty τx]>Σe).
      set (Στx := <[LVBound 0:=erase_ty τx]>Στ).
      pose proof (IH Σex Στ τx (tret (vbvar 0)) ltac:(lia)) as Hx.
      pose proof (IH Σex Στx τ (tapp_tm e (vbvar 0)) ltac:(lia)) as Hbody.
      subst Σex Στx.
      rewrite !lty_env_atom_dom_insert_bound in Hx.
      rewrite !lty_env_atom_dom_insert_bound in Hbody.
      cbn [formula_fv].
      transitivity
        (lty_env_atom_dom Σe ∪ lty_env_atom_dom Στ ∪
          (fv_cty τx ∪ fv_cty τ)).
      { set_solver. }
      set_solver.
Qed.

Lemma denot_ty_fuel_formula_fv_subset gas Σ τ e :
  cty_measure τ <= gas →
  formula_fv (denot_ty_fuel gas Σ τ e) ⊆ dom Σ ∪ fv_cty τ.
Proof.
  intros Hgas.
  unfold denot_ty_fuel.
  pose proof (denot_ty_fuel_lvar_formula_fv_subset
    gas (atom_env_to_lty_env Σ) (atom_env_to_lty_env Σ) τ e Hgas) as Hfv.
  rewrite !atom_env_to_lty_env_atom_dom in Hfv.
  set_solver.
Qed.

Lemma denot_ty_fuel_body_formula_fv_subset gas Σ τ e :
  cty_measure τ <= gas →
  formula_fv (denot_ty_fuel_body gas Σ τ e) ⊆ dom Σ ∪ fv_cty τ.
Proof.
  intros Hgas.
  pose proof (denot_ty_fuel_formula_fv_subset gas Σ τ e Hgas) as Hfv.
  rewrite denot_ty_fuel_unfold in Hfv.
  cbn [denot_ty_obligations formula_fv] in Hfv.
  set_solver.
Qed.

Lemma denot_ty_fuel_formula_fv_subset_env
    gas (Σ : gmap atom ty) (τ : choice_ty) e :
  cty_measure τ <= gas →
  fv_cty τ ⊆ dom Σ →
  formula_fv (denot_ty_fuel gas Σ τ e) ⊆ dom Σ.
Proof.
  intros Hgas Hfv.
  pose proof (denot_ty_fuel_formula_fv_subset gas Σ τ e Hgas) as Hφ.
  set_solver.
Qed.

Lemma denot_ty_fuel_body_formula_fv_subset_env
    gas (Σ : gmap atom ty) (τ : choice_ty) e :
  cty_measure τ <= gas →
  fv_cty τ ⊆ dom Σ →
  formula_fv (denot_ty_fuel_body gas Σ τ e) ⊆ dom Σ.
Proof.
  intros Hgas Hfv.
  pose proof (denot_ty_fuel_body_formula_fv_subset gas Σ τ e Hgas) as Hφ.
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
  intros _.
  rewrite denot_ty_fuel_unfold.
  unfold denot_ty_obligations, FBasicTypingIn, FClosedResourceIn,
    FStrongTotalIn, FStoreResourceAtom, FResourceAtom.
  cbn [formula_fv stale stale_logic_qualifier lqual_dom].
  denot_lvars_norm.
  rewrite !atom_env_to_lty_env_dom.
  rewrite !lvars_fv_union, !lvars_fv_of_atoms.
  set_solver.
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
