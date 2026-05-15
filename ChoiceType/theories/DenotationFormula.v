(** * ChoiceType.Denotation

    Denotational semantics for the choice type system (§1.5 of the paper).

    The interpretation is given as formulas in [Choice Logic] whose atoms are
    logic qualifiers.  Core expressions are embedded through
    [expr_logic_qual], and type qualifiers are embedded directly as
    store/resource atoms after they have been opened to closed atom-based
    qualifiers.

    The satisfaction notation [m ⊨ φ] is the central judgment used by
    the typing rules and the fundamental theorem. *)

From Stdlib Require Import Logic.FunctionalExtensionality Logic.PropExtensionality.
From LocallyNameless Require Import Tactics.
From CoreLang Require Import Instantiation InstantiationProps LocallyNamelessProps
  OperationalProps StrongNormalization.
From ChoiceType Require Export DenotationFibers.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

(** ** ChoiceLogic satisfaction, instantiated for qualifiers *)

(** Local abbreviation for the ChoiceType formula instantiation.  The exported
    name from [Prelude] is [FormulaQ]. *)
Local Notation FQ := FormulaQ.

#[global] Instance into_lvars_atom_ty_env : IntoLVars (gmap atom ty) :=
  fun Σ => lvars_of_atoms (dom Σ).

#[global] Instance into_lvars_logic_ty_env : IntoLVars (gmap logic_var ty) :=
  fun Σ => dom Σ.

Ltac denot_lvars_norm :=
  repeat match goal with
  | |- context[into_lvars ?X] =>
      let T := type of X in
      lazymatch T with
      | lvset => change (into_lvars X) with X
      | aset => change (into_lvars X) with (lvars_of_atoms X)
      | gmap atom ty => change (into_lvars X) with (lvars_of_atoms (dom X))
      | gmap logic_var ty => change (into_lvars X) with (dom X)
      end
  | H : context[into_lvars ?X] |- _ =>
      let T := type of X in
      lazymatch T with
      | lvset => change (into_lvars X) with X in H
      | aset => change (into_lvars X) with (lvars_of_atoms X) in H
      | gmap atom ty => change (into_lvars X) with (lvars_of_atoms (dom X)) in H
      | gmap logic_var ty => change (into_lvars X) with (dom X) in H
      end
  end.

(** Satisfaction: [m ⊨ φ]  ↔  [res_models m φ] *)
Notation "m ⊨ φ" :=
  (res_models m φ)
  (at level 70, format "m  ⊨  φ").

(** Entailment shorthand: [φ ⊫ ψ]  ↔  [∀ m, m ⊨ φ → m ⊨ ψ] *)
Notation "φ ⊫ ψ" :=
  (entails φ ψ)
  (at level 85, ψ at level 84, no associativity).

(** ** Logic atoms and fresh variable helpers for denotation *)


Definition expr_result_store (ν : atom) (eρ : tm) (σw : Store) : Prop :=
  ∃ v,
    σw = {[ν := v]} ∧
    stale v = ∅ ∧
    is_lc v ∧
    eρ →* tret v.

Lemma expr_result_store_elim ν eρ σw :
  expr_result_store ν eρ σw →
  ∃ v,
    σw = {[ν := v]} ∧
    stale v = ∅ ∧
    is_lc v ∧
    eρ →* tret v.
Proof. intros H. exact H. Qed.

Lemma expr_result_store_intro ν eρ v :
  stale v = ∅ →
  is_lc v →
  eρ →* tret v →
  expr_result_store ν eρ ({[ν := v]}).
Proof. intros Hstale Hlc Hsteps. exists v. repeat split; auto. Qed.

Lemma expr_result_store_lookup ν eρ σw :
  expr_result_store ν eρ σw →
  ∃ v, σw !! ν = Some v ∧ eρ →* tret v.
Proof.
  intros [v [-> [_ [_ Hsteps]]]].
  exists v. split; [rewrite lookup_singleton; rewrite decide_True by reflexivity; reflexivity |].
  exact Hsteps.
Qed.

Definition expr_result_in_world (ρ : Store) (e : tm) (ν : atom) (w : WfWorld) : Prop :=
  ∀ σν,
    (res_restrict w {[ν]} : World) σν ↔
    expr_result_store ν (subst_map ρ e) σν.

Lemma expr_result_in_world_sound ρ e ν w σw :
  expr_result_in_world ρ e ν w →
  (res_restrict w {[ν]} : World) σw →
  expr_result_store ν (subst_map ρ e) σw.
Proof. intros H Hw. exact (proj1 (H σw) Hw). Qed.

Lemma expr_result_in_world_complete ρ e ν w σw :
  expr_result_in_world ρ e ν w →
  expr_result_store ν (subst_map ρ e) σw →
  (res_restrict w {[ν]} : World) σw.
Proof. intros H Hσ. exact (proj2 (H σw) Hσ). Qed.

Lemma expr_result_in_world_store_elim ρ e ν w σw :
  expr_result_in_world ρ e ν w →
  (res_restrict w {[ν]} : World) σw →
  ∃ v,
    σw = {[ν := v]} ∧
    stale v = ∅ ∧
    is_lc v ∧
    subst_map ρ e →* tret v.
Proof.
  intros Hres Hw.
  exact (expr_result_store_elim ν (subst_map ρ e) σw
    (expr_result_in_world_sound ρ e ν w σw Hres Hw)).
Qed.

Definition open_tm_env (η : gmap nat atom) (e : tm) : tm :=
  map_fold (λ k x acc, open_tm k (vfvar x) acc) e η.

Lemma open_tm_env_singleton_lc k x e :
  lc_tm e →
  open_tm_env (<[k := x]> ∅) e = e.
Proof.
  intros Hlc.
  unfold open_tm_env.
  change (<[k := x]> ∅ : gmap nat atom) with ({[k := x]} : gmap nat atom).
  rewrite map_fold_singleton.
  apply open_rec_lc_tm. exact Hlc.
Qed.

Definition expr_logic_qual (e : tm) (ν : atom) : logic_qualifier :=
  lqual_fvars {[ν]} (fun σ w => expr_result_in_world σ e ν w).

Definition FExprResultOn {A : Type} `{IntoLVars A} (D : A) (e : tm) : FQ :=
  let L := into_lvars D in
  FFibVars L
    (FStoreResourceAtom (L ∪ {[LVBound 0]})
      (fun η σ w =>
        match η !! 0 with
        | Some ν =>
            expr_result_in_world (store_restrict σ (lvars_fv L))
              (open_tm_env η e) ν w
        | None => False
        end)).

Definition FExprResultAt {A : Type} `{IntoLVars A}
    (D : A) (e : tm) (ν : atom) : FQ :=
  formula_open 0 ν (FExprResultOn D e).

Lemma FExprResultOn_fv X e :
  formula_fv (FExprResultOn X e) = X.
Proof.
  unfold FExprResultOn, FStoreResourceAtom.
  cbn [formula_fv stale stale_logic_qualifier lqual_dom into_lvars
    into_lvars_aset into_lvars_lvset].
  denot_lvars_norm.
  rewrite lvars_fv_union, !lvars_fv_of_atoms, lvars_fv_singleton_bound.
  set_solver.
Qed.

Lemma FExprResultOn_fv_subset X e :
  formula_fv (FExprResultOn X e) ⊆ X.
Proof.
  rewrite FExprResultOn_fv. set_solver.
Qed.

Lemma FExprResultAt_fv_subset X e ν :
  formula_fv (FExprResultAt X e ν) ⊆ X ∪ {[ν]}.
Proof.
  unfold FExprResultAt.
  pose proof (formula_open_fv_subset 0 ν (FExprResultOn X e)) as Hopen.
  rewrite FExprResultOn_fv in Hopen.
  set_solver.
Qed.

Lemma FExprResultAt_fv X e ν :
  formula_fv (FExprResultAt X e ν) = X ∪ {[ν]}.
Proof.
  unfold FExprResultAt, FExprResultOn, FStoreResourceAtom.
  cbn [formula_open formula_fv stale stale_logic_qualifier lqual_dom
    lqual_open into_lvars into_lvars_aset into_lvars_lvset].
  denot_lvars_norm.
  rewrite lvars_open_of_atoms.
  rewrite lvars_fv_of_atoms.
  rewrite lvars_fv_open_atoms_with_bound.
  set_solver.
Qed.

Ltac denot_sugar_norm :=
  denot_lvars_norm.

(** [FExprContIn Σ e Q] abbreviates [∀ν. FExprResultOn (dom Σ) e ⇒ Q].
    The postcondition [Q] is an LN body: [LVBound 0] names the result
    coordinate introduced by the surrounding [FForall]. *)
Definition FExprContIn {E : Type} `{IntoLVars E}
    (Σ : E) (e : tm) (Q : FQ) : FQ :=
  FForall (FImpl (FExprResultOn (into_lvars Σ) e) Q).

Lemma FExprContIn_formula_fv_subset
    (Σ : gmap atom ty) e (S : aset) (Q : FQ) :
  dom Σ ⊆ S →
  formula_fv Q ⊆ S →
  formula_fv (FExprContIn Σ e Q) ⊆ S.
Proof.
  intros HΣ HQ.
  unfold FExprContIn.
  cbn [formula_fv].
  denot_lvars_norm.
  unfold FExprResultOn at 1.
  unfold FStoreResourceAtom.
  cbn [formula_fv stale stale_logic_qualifier lqual_dom into_lvars
    into_lvars_lvset].
  denot_lvars_norm.
  rewrite lvars_fv_union, lvars_fv_of_atoms, lvars_fv_singleton_bound.
  set_solver.
Qed.

Lemma FExprContIn_post_eq
    (Σ : gmap atom ty) e (P Q : FQ) :
  P = Q →
  FExprContIn Σ e P = FExprContIn Σ e Q.
Proof.
  intros ->. reflexivity.
Qed.

Lemma stale_expr_logic_qual e ν :
  stale (expr_logic_qual e ν) = {[ν]}.
Proof.
  unfold expr_logic_qual, stale, stale_logic_qualifier, lqual_dom, lqual_fvars.
  simpl. rewrite lvars_fv_of_atoms. reflexivity.
Qed.

Lemma FExprResultOn_scoped_dom X e ν m :
  formula_scoped_in_world ∅ m (FExprResultAt X e ν) →
  X ∪ {[ν]} ⊆ world_dom (m : World).
Proof.
  intros Hscope z Hz.
  apply Hscope.
  rewrite dom_empty_L.
  apply elem_of_union_r.
  rewrite FExprResultAt_fv.
  exact Hz.
Qed.

(** Prop-level totality for the expression component of a type denotation.

    This is intentionally not encoded as a ChoiceLogic formula.  Since the core
    language is deterministic, totality is recorded as result reachability for
    every store in the world. *)
Definition expr_total_on (X : aset) (e : tm) (m : WfWorld) : Prop :=
  fv_tm e ⊆ X ∧
  ∀ σ, (m : World) σ →
    ∃ vx, subst_map (store_restrict σ X) e →* tret vx.

(** [world_closed_on X m] is the ChoiceType-level invariant saying that every
    store in [m] is operationally usable on the coordinates [X].  This belongs
    here rather than in ChoiceAlgebra: the algebra is polymorphic in store
    values, while closedness is a CoreLang [value] property. *)
Definition world_closed_on (X : aset) (m : WfWorld) : Prop :=
  ∀ σ, (m : World) σ → store_closed (store_restrict σ X).

Lemma world_closed_on_le X m n :
  m ⊑ n →
  world_closed_on X n →
  world_closed_on X m.
Proof.
  intros Hle Hclosed σ Hσ.
  unfold world_closed_on in Hclosed.
  unfold sqsubseteq, wf_world_sqsubseteq, raw_le in Hle.
  change ((m : World) σ) in Hσ.
  rewrite Hle in Hσ. simpl in Hσ.
  destruct Hσ as [σn [Hσn Hrestrict]].
  rewrite <- Hrestrict.
  rewrite !store_restrict_restrict.
  replace (world_dom (m : World) ∩ X) with (X ∩ world_dom (m : World))
    by set_solver.
  rewrite <- store_restrict_restrict.
  apply store_closed_restrict.
  exact (Hclosed σn Hσn).
Qed.

Lemma basic_world_formula_world_closed_on Σ X m :
  X ⊆ dom Σ →
  m ⊨ basic_world_formula Σ X →
  world_closed_on X m.
Proof.
  intros HXΣ Hbasic σ Hσ.
  split.
  - eapply basic_world_formula_store_restrict_closed_env; eauto.
  - eapply basic_world_formula_store_restrict_lc_env; eauto.
Qed.

Lemma expr_result_store_let_elim ρ e1 e2 ν σw :
  expr_result_store ν (subst_map ρ (tlete e1 e2)) σw →
  ∃ v vx,
    σw = {[ν := v]} ∧
    subst_map ρ e1 →* tret vx ∧
    open_tm 0 vx (subst_map ρ e2) →* tret v.
Proof.
  intros Hstore.
  destruct (expr_result_store_elim ν (subst_map ρ (tlete e1 e2)) σw Hstore)
    as [v [Hσw [_ [_ Hsteps]]]].
  change (subst_map ρ (tlete e1 e2)) with (m{ρ} (tlete e1 e2)) in Hsteps.
  rewrite msubst_lete in Hsteps.
  destruct (reduction_lete (m{ρ} e1) (m{ρ} e2) v Hsteps)
    as [vx [Hsteps1 Hsteps2]].
  exists v, vx. repeat split; assumption.
Qed.

Lemma expr_result_in_world_let_elim ρ e1 e2 ν (w : WfWorld) :
  expr_result_in_world ρ (tlete e1 e2) ν w →
  ∀ σν,
    (res_restrict w {[ν]} : World) σν →
    ∃ v vx,
      σν = {[ν := v]} ∧
      subst_map ρ e1 →* tret vx ∧
      open_tm 0 vx (subst_map ρ e2) →* tret v.
Proof.
  intros Hworld σν Hσν.
  pose proof (expr_result_in_world_sound ρ (tlete e1 e2) ν w σν
    Hworld Hσν) as Hstore.
  exact (expr_result_store_let_elim ρ e1 e2 ν σν Hstore).
Qed.

Lemma expr_result_store_let_intro ρ e1 e2 ν v vx :
  stale v = ∅ →
  is_lc v →
  body_tm (subst_map ρ e2) →
  subst_map ρ e1 →* tret vx →
  open_tm 0 vx (subst_map ρ e2) →* tret v →
  expr_result_store ν (subst_map ρ (tlete e1 e2)) {[ν := v]}.
Proof.
  intros Hv_closed Hv_lc Hbody Hsteps1 Hsteps2.
  apply expr_result_store_intro; [exact Hv_closed | exact Hv_lc |].
  change (subst_map ρ (tlete e1 e2)) with (m{ρ} (tlete e1 e2)).
  rewrite msubst_lete.
  eapply reduction_lete_intro; eauto.
Qed.

Lemma expr_result_in_world_let_intro ρ e1 e2 ν (w : WfWorld) :
  body_tm (subst_map ρ e2) →
  (∀ σν,
    (res_restrict w {[ν]} : World) σν ↔
    ∃ v vx,
      σν = {[ν := v]} ∧
      stale v = ∅ ∧
      is_lc v ∧
      subst_map ρ e1 →* tret vx ∧
      open_tm 0 vx (subst_map ρ e2) →* tret v) →
  expr_result_in_world ρ (tlete e1 e2) ν w.
Proof.
  intros Hbody Hexact σν. split.
  - intros Hσν.
    destruct (proj1 (Hexact σν) Hσν)
      as [v [vx [Hσν_eq [Hv_closed [Hv_lc [Hsteps1 Hsteps2]]]]]].
    subst σν.
    eapply expr_result_store_let_intro; eauto.
  - intros Hstore.
    destruct (expr_result_store_elim ν (subst_map ρ (tlete e1 e2)) σν Hstore)
      as [v [Hσν_eq [Hv_closed [Hv_lc Hsteps]]]].
    destruct (expr_result_store_let_elim ρ e1 e2 ν σν Hstore)
      as [v' [vx [Hσν_eq' [Hsteps1 Hsteps2]]]].
    subst σν.
    assert (Hv' : v' = v).
    {
      assert (({[ν := v']} : Store) !! ν = Some v).
      {
        rewrite <- Hσν_eq'.
        rewrite lookup_singleton. rewrite decide_True by reflexivity.
        reflexivity.
      }
      rewrite lookup_singleton in H.
      rewrite decide_True in H by reflexivity.
      inversion H. reflexivity.
    }
    subst v'.
    apply (proj2 (Hexact {[ν := v]})).
    exists v, vx. repeat split; eauto.
Qed.

Lemma expr_result_store_tlete_to_body_open_atom ρ e1 e2 x ν σν :
  closed_env ρ →
  lc_env ρ →
  x ∉ dom ρ ∪ fv_tm e2 →
  (∀ vx, subst_map ρ e1 →* tret vx → stale vx = ∅ ∧ is_lc vx) →
  expr_result_store ν (subst_map ρ (tlete e1 e2)) σν →
  ∃ vx,
    subst_map ρ e1 →* tret vx ∧
    expr_result_store ν (subst_map (<[x := vx]> ρ) (e2 ^^ x)) σν.
Proof.
  intros Hclosed Hlc Hx Hresult_closed Hstore.
  destruct (expr_result_store_elim ν (subst_map ρ (tlete e1 e2)) σν Hstore)
    as [v [Hσν [Hv_closed [Hv_lc _]]]].
  destruct (expr_result_store_let_elim ρ e1 e2 ν σν Hstore)
    as [v' [vx [Hσν' [Hsteps1 Hsteps2]]]].
  subst σν.
  assert (Hv' : v' = v).
  {
    assert (({[ν := v']} : Store) !! ν = Some v).
    {
      rewrite <- Hσν'.
      rewrite lookup_singleton. rewrite decide_True by reflexivity.
      reflexivity.
    }
    rewrite lookup_singleton in H.
    rewrite decide_True in H by reflexivity.
    inversion H. reflexivity.
  }
  subst v'.
  exists vx. split; [exact Hsteps1 |].
  apply expr_result_store_intro; [exact Hv_closed | exact Hv_lc |].
  change (subst_map (<[x := vx]> ρ) (e2 ^^ x)) with
    (m{<[x := vx]> ρ} (open_tm 0 (vfvar x) e2)).
  rewrite (msubst_intro_open_tm e2 0 vx x ρ).
  - exact Hsteps2.
  - exact Hclosed.
  - apply (proj1 (Hresult_closed vx Hsteps1)).
  - apply (proj2 (Hresult_closed vx Hsteps1)).
  - exact Hlc.
  - exact Hx.
Qed.

Lemma expr_result_store_ret_fvar_lookup x ν σw vx :
  stale vx = ∅ →
  σw !! x = Some vx →
  expr_result_store ν (subst_map ∅ (tret (vfvar x))) σw →
  σw !! ν = Some vx.
Proof.
  intros _ _ Hret.
  destruct (expr_result_store_elim ν (subst_map ∅ (tret (vfvar x))) σw Hret)
    as [v [-> [Hv_stale [_ Hsteps]]]].
  simpl in Hsteps.
  pose proof (value_steps_self (vfvar x) (tret v) Hsteps) as Heq.
  inversion Heq. subst v.
  simpl in Hv_stale. set_solver.
Qed.

Lemma expr_result_store_ret_fvar_trans ρ e x ν σw :
  (∀ vx, subst_map σw (subst_map ρ e) →* tret vx → stale vx = ∅) →
  expr_result_store x (subst_map ρ e) σw →
  expr_result_store ν (subst_map ∅ (tret (vfvar x))) σw →
  expr_result_store ν (subst_map ρ e) σw.
Proof.
  intros _ _ Hret.
  destruct (expr_result_store_elim ν (subst_map ∅ (tret (vfvar x))) σw Hret)
    as [v [-> [Hv_stale [_ Hsteps]]]].
  simpl in Hsteps.
  pose proof (value_steps_self (vfvar x) (tret v) Hsteps) as Heq.
  inversion Heq. subst v.
  simpl in Hv_stale. set_solver.
Qed.

Lemma expr_result_in_world_ret_fvar_trans ρ e x ν (w : WfWorld) :
  (∀ σw vx,
    (w : World) σw →
    subst_map σw (subst_map ρ e) →* tret vx →
    stale vx = ∅) →
  expr_result_in_world ρ e x w →
  expr_result_in_world ∅ (tret (vfvar x)) ν w →
  expr_result_in_world ρ e ν w.
Proof.
  intros _ _ Hret_world.
  exfalso.
  destruct (world_wf w) as [[σ Hσ] _].
  set (σν := store_restrict σ {[ν]}).
  assert (Hprojν : (res_restrict w {[ν]} : World) σν).
  { exists σ. split; [exact Hσ | reflexivity]. }
  pose proof (expr_result_in_world_sound ∅ (tret (vfvar x)) ν w σν
    Hret_world Hprojν) as Hret.
  destruct (expr_result_store_elim ν (subst_map ∅ (tret (vfvar x))) σν Hret)
    as [v [-> [Hv_stale [_ Hsteps]]]].
  simpl in Hsteps.
  pose proof (value_steps_self (vfvar x) (tret v) Hsteps) as Heq.
  inversion Heq. subst v.
  simpl in Hv_stale. set_solver.
Qed.
