(** * ChoiceType.Denotation

    Denotational semantics for the choice type system (§1.5 of the paper).

    The interpretation is given as formulas in [Choice Logic] whose atoms are
    logic qualifiers.  Core expressions are embedded through
    expression-result formulas, and type qualifiers are embedded directly as
    store/resource atoms after they have been opened to closed atom-based
    qualifiers.

    The satisfaction notation [m ⊨ φ] is the central judgment used by
    the typing rules and the fundamental theorem. *)

From Stdlib Require Import Logic.FunctionalExtensionality Logic.PropExtensionality.
From LocallyNameless Require Import Tactics.
From CoreLang Require Import Instantiation InstantiationProps LocallyNamelessProps
  OperationalProps StrongNormalization Sugar.
From ChoiceType Require Export DenotationFibers.
From ChoiceType Require Import BasicStore BasicTyping LocallyNamelessProps.

(** ** ChoiceLogic satisfaction, instantiated for qualifiers *)

(** Local abbreviation for the ChoiceType formula instantiation.  The exported
    name from [Prelude] is [FormulaQ]. *)
Local Notation FQ := FormulaQ.

Class MOpen Env A B := mopen : Env → A → B.

Class MOpenInsertLaws A B `{Open atom A}
    `{MOpen (gmap nat atom) A B} := {
  mopen_insert_norm :
    ∀ k x η (a : A),
      mopen η ({k ~> x} a) = mopen (<[k := x]> η) a;
}.

Notation "η ⊙ x" := (mopen η x)
  (at level 30, right associativity, format "η  ⊙  x").

Ltac mopen_norm :=
  rewrite ?mopen_insert_norm.

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

Definition expr_result_in_world (ρ : Store) (e : tm) (ν : atom) (w : WfWorld) : Prop :=
  ∀ σν,
    (res_restrict w {[ν]} : World) σν ↔
    expr_result_store ν (subst_map ρ e) σν.

Lemma expr_result_in_world_sound ρ e ν w σw :
  expr_result_in_world ρ e ν w →
  (res_restrict w {[ν]} : World) σw →
  expr_result_store ν (subst_map ρ e) σw.
Proof. intros H Hw. exact (proj1 (H σw) Hw). Qed.

Definition open_tm_env (η : gmap nat atom) (e : tm) : tm :=
  map_fold (λ k x acc, open_tm k (vfvar x) acc) e η.

#[global] Instance mopen_tm_inst :
  MOpen (gmap nat atom) tm tm := open_tm_env.

Lemma open_tm_env_singleton k x e :
  open_tm_env (<[k := x]> ∅) e = open_tm k (vfvar x) e.
Proof.
  unfold open_tm_env.
  change (<[k := x]> ∅ : gmap nat atom) with ({[k := x]} : gmap nat atom).
  rewrite map_fold_singleton. reflexivity.
Qed.

Lemma open_tm_env_singleton_lc k x e :
  lc_tm e →
  open_tm_env (<[k := x]> ∅) e = e.
Proof.
  intros Hlc.
  rewrite open_tm_env_singleton.
  apply open_rec_lc_tm. exact Hlc.
Qed.

Lemma open_tm_env_lc η e :
  lc_tm e →
  open_tm_env η e = e.
Proof.
  intros Hlc.
  unfold open_tm_env.
  refine (fin_maps.map_fold_ind
    (fun η => map_fold
      (λ k x acc, open_tm k (vfvar x) acc) e η = e) _ _ η).
  - rewrite map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite Hfold, IH.
    apply open_rec_lc_tm. exact Hlc.
Qed.

Lemma open_tm_env_open_tm k x η e :
  open_tm_env η (open_tm k (vfvar x) e) =
  open_tm_env (<[k := x]> η) e.
Proof.
  (* Standard mopen composition for terms.  This should be proved by the
     locally-nameless open-commutation lemmas, not by unfolding users of
     [open_tm_env]. *)
Admitted.

Lemma open_tm_env_shift_open_one η k x e :
  open_tm_env η (tm_shift 0 (open_tm k (vfvar x) e)) =
  open_tm_env (<[S k := x]> η) (tm_shift 0 e).
Proof.
  (* Binder-under-result normalization: opening the body at [k] and then
     shifting under the result binder is the same as interpreting the shifted
     body in an environment extended at [S k]. *)
Admitted.

#[global] Instance mopen_insert_tm_inst : MOpenInsertLaws tm tm := {
  mopen_insert_norm := open_tm_env_open_tm
}.

Definition FExprResultAtLvar {A : Type} `{IntoLVars A}
    (D : A) (e : tm) (ν : logic_var) : FQ :=
  let L := into_lvars D in
  FFibVars L
    (FStoreResourceAtom (L ∪ {[ν]})
      (fun η σ w =>
        match logic_var_to_atom η ν with
        | Some x =>
            expr_result_in_world (store_restrict σ (lvars_to_atoms η L))
              (open_tm_env η e) x w
        | None => False
        end)).

Definition FExprResultOn {A : Type} `{IntoLVars A} (D : A) (e : tm) : FQ :=
  FExprResultAtLvar (lvars_shift (into_lvars D)) (tm_shift 0 e) (LVBound 0).

Definition FExprResultAt {A : Type} `{IntoLVars A}
    (D : A) (e : tm) (ν : atom) : FQ :=
  FExprResultAtLvar D e (LVFree ν).

Lemma formula_open_FExprResultAtLvar_raw {A : Type} `{IntoLVars A}
    k x (D : A) (e : tm) (ν : logic_var) :
  formula_open k x (FExprResultAtLvar D e ν) =
  let L := into_lvars D in
  FFibVars (lvars_open k x L)
    (FStoreResourceAtom (lvars_open k x (L ∪ {[ν]}))
      (fun η σ w =>
        match logic_var_to_atom (<[k := x]> η) ν with
        | Some y =>
            expr_result_in_world
              (store_restrict σ (lvars_to_atoms (<[k := x]> η) L))
              (open_tm_env (<[k := x]> η) e) y w
        | None => False
        end)).
Proof. reflexivity. Qed.

Lemma FExprResultAtLvar_fv {A : Type} `{IntoLVars A}
    (D : A) e ν :
  formula_fv (FExprResultAtLvar D e ν) =
  lvars_fv (into_lvars D ∪ {[ν]}).
Proof.
  unfold FExprResultAtLvar, FStoreResourceAtom.
  cbn [formula_fv stale stale_logic_qualifier lqual_dom].
  denot_lvars_norm.
  rewrite lvars_fv_union.
  set_solver.
Qed.

Lemma FExprResultOn_lvars_fv {A : Type} `{IntoLVars A} (D : A) e :
  formula_fv (FExprResultOn D e) = lvars_fv (into_lvars D).
Proof.
  unfold FExprResultOn.
  rewrite FExprResultAtLvar_fv.
  change (into_lvars (lvars_shift (into_lvars D)))
    with (lvars_shift (into_lvars D)).
  rewrite lvars_fv_union, lvars_fv_singleton_bound.
  rewrite lvars_fv_shift.
  set_solver.
Qed.

Lemma FExprResultOn_fv X e :
  formula_fv (FExprResultOn X e) = X.
Proof.
  rewrite FExprResultOn_lvars_fv.
  cbn [into_lvars into_lvars_aset].
  apply lvars_fv_of_atoms.
Qed.

Lemma FExprResultAt_fv X e ν :
  formula_fv (FExprResultAt X e ν) = X ∪ {[ν]}.
Proof.
  unfold FExprResultAt.
  rewrite FExprResultAtLvar_fv.
  denot_lvars_norm.
  rewrite lvars_fv_union, lvars_fv_of_atoms, lvars_fv_singleton_free.
  set_solver.
Qed.

Lemma lvars_shift_of_atoms X :
  lvars_shift (lvars_of_atoms X) = lvars_of_atoms X.
Proof.
  unfold lvars_shift, lvars_of_atoms.
  apply set_eq. intros v.
  rewrite !elem_of_map.
  split.
  - intros [w [-> Hw]].
    rewrite elem_of_map in Hw.
    destruct Hw as [x [-> Hx]].
    exists x. split; [reflexivity | exact Hx].
  - intros [x [-> Hx]].
    exists (LVFree x). split; [reflexivity |].
    rewrite elem_of_map.
    exists x. split; [reflexivity | exact Hx].
Qed.

Lemma lvars_open_shift_of_atoms k x X :
  lvars_open k x (lvars_shift (lvars_of_atoms X)) = lvars_of_atoms X.
Proof.
  rewrite lvars_shift_of_atoms.
  apply lvars_open_of_atoms.
Qed.

Lemma lvars_to_atoms_shift_of_atoms η X :
  lvars_to_atoms η (lvars_shift (lvars_of_atoms X)) = X.
Proof.
  rewrite lvars_shift_of_atoms.
  apply lvars_to_atoms_of_atoms.
Qed.

Lemma lvars_to_atoms_insert_empty_subset k x D :
  lvars_to_atoms (<[k := x]> ∅) D ⊆ lvars_fv D ∪ {[x]}.
Proof.
  (* Pure lvar interpretation fact: with only [k ↦ x] in the environment,
     interpreting [D] can produce only the free atoms already in [D] plus [x]. *)
Admitted.

Lemma lvars_to_atoms_open η k x D :
  lvars_to_atoms η (lvars_open k x D) =
  lvars_to_atoms (<[k := x]> η) D.
Proof.
  (* Pure syntax normalization: opening an lvar set and then interpreting it
     equals interpreting the original set in the environment extended by the
     freshly chosen atom. *)
Admitted.

Lemma lvars_to_atoms_shift_open_one η k x D :
  lvars_to_atoms η (lvars_shift (lvars_open k x D)) =
  lvars_to_atoms (<[S k := x]> η) (lvars_shift D).
Proof.
  rewrite <- lvars_to_atoms_open.
  (* The remaining step is [open (S k)] commuting through [shift]. *)
Admitted.

Lemma open_tm_env_shift_lc η k e :
  lc_tm e →
  open_tm_env η (tm_shift k e) = e.
Proof.
  intros Hlc.
  rewrite (tm_shift_lc_id k e Hlc).
  apply open_tm_env_lc. exact Hlc.
Qed.

Lemma formula_open_FExprResultAtLvar_shift_atom X e ν :
  lc_tm e →
  formula_open 0 ν
    (FExprResultAtLvar (lvars_shift (lvars_of_atoms X))
      (tm_shift 0 e) (LVBound 0)) =
  FExprResultAt X e ν.
Proof.
  intros Hlc.
  rewrite formula_open_FExprResultAtLvar_raw.
  unfold FExprResultAt, FExprResultAtLvar.
  denot_lvars_norm.
  rewrite lvars_open_shift_of_atoms.
  unfold lvars_open at 1.
  rewrite set_map_union_L.
  fold (lvars_open 0 ν (lvars_shift (lvars_of_atoms X))).
  fold (lvars_open 0 ν ({[LVBound 0]} : lvset)).
  rewrite lvars_open_shift_of_atoms.
  unfold lvars_open at 1.
  rewrite set_map_singleton_L.
  cbn [logic_var_open].
  destruct (decide (0 = 0)) as [_|Hneq]; [|congruence].
  cbn [logic_var_to_atom].
  f_equal.
  f_equal.
  apply functional_extensionality; intro η.
  apply functional_extensionality; intro σ.
  apply functional_extensionality; intro w.
  rewrite lvars_to_atoms_shift_of_atoms.
  rewrite lvars_to_atoms_of_atoms.
  rewrite open_tm_env_shift_lc by exact Hlc.
  rewrite open_tm_env_lc by exact Hlc.
  rewrite lookup_insert_eq.
  reflexivity.
Qed.

(** [FExprContIn Σ e Q] abbreviates [∀ν. FExprResultOn (dom Σ) e ⇒ Q].
    The postcondition [Q] is an LN body: [LVBound 0] names the result
    coordinate introduced by the surrounding [FForall]. *)
Definition FExprContIn {E : Type} `{IntoLVars E}
    (Σ : E) (e : tm) (Q : FQ) : FQ :=
  FForall
    (FImpl
      (FExprResultAtLvar (lvars_shift (into_lvars Σ))
        (tm_shift 0 e) (LVBound 0))
      Q).

Lemma formula_open_FExprContIn_raw {E : Type} `{IntoLVars E}
    k x (Σ : E) e Q :
  formula_open k x (FExprContIn Σ e Q) =
  FForall
    (FImpl
      (formula_open (S k) x
        (FExprResultAtLvar (lvars_shift (into_lvars Σ))
          (tm_shift 0 e) (LVBound 0)))
      (formula_open (S k) x Q)).
Proof. reflexivity. Qed.

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
  rewrite FExprResultAtLvar_fv.
  cbn [into_lvars into_lvars_lvset].
  denot_lvars_norm.
  rewrite lvars_fv_union, lvars_fv_shift, lvars_fv_of_atoms,
    lvars_fv_singleton_bound.
  set_solver.
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
Definition expr_total_on (e : tm) (m : WfWorld) : Prop :=
  fv_tm e ⊆ world_dom (m : World) ∧
  ∀ σ, (m : World) σ →
    ∃ vx, subst_map (store_restrict σ (fv_tm e)) e →* tret vx.

Notation "m '|=total' e" := (expr_total_on e m)
  (at level 70, e at next level).

Lemma expr_total_on_restrict_self X e (m : WfWorld) :
  fv_tm e ⊆ X →
  expr_total_on e m →
  expr_total_on e (res_restrict m X).
Proof.
  intros HfvX [Hfv Htotal]. split; [simpl; set_solver |].
  intros σ [σm [Hσm <-]].
  rewrite store_restrict_twice_subset by exact HfvX.
  apply Htotal. exact Hσm.
Qed.

(** [world_closed_on X m] is the ChoiceType-level invariant saying that every
    store in [m] is operationally usable on the coordinates [X].  This belongs
    here rather than in ChoiceAlgebra: the algebra is polymorphic in store
    values, while closedness is a CoreLang [value] property. *)
Definition world_closed_on (X : aset) (m : WfWorld) : Prop :=
  ∀ σ, (m : World) σ → store_closed (store_restrict σ X).

#[global] Instance scoped_wf_world : ScopedIn WfWorld := world_closed_on.

Module WorldScopingNotationSmoke.
  Section Smoke.
    Variable X : aset.
    Variable m : WfWorld.

    Example scoped_world_notation :
      (X ⊢s m) = world_closed_on X m := eq_refl.
  End Smoke.
End WorldScopingNotationSmoke.

Lemma scoped_world_iff X m :
  X ⊢s m ↔ world_closed_on X m.
Proof. reflexivity. Qed.

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
  rewrite store_restrict_comm.
  apply store_closed_restrict.
  exact (Hclosed σn Hσn).
Qed.

Lemma expr_total_on_tlete_elim_e1_strong X e1 e2 (m : WfWorld) :
  fv_tm (tlete e1 e2) ⊆ X →
  world_closed_on X m →
  expr_total_on (tlete e1 e2) m →
  expr_total_on e1 m.
Proof.
  intros HfvX Hclosed [Hfv Htotal].
  split; [simpl in Hfv; set_solver |].
  intros σ Hσ.
  destruct (Htotal σ Hσ) as [v Hsteps].
  rewrite (subst_map_restrict_to_fv_from_superset
    (tlete e1 e2) X σ HfvX (proj1 (Hclosed σ Hσ))) in Hsteps.
  change (m{store_restrict σ X} (tlete e1 e2) →* tret v) in Hsteps.
  rewrite msubst_lete in Hsteps.
  apply reduction_lete in Hsteps as [vx [HstepsX _]].
  exists vx.
  rewrite (subst_map_restrict_to_fv_from_superset e1
    X σ ltac:(simpl in HfvX; set_solver)).
  - exact HstepsX.
  - exact (proj1 (Hclosed σ Hσ)).
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

Lemma expr_result_store_body_open_to_tlete ρ e1 e2 x ν σν vx :
  closed_env ρ →
  lc_env ρ →
  body_tm (subst_map ρ e2) →
  x ∉ dom ρ ∪ fv_tm e2 →
  stale vx = ∅ →
  is_lc vx →
  subst_map ρ e1 →* tret vx →
  expr_result_store ν (subst_map (<[x := vx]> ρ) (e2 ^^ x)) σν →
  expr_result_store ν (subst_map ρ (tlete e1 e2)) σν.
Proof.
  intros Hclosed Hlc Hbody Hx Hv_closed Hv_lc Hsteps1 Hstore.
  destruct (expr_result_store_elim ν
    (subst_map (<[x := vx]> ρ) (e2 ^^ x)) σν Hstore)
    as [v [Hσν [Hres_closed [Hres_lc Hsteps2]]]].
  subst σν.
  eapply expr_result_store_let_intro; eauto.
  change (subst_map (<[x := vx]> ρ) (e2 ^^ x)) with
    (m{<[x := vx]> ρ} (open_tm 0 (vfvar x) e2)) in Hsteps2.
  rewrite (msubst_intro_open_tm e2 0 vx x ρ) in Hsteps2.
  - exact Hsteps2.
  - exact Hclosed.
  - exact Hv_closed.
  - exact Hv_lc.
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
