(** * ChoiceType.DenotationType

    Choice-type denotation and formula-locality lemmas. *)

From LocallyNameless Require Import Tactics.
From CoreLang Require Import Instantiation InstantiationProps BasicTypingProps
  LocallyNamelessProps OperationalProps StrongNormalization Sugar.
From ChoiceLogic Require Import FormulaDerived.
From ChoiceType Require Export DenotationFormulaEquiv.
From ChoiceType Require Import BasicStore BasicTyping LocallyNamelessProps.

Local Notation FQ := FormulaQ.

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

Lemma open_cty_env_empty τ :
  open_cty_env ∅ τ = τ.
Proof. unfold open_cty_env. rewrite map_fold_empty. reflexivity. Qed.

Lemma open_tm_env_empty e :
  open_tm_env ∅ e = e.
Proof. unfold open_tm_env. rewrite map_fold_empty. reflexivity. Qed.

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

Lemma atom_env_to_lty_env_lookup_bound_none Σ k :
  atom_env_to_lty_env Σ !! LVBound k = None.
Proof.
  apply not_elem_of_dom.
  rewrite atom_env_to_lty_env_dom.
  intros Hin.
  unfold lvars_of_atoms in Hin.
  rewrite elem_of_map in Hin.
  destruct Hin as [y [Hy _]].
  congruence.
Qed.

Lemma lty_env_open_atom_env η Σ :
  lty_env_open η (atom_env_to_lty_env Σ) = Σ.
Proof.
  unfold atom_env_to_lty_env.
  refine (fin_maps.map_fold_ind
    (fun Σ =>
      lty_env_open η
        (map_fold
          (fun (x : atom) (T : ty) (acc : lty_env) =>
            <[LVFree x := T]> acc) ∅ Σ) = Σ) _ _ Σ).
  - unfold lty_env_open. rewrite map_fold_empty. reflexivity.
  - intros x T Σ' Hfresh Hfold IH.
    rewrite Hfold.
    unfold lty_env_open in *.
    rewrite (map_fold_insert_L
      (M:=gmap logic_var)
      (fun v U acc =>
        match lvar_to_atom η v with
        | Some y => <[y:=U]> acc
        | None => acc
        end)
      (∅ : gmap atom ty) (LVFree x) T
      (map_fold
        (fun (x : atom) (T : ty) (acc : lty_env) =>
          <[LVFree x:=T]> acc) ∅ Σ')).
    + cbn [lvar_to_atom].
      change (map_fold
        (fun v U acc =>
          match lvar_to_atom η v with
          | Some y => <[y:=U]> acc
          | None => acc
          end)
        ∅
        (map_fold
          (fun (x : atom) (T : ty) (acc : lty_env) =>
            <[LVFree x:=T]> acc) ∅ Σ')) with
        (lty_env_open η
          (map_fold
            (fun (x : atom) (T : ty) (acc : lty_env) =>
              <[LVFree x:=T]> acc) ∅ Σ')).
      change (lty_env_open η
          (map_fold
            (fun (x : atom) (T : ty) (acc : lty_env) =>
              <[LVFree x:=T]> acc) ∅ Σ') = Σ') in IH.
      rewrite IH. reflexivity.
    + intros i j Ti Tj acc Hne Hi Hj.
      cbn [lvar_to_atom] in *.
      destruct i as [ki|xi], j as [kj|xj]; cbn [lvar_to_atom] in *;
        try reflexivity.
      * rewrite lookup_insert_ne in Hi by congruence.
        change (map_fold
          (fun (x0 : atom) (T0 : ty) (acc0 : lty_env) =>
            <[LVFree x0:=T0]> acc0) ∅ Σ')
          with (atom_env_to_lty_env Σ') in Hi.
        rewrite atom_env_to_lty_env_lookup_bound_none in Hi. discriminate.
      * rewrite lookup_insert_ne in Hi by congruence.
        change (map_fold
          (fun (x0 : atom) (T0 : ty) (acc0 : lty_env) =>
            <[LVFree x0:=T0]> acc0) ∅ Σ')
          with (atom_env_to_lty_env Σ') in Hi.
        rewrite atom_env_to_lty_env_lookup_bound_none in Hi. discriminate.
      * rewrite lookup_insert_ne in Hj by congruence.
        change (map_fold
          (fun (x0 : atom) (T0 : ty) (acc0 : lty_env) =>
            <[LVFree x0:=T0]> acc0) ∅ Σ')
          with (atom_env_to_lty_env Σ') in Hj.
        rewrite atom_env_to_lty_env_lookup_bound_none in Hj. discriminate.
      * rewrite insert_insert_ne by congruence. reflexivity.
    + change (map_fold
        (fun (x0 : atom) (T0 : ty) (acc : lty_env) =>
          <[LVFree x0:=T0]> acc) ∅ Σ')
        with (atom_env_to_lty_env Σ').
      apply not_elem_of_dom.
      rewrite atom_env_to_lty_env_dom.
      unfold lvars_of_atoms.
      intros Hin.
      rewrite elem_of_map in Hin.
      destruct Hin as [y [Hy HyΣ]].
      inversion Hy. subst.
      apply elem_of_dom in HyΣ as [Ty HTy].
      rewrite Hfresh in HTy. discriminate.
Qed.

Lemma lty_env_open_insert_bound_atom_env k x T η Σ :
  x ∉ dom Σ →
  lty_env_open (<[k := x]> η) (<[LVBound k := T]> (atom_env_to_lty_env Σ)) =
  <[x := T]> Σ.
Proof.
  intros Hx.
  unfold lty_env_open.
  set (ηx := <[k:=x]> η).
  set (f := fun (v : logic_var) (U : ty) (acc : gmap atom ty) =>
    match lvar_to_atom ηx v with
    | Some y => <[y:=U]> acc
    | None => acc
    end).
  change (map_fold f ∅ (<[LVBound k:=T]> (atom_env_to_lty_env Σ)) =
    <[x:=T]> Σ).
  rewrite (map_fold_insert_L f ∅ (LVBound k) T (atom_env_to_lty_env Σ)).
  - subst f ηx. cbn [lvar_to_atom].
    rewrite lookup_insert.
    change (map_fold
      (fun v U acc =>
        match lvar_to_atom (<[k:=x]> η) v with
        | Some y => <[y:=U]> acc
        | None => acc
        end)
      ∅ (atom_env_to_lty_env Σ))
      with (lty_env_open (<[k:=x]> η) (atom_env_to_lty_env Σ)).
    rewrite lty_env_open_atom_env.
    destruct (decide (k = k)); [reflexivity | congruence].
  - subst f ηx.
    intros j1 j2 z1 z2 acc Hne Hj1 Hj2.
    cbn [lvar_to_atom].
    destruct j1 as [j1|y1], j2 as [j2|y2]; cbn [lvar_to_atom] in *.
    + destruct (decide (j1 = k)) as [->|Hj1k];
        destruct (decide (j2 = k)) as [->|Hj2k].
      * congruence.
      * rewrite lookup_insert in Hj1.
        rewrite lookup_insert_ne in Hj2 by congruence.
        rewrite atom_env_to_lty_env_lookup_bound_none in Hj2.
        discriminate.
      * rewrite lookup_insert_ne in Hj1 by congruence.
        rewrite lookup_insert in Hj2.
        rewrite atom_env_to_lty_env_lookup_bound_none in Hj1.
        discriminate.
      * rewrite lookup_insert_ne in Hj1 by congruence.
        rewrite lookup_insert_ne in Hj2 by congruence.
        rewrite atom_env_to_lty_env_lookup_bound_none in Hj1.
        discriminate.
    + destruct (decide (j1 = k)) as [->|Hj1k].
      * rewrite lookup_insert in Hj1.
        assert (Hy2 : y2 ∈ dom Σ).
        {
          rewrite lookup_insert_ne in Hj2 by congruence.
          apply elem_of_dom_2 in Hj2.
          rewrite atom_env_to_lty_env_dom in Hj2.
          unfold lvars_of_atoms in Hj2.
          rewrite elem_of_map in Hj2.
          destruct Hj2 as [y [Hy Hydom]].
          inversion Hy. subst. exact Hydom.
        }
        rewrite lookup_insert.
        destruct (decide (k = k)) as [_|Hkk]; [| congruence].
        rewrite insert_insert_ne by set_solver. reflexivity.
      * rewrite lookup_insert_ne in Hj1 by congruence.
        rewrite atom_env_to_lty_env_lookup_bound_none in Hj1.
        discriminate.
    + destruct (decide (j2 = k)) as [->|Hj2k].
      * rewrite lookup_insert in Hj2.
        assert (Hy1 : y1 ∈ dom Σ).
        {
          rewrite lookup_insert_ne in Hj1 by congruence.
          apply elem_of_dom_2 in Hj1.
          rewrite atom_env_to_lty_env_dom in Hj1.
          unfold lvars_of_atoms in Hj1.
          rewrite elem_of_map in Hj1.
          destruct Hj1 as [y [Hy Hydom]].
          inversion Hy. subst. exact Hydom.
        }
        rewrite lookup_insert.
        destruct (decide (k = k)) as [_|Hkk]; [| congruence].
        rewrite <- insert_insert_ne by set_solver. reflexivity.
      * rewrite lookup_insert_ne in Hj2 by congruence.
        rewrite atom_env_to_lty_env_lookup_bound_none in Hj2.
        discriminate.
    + rewrite <- insert_insert_ne by congruence. reflexivity.
  - apply atom_env_to_lty_env_lookup_bound_none.
Qed.

Lemma open_cty_env_singleton k x τ :
  open_cty_env (<[k := x]> ∅) τ = cty_open k x τ.
Proof.
  unfold open_cty_env.
  change (<[k := x]> ∅ : gmap nat atom) with ({[k := x]} : gmap nat atom).
  rewrite map_fold_singleton. reflexivity.
Qed.

(** ** Type denotation

    [denot_ty_lvar Σe Στ τ e] is the recursive semantic content of
    "expression [e] has type [τ]" under erased basic environments [Σe] and
    [Στ], including the obligations every denotation needs: basic typing,
    closed resources, and deterministic result reachability.

    The recursion is structural on [τ].  [denot_ty_body_lvar] is the one-step
    view used by proofs to peel the outer obligation layer.
    Expression-result atoms and fresh representatives are driven by the
    environment domains.  The regularity assumptions that [fv_tm e] and
    [fv_cty τ] are contained in the environment are supplied by the basic
    typing conjunct. *)

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

Lemma FResultBasicWorld_fv Σ b D :
  formula_fv (FResultBasicWorld Σ b D) =
  lvars_fv (lty_env_bvar_scope Σ ∪ D ∪ {[LVBound 0]}).
Proof.
  unfold FResultBasicWorld.
  apply formula_fv_FStoreResourceAtom_lvars.
Qed.

Lemma FResultBasicWorld_fv_atom_env_subset Σ b D :
  lvars_fv D ⊆ dom Σ →
  formula_fv (FResultBasicWorld (atom_env_to_lty_env Σ) b D) ⊆ dom Σ.
Proof.
  intros HD.
  rewrite FResultBasicWorld_fv.
  unfold lty_env_bvar_scope.
  rewrite atom_env_to_lty_env_dom.
  rewrite lvars_bv_of_atoms.
  rewrite lvars_fv_union, lvars_fv_union.
  rewrite lvars_fv_of_bvars, lvars_fv_singleton_bound.
  set_solver.
Qed.

Lemma FResultBasicWorld_fv_atom_env Σ b D :
  formula_fv (FResultBasicWorld (atom_env_to_lty_env Σ) b D) = lvars_fv D.
Proof.
  rewrite FResultBasicWorld_fv.
  unfold lty_env_bvar_scope.
  rewrite atom_env_to_lty_env_dom.
  rewrite lvars_bv_of_atoms.
  rewrite lvars_fv_union, lvars_fv_union.
  rewrite lvars_fv_of_bvars, lvars_fv_singleton_bound.
  set_solver.
Qed.

Lemma FResultBasicWorld_open_fv_atom_env Σ D ν :
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

Lemma FResultBasicWorld_open_fv_atom_env_into Σ D ν :
  lvars_fv
    (lvars_open 0 ν
      (into_lvars
        (lty_env_bvar_scope (atom_env_to_lty_env Σ) ∪ D ∪ {[LVBound 0]}))) =
  lvars_fv D ∪ {[ν]}.
Proof.
  cbn [into_lvars into_lvars_lvset].
  apply FResultBasicWorld_open_fv_atom_env.
Qed.

Lemma FResultBasicWorld_insert_fresh_open_equiv
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
  rewrite !FResultBasicWorld_open_fv_atom_env_into.
  rewrite !lty_env_open_atom_env.
  rewrite lookup_insert_eq.
  split; intros [Hscope [m0 [Hscope0 [Htyped Hle]]]]; split.
  - unfold formula_scoped_in_world in *.
    cbn [formula_fv lqual_dom stale stale_logic_qualifier] in *.
    rewrite !FResultBasicWorld_open_fv_atom_env_into in *.
    exact Hscope.
  - exists m0. split.
    + unfold formula_scoped_in_world in *.
      cbn [formula_fv lqual_dom stale stale_logic_qualifier] in *.
      rewrite !FResultBasicWorld_open_fv_atom_env_into in *.
      exact Hscope0.
    + split; [| exact Hle].
      pose proof (world_has_type_on_insert_under_result_irrel
        Σ (lvars_fv D) (res_restrict m0 (lvars_fv D ∪ {[ν]}))
        x T ν b ltac:(set_solver)) as Hiff.
      exact (proj1 Hiff Htyped).
  - unfold formula_scoped_in_world in *.
    cbn [formula_fv lqual_dom stale stale_logic_qualifier] in *.
    rewrite !FResultBasicWorld_open_fv_atom_env_into in *.
    exact Hscope.
  - exists m0. split.
    + unfold formula_scoped_in_world in *.
      cbn [formula_fv lqual_dom stale stale_logic_qualifier] in *.
      rewrite !FResultBasicWorld_open_fv_atom_env_into in *.
      exact Hscope0.
    + split; [| exact Hle].
      pose proof (world_has_type_on_insert_under_result_irrel
        Σ (lvars_fv D) (res_restrict m0 (lvars_fv D ∪ {[ν]}))
        x T ν b ltac:(set_solver)) as Hiff.
      exact (proj2 Hiff Htyped).
Qed.

Lemma FResultBasicWorld_insert_fresh_open_fv
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
  rewrite !FResultBasicWorld_open_fv_atom_env_into.
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
      rewrite store_restrict_twice_same.
      reflexivity. }
    rewrite Heq. apply Hclosed. exact Hσm.
  - intros σ Hσ.
    destruct (res_restrict_lift_store m X σ Hσ) as [σm [Hσm Hrestrict]].
    assert (Heq : store_restrict ((∅ : Store) ∪ σ) X = store_restrict σm X).
    { rewrite map_empty_union.
      rewrite <- Hrestrict.
      rewrite store_restrict_twice_same.
      reflexivity. }
    rewrite Heq. apply Htotal. exact Hσm.
Unshelve.
  all: try typeclasses eauto; try set_solver.
Qed.

Lemma FBasicTypingIn_atom_env_insert_fresh_models Σ x T τ e m :
  x ∉ dom Σ →
  x ∉ fv_cty τ ∪ fv_tm e →
  res_models m (FBasicTypingIn (atom_env_to_lty_env (<[x := T]> Σ))
    (atom_env_to_lty_env (<[x := T]> Σ)) τ e) →
  res_models m (FBasicTypingIn (atom_env_to_lty_env Σ)
    (atom_env_to_lty_env Σ) τ e).
Proof.
  intros HxΣ Hx Hmodel.
  unfold FBasicTypingIn, res_models in *.
  eapply res_models_with_store_store_resource_atom_vars_intro.
  - unfold formula_scoped_in_world.
    rewrite formula_fv_FStoreResourceAtom_lvars.
    rewrite !atom_env_to_lty_env_dom.
    rewrite !lvars_fv_union, !lvars_fv_of_atoms.
    pose proof (res_models_with_store_fuel_scoped _ _ _ _ Hmodel) as Hscope.
    unfold formula_scoped_in_world in Hscope.
    rewrite formula_fv_FStoreResourceAtom_lvars in Hscope.
    rewrite !atom_env_to_lty_env_dom in Hscope.
    rewrite !lvars_fv_union, !lvars_fv_of_atoms in Hscope.
    set_solver.
  - eapply res_models_with_store_store_resource_atom_vars_elim in Hmodel
      as [m0 [Hscope [Hbasic Hle]]].
    rewrite !lty_env_open_atom_env in Hbasic.
    cbn [open_cty_env open_tm_env] in Hbasic.
    destruct Hbasic as [Hbasic Htyped].
    rewrite lty_env_open_atom_env. cbn [open_cty_env open_tm_env].
    rewrite open_cty_env_empty in Hbasic.
    rewrite open_tm_env_empty in Htyped.
    rewrite open_cty_env_empty in Htyped.
    rewrite open_cty_env_empty, open_tm_env_empty.
    split.
    + eapply basic_choice_ty_drop_insert_fresh.
      * exact HxΣ.
      * set_solver.
      * exact Hbasic.
    + eapply basic_typing_drop_insert_fresh_tm.
      * intros Hxe. apply Hx. set_solver.
      * exact Htyped.
Qed.

Lemma FClosedResourceIn_atom_env_insert_restrict_models Σ x T m :
  x ∉ dom Σ →
  res_models m (FClosedResourceIn (atom_env_to_lty_env (<[x := T]> Σ))) →
  res_models (res_restrict m (dom Σ))
    (FClosedResourceIn (atom_env_to_lty_env Σ)).
Proof.
  intros HxΣ Hmodel.
  unfold FClosedResourceIn, res_models in *.
  pose proof (res_models_with_store_fuel_scoped _ _ _ _ Hmodel) as Hscope.
  eapply res_models_with_store_resource_atom_vars_elim in Hmodel
    as [m0 [Hscope0 [Hclosed Hle]]].
  eapply res_models_with_store_resource_atom_vars_witness_intro
    with (m0 := res_restrict m0 (dom Σ)).
  - unfold formula_scoped_in_world in *.
    rewrite !formula_fv_FResourceAtom_lvars in *.
    rewrite !atom_env_to_lty_env_dom, !lvars_fv_of_atoms in *.
    rewrite dom_insert_L in Hscope.
    rewrite !dom_empty_L in *.
    cbn [world_dom raw_restrict].
    set_solver.
  - unfold formula_scoped_in_world in *.
    rewrite !formula_fv_FResourceAtom_lvars in *.
    rewrite !atom_env_to_lty_env_dom, !lvars_fv_of_atoms in *.
    rewrite dom_insert_L in Hscope0.
    rewrite !dom_empty_L in *.
    cbn [world_dom raw_restrict].
    set_solver.
  - rewrite atom_env_to_lty_env_atom_dom.
    rewrite res_restrict_restrict_eq.
    rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms.
    replace (dom Σ ∩ dom Σ) with (dom Σ) by set_solver.
    rewrite atom_env_to_lty_env_atom_dom in Hclosed.
    rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms in Hclosed.
    rewrite dom_insert_L in Hclosed.
    assert (Hclosed_big :
        world_closed_on ({[x]} ∪ dom Σ) (res_restrict m0 (dom Σ))).
    { eapply (world_closed_on_le ({[x]} ∪ dom Σ)
        (res_restrict m0 (dom Σ))
        (res_restrict m0 ({[x]} ∪ dom Σ))).
      - apply res_restrict_mono. set_solver.
      - exact Hclosed.
    }
    intros σ Hσ.
    specialize (Hclosed_big σ Hσ).
    assert (Hdomσ : dom σ ⊆ dom Σ).
    { pose proof (wfworld_store_dom (res_restrict m0 (dom Σ)) σ Hσ).
      set_solver. }
    rewrite store_restrict_idemp in Hclosed_big by set_solver.
    rewrite store_restrict_idemp by exact Hdomσ.
    exact Hclosed_big.
  - eapply res_restrict_le_mono. exact Hle.
Qed.

Fixpoint denot_ty_body_lvar_gas
    (gas : nat) (Σe Στ : lty_env) (τ : choice_ty) (e : tm)
    {struct gas} : FQ :=
  match gas with
  | 0 => FTrue
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
          (denot_ty_body_lvar_gas gas' Σe Στ τ1 e))
        (denot_ty_obligations Σe Στ τ2 e
          (denot_ty_body_lvar_gas gas' Σe Στ τ2 e))
  | CTUnion τ1 τ2 =>
      FOr
        (denot_ty_obligations Σe Στ τ1 e
          (denot_ty_body_lvar_gas gas' Σe Στ τ1 e))
        (denot_ty_obligations Σe Στ τ2 e
          (denot_ty_body_lvar_gas gas' Σe Στ τ2 e))
  | CTSum τ1 τ2 =>
      FPlus
        (denot_ty_obligations Σe Στ τ1 e
          (denot_ty_body_lvar_gas gas' Σe Στ τ1 e))
        (denot_ty_obligations Σe Στ τ2 e
          (denot_ty_body_lvar_gas gas' Σe Στ τ2 e))
  | CTArrow τx τ =>
      FForall (
        let Σex := <[LVBound 0 := erase_ty τx]> Σe in
        let Στx := <[LVBound 0 := erase_ty τx]> Στ in
          FImpl
            (denot_ty_obligations Σex Στ τx (tret (vbvar 0))
              (denot_ty_body_lvar_gas gas' Σex Στ τx (tret (vbvar 0))))
            (denot_ty_obligations Σex Στx τ (tapp_tm e (vbvar 0))
              (denot_ty_body_lvar_gas gas' Σex Στx τ
                (tapp_tm e (vbvar 0)))))
  | CTWand τx τ =>
      FForall (
        let Σex := <[LVBound 0 := erase_ty τx]> Σe in
        let Στx := <[LVBound 0 := erase_ty τx]> Στ in
          FWand
            (denot_ty_obligations Σex Στ τx (tret (vbvar 0))
              (denot_ty_body_lvar_gas gas' Σex Στ τx (tret (vbvar 0))))
            (denot_ty_obligations Σex Στx τ (tapp_tm e (vbvar 0))
              (denot_ty_body_lvar_gas gas' Σex Στx τ
                (tapp_tm e (vbvar 0)))))
  end
  end.

Definition denot_ty_body_lvar
    (Σe Στ : lty_env) (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_body_lvar_gas (cty_depth τ) Σe Στ τ e.

Definition denot_ty_lvar_gas
    (gas : nat) (Σe Στ : lty_env) (τ : choice_ty) (e : tm)
    : FQ :=
  denot_ty_obligations Σe Στ τ e
    (denot_ty_body_lvar_gas gas Σe Στ τ e).

Definition denot_ty_lvar
    (Σe Στ : lty_env) (τ : choice_ty) (e : tm)
    : FQ :=
  denot_ty_lvar_gas (cty_depth τ) Σe Στ τ e.

Lemma denot_ty_body_lvar_gas_saturate τ :
  ∀ gas Σe Στ e,
    cty_depth τ <= gas →
    denot_ty_body_lvar_gas gas Σe Στ τ e =
    denot_ty_body_lvar_gas (cty_depth τ) Σe Στ τ e.
Proof.
  induction τ as [b φ|b φ|τ1 IH1 τ2 IH2|τ1 IH1 τ2 IH2
    |τ1 IH1 τ2 IH2|τx IHx τ IH|τx IHx τ IH];
    intros [|gas] Σe Στ e Hgas; cbn [cty_depth] in Hgas; try lia;
    cbn [denot_ty_body_lvar_gas cty_depth].
  - reflexivity.
  - reflexivity.
  - rewrite !(IH1 gas) by lia.
    rewrite !(IH1 (Nat.max (cty_depth τ1) (cty_depth τ2))) by lia.
    rewrite !(IH2 gas) by lia.
    rewrite !(IH2 (Nat.max (cty_depth τ1) (cty_depth τ2))) by lia.
    reflexivity.
  - rewrite !(IH1 gas) by lia.
    rewrite !(IH1 (Nat.max (cty_depth τ1) (cty_depth τ2))) by lia.
    rewrite !(IH2 gas) by lia.
    rewrite !(IH2 (Nat.max (cty_depth τ1) (cty_depth τ2))) by lia.
    reflexivity.
  - rewrite !(IH1 gas) by lia.
    rewrite !(IH1 (Nat.max (cty_depth τ1) (cty_depth τ2))) by lia.
    rewrite !(IH2 gas) by lia.
    rewrite !(IH2 (Nat.max (cty_depth τ1) (cty_depth τ2))) by lia.
    reflexivity.
  - rewrite !(IHx gas) by lia.
    rewrite !(IHx (Nat.max (cty_depth τx) (cty_depth τ))) by lia.
    rewrite !(IH gas) by lia.
    rewrite !(IH (Nat.max (cty_depth τx) (cty_depth τ))) by lia.
    reflexivity.
  - rewrite !(IHx gas) by lia.
    rewrite !(IHx (Nat.max (cty_depth τx) (cty_depth τ))) by lia.
    rewrite !(IH gas) by lia.
    rewrite !(IH (Nat.max (cty_depth τx) (cty_depth τ))) by lia.
    reflexivity.
Qed.

Lemma denot_ty_lvar_gas_saturate gas Σe Στ τ e :
  cty_depth τ <= gas →
  denot_ty_lvar_gas gas Σe Στ τ e = denot_ty_lvar Σe Στ τ e.
Proof.
  intros Hgas.
  unfold denot_ty_lvar, denot_ty_lvar_gas.
  rewrite denot_ty_body_lvar_gas_saturate by exact Hgas.
  reflexivity.
Qed.

Lemma denot_ty_obligations_body_gas_saturate gas Σe Στ τ e :
  cty_depth τ <= gas →
  denot_ty_obligations Σe Στ τ e
    (denot_ty_body_lvar_gas gas Σe Στ τ e) =
  denot_ty_lvar Σe Στ τ e.
Proof.
  intros Hgas.
  unfold denot_ty_lvar, denot_ty_lvar_gas.
  rewrite denot_ty_body_lvar_gas_saturate by exact Hgas.
  reflexivity.
Qed.

Lemma denot_ty_body_lvar_inter Σe Στ τ1 τ2 e :
  denot_ty_body_lvar Σe Στ (CTInter τ1 τ2) e =
  FAnd (denot_ty_lvar Σe Στ τ1 e) (denot_ty_lvar Σe Στ τ2 e).
Proof.
  unfold denot_ty_body_lvar.
  cbn [cty_depth denot_ty_body_lvar_gas].
  rewrite !denot_ty_obligations_body_gas_saturate by lia.
  reflexivity.
Qed.

Lemma denot_ty_body_lvar_union Σe Στ τ1 τ2 e :
  denot_ty_body_lvar Σe Στ (CTUnion τ1 τ2) e =
  FOr (denot_ty_lvar Σe Στ τ1 e) (denot_ty_lvar Σe Στ τ2 e).
Proof.
  unfold denot_ty_body_lvar.
  cbn [cty_depth denot_ty_body_lvar_gas].
  rewrite !denot_ty_obligations_body_gas_saturate by lia.
  reflexivity.
Qed.

Lemma denot_ty_body_lvar_sum Σe Στ τ1 τ2 e :
  denot_ty_body_lvar Σe Στ (CTSum τ1 τ2) e =
  FPlus (denot_ty_lvar Σe Στ τ1 e) (denot_ty_lvar Σe Στ τ2 e).
Proof.
  unfold denot_ty_body_lvar.
  cbn [cty_depth denot_ty_body_lvar_gas].
  rewrite !denot_ty_obligations_body_gas_saturate by lia.
  reflexivity.
Qed.

Lemma denot_ty_body_lvar_arrow Σe Στ τx τ e :
  denot_ty_body_lvar Σe Στ (CTArrow τx τ) e =
  FForall (
    let Σex := <[LVBound 0 := erase_ty τx]> Σe in
    let Στx := <[LVBound 0 := erase_ty τx]> Στ in
    FImpl
      (denot_ty_lvar Σex Στ τx (tret (vbvar 0)))
      (denot_ty_lvar Σex Στx τ (tapp_tm e (vbvar 0)))).
Proof.
  unfold denot_ty_body_lvar.
  cbn [cty_depth denot_ty_body_lvar_gas].
  rewrite !denot_ty_obligations_body_gas_saturate by lia.
  reflexivity.
Qed.

Lemma denot_ty_body_lvar_wand Σe Στ τx τ e :
  denot_ty_body_lvar Σe Στ (CTWand τx τ) e =
  FForall (
    let Σex := <[LVBound 0 := erase_ty τx]> Σe in
    let Στx := <[LVBound 0 := erase_ty τx]> Στ in
    FWand
      (denot_ty_lvar Σex Στ τx (tret (vbvar 0)))
      (denot_ty_lvar Σex Στx τ (tapp_tm e (vbvar 0)))).
Proof.
  unfold denot_ty_body_lvar.
  cbn [cty_depth denot_ty_body_lvar_gas].
  rewrite !denot_ty_obligations_body_gas_saturate by lia.
  reflexivity.
Qed.

Definition denot_ty_body
    (Σ : gmap atom ty) (τ : choice_ty) (e : tm) : FQ :=
  let Σl := atom_env_to_lty_env Σ in
  denot_ty_body_lvar Σl Σl τ e.

Definition denot_ty_on
    (Σ : gmap atom ty) (τ : choice_ty) (e : tm) : FQ :=
  let Σl := atom_env_to_lty_env Σ in
  denot_ty_lvar Σl Σl τ e.

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

Lemma denot_ty_intro Σ τ e m :
  basic_choice_ty (dom Σ) τ →
  Σ ⊢ₑ e ⋮ erase_ty τ →
  world_closed_on (dom Σ) m →
  expr_total_on (dom Σ) e m →
  m ⊨ denot_ty_body Σ τ e →
  dom Σ ⊆ world_dom (m : World) →
  m ⊨ denot_ty_on Σ τ e.
Proof.
  intros Hbasic Htyped Hclosed Htotal Hbody Hdom.
  unfold denot_ty_on, denot_ty_body.
  unfold denot_ty_obligations.
  apply res_models_and_intro_from_models.
  - unfold FBasicTypingIn, res_models.
    eapply res_models_with_store_store_resource_atom_vars_intro.
    + unfold formula_scoped_in_world.
      rewrite formula_fv_FStoreResourceAtom_lvars.
      rewrite !atom_env_to_lty_env_dom.
      rewrite lvars_fv_union, !lvars_fv_of_atoms.
      rewrite dom_empty_L. set_solver.
    + rewrite lty_env_open_atom_env. cbn [open_cty_env open_tm_env].
      split; assumption.
  - apply res_models_and_intro_from_models.
    + unfold FClosedResourceIn, res_models.
      eapply res_models_with_store_resource_atom_vars_intro.
      * unfold formula_scoped_in_world.
        rewrite formula_fv_FResourceAtom_lvars.
        rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms.
        rewrite dom_empty_L. set_solver.
      * rewrite atom_env_to_lty_env_atom_dom.
        eapply world_closed_on_le.
        -- apply res_restrict_le.
        -- exact Hclosed.
    + apply res_models_and_intro_from_models.
      * unfold FStrongTotalIn, res_models.
        eapply res_models_with_store_store_resource_atom_vars_intro.
        -- unfold formula_scoped_in_world.
           rewrite formula_fv_FStoreResourceAtom_lvars.
           rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms.
           rewrite dom_empty_L. set_solver.
        -- rewrite atom_env_to_lty_env_atom_dom.
           rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms.
           rewrite store_restrict_empty. cbn [open_tm_env].
           eapply expr_total_with_store_empty_restrict; eauto.
      * exact Hbody.
Qed.

Lemma denot_ty_body_of_formula Σ τ e m :
  m ⊨ denot_ty_on Σ τ e →
  m ⊨ denot_ty_body Σ τ e.
Proof.
  intros Hm.
  unfold denot_ty_on, denot_ty_body in Hm.
  unfold denot_ty_obligations in Hm.
  apply res_models_with_store_and_elim_r in Hm.
  apply res_models_with_store_and_elim_r in Hm.
  apply res_models_with_store_and_elim_r in Hm.
  exact Hm.
Qed.

Lemma denot_ty_basic_of_formula Σ τ e m :
  m ⊨ denot_ty_on Σ τ e →
  basic_choice_ty (dom Σ) τ ∧ Σ ⊢ₑ e ⋮ erase_ty τ.
Proof.
  intros Hm.
  unfold denot_ty_on in Hm.
  unfold denot_ty_obligations, FBasicTypingIn in Hm.
  apply res_models_with_store_and_elim_l in Hm.
  destruct (res_models_with_store_store_resource_atom_vars_elim _ _ _ _ Hm)
    as [_ [_ [Hbasic _]]].
  rewrite lty_env_open_atom_env in Hbasic.
  cbn [open_cty_env open_tm_env] in Hbasic.
  exact Hbasic.
Qed.

Lemma world_closed_on_extend X (m n : WfWorld) :
  X ⊆ world_dom (m : World) →
  m ⊑ n →
  world_closed_on X m →
  world_closed_on X n.
Proof.
  intros HXm Hle Hclosed σ Hσ.
  pose proof (res_restrict_eq_of_le m n Hle) as Hrestrict.
  assert ((res_restrict n (world_dom (m : World)) : World)
    (store_restrict σ (world_dom (m : World)))) as Hσm.
  { exists σ. split; [exact Hσ | reflexivity]. }
  rewrite Hrestrict in Hσm.
  replace (store_restrict σ X) with
    (store_restrict (store_restrict σ (world_dom (m : World))) X).
  - exact (Hclosed _ Hσm).
  - store_norm. reflexivity.
Qed.

Lemma denot_ty_world_closed_on_of_formula Σ τ e m :
  m ⊨ denot_ty_on Σ τ e →
  world_closed_on (dom Σ) m.
Proof.
  intros Hm.
  unfold denot_ty_on in Hm.
  unfold denot_ty_obligations, FClosedResourceIn in Hm.
  apply res_models_with_store_and_elim_r in Hm.
  apply res_models_with_store_and_elim_l in Hm.
  destruct (res_models_with_store_resource_atom_vars_elim ∅ m
    (dom (atom_env_to_lty_env Σ))
    (world_closed_on (lty_env_atom_dom (atom_env_to_lty_env Σ))) Hm)
    as [m0 [Hscope [Hclosed Hle]]].
  rewrite atom_env_to_lty_env_atom_dom in Hclosed.
  rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms in Hclosed.
  eapply (world_closed_on_extend (dom Σ)
    (res_restrict m0 (dom Σ)) m).
  - simpl. intros z Hz. apply elem_of_intersection. split; [| exact Hz].
    unfold formula_scoped_in_world in Hscope.
    rewrite dom_empty_L in Hscope.
    apply Hscope. apply elem_of_union. right.
    rewrite formula_fv_FResourceAtom_lvars.
    rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms. exact Hz.
  - etrans; [apply res_restrict_le | exact Hle].
  - exact Hclosed.
Qed.

Lemma denot_ty_expr_total_on_of_formula Σ τ e m :
  m ⊨ denot_ty_on Σ τ e →
  expr_total_on (dom Σ) e m.
Proof.
  intros Hm.
  pose proof (denot_ty_basic_of_formula _ _ _ _ Hm)
    as [_ Htyped].
  split.
  - eauto using basic_typing_contains_fv_tm.
  - unfold denot_ty_on in Hm.
    unfold denot_ty_obligations, FStrongTotalIn in Hm.
    apply res_models_with_store_and_elim_r in Hm.
    apply res_models_with_store_and_elim_r in Hm.
    apply res_models_with_store_and_elim_l in Hm.
    destruct (res_models_with_store_store_resource_atom_vars_elim ∅ m
      (dom (atom_env_to_lty_env Σ))
      (fun η ρ m =>
        expr_total_with_store (lty_env_atom_dom (atom_env_to_lty_env Σ))
          (open_tm_env η e) ρ m) Hm)
      as [m0 [Hscope [Htotal Hle]]].
    rewrite atom_env_to_lty_env_atom_dom in Htotal.
    rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms in Htotal.
    rewrite store_restrict_empty in Htotal.
    cbn [open_tm_env] in Htotal.
    destruct Htotal as [_ Htotal].
    intros σ Hσ.
    pose proof (res_restrict_eq_of_le m0 m Hle) as Hrestrict.
    assert (Hσm0 :
      (m0 : World) (store_restrict σ (world_dom (m0 : World)))).
    { assert ((res_restrict m (world_dom (m0 : World)) : World)
        (store_restrict σ (world_dom (m0 : World)))) as Hraw.
      { exists σ. split; [exact Hσ | reflexivity]. }
      rewrite Hrestrict in Hraw. exact Hraw. }
    assert (HdomΣ : dom Σ ⊆ world_dom (m0 : World)).
    { unfold formula_scoped_in_world in Hscope.
      rewrite dom_empty_L in Hscope.
      intros z Hz. apply Hscope. apply elem_of_union. right.
      rewrite formula_fv_FStoreResourceAtom_lvars.
      rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms. exact Hz. }
    assert (HσD :
      (res_restrict m0 (dom Σ) : World) (store_restrict σ (dom Σ))).
    { exists (store_restrict σ (world_dom (m0 : World))).
      split; [exact Hσm0 |].
      rewrite store_restrict_twice_subset by set_solver.
      reflexivity. }
    specialize (Htotal _ HσD) as [vx Hsteps].
    exists vx.
    rewrite map_empty_union in Hsteps.
    rewrite store_restrict_twice_same in Hsteps.
    exact Hsteps.
Qed.

Definition denot_ty_total_in_ctx_under
    (Σ : gmap atom ty) (Γ : ctx) (τ : choice_ty) (e : tm)
    (m : WfWorld) : Prop :=
  m ⊨ denot_ty_in_ctx_under Σ Γ τ e ∧
  expr_total_on (dom (erase_ctx_under Σ Γ)) e m.

Definition entails_total (φ : FQ) (P : WfWorld → Prop) : Prop :=
  ∀ m, m ⊨ φ → P m.

Definition ty_env_agree_on (X : aset) (Σ1 Σ2 : gmap atom ty) : Prop :=
  ∀ x, x ∈ X → Σ1 !! x = Σ2 !! x.

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

Lemma denot_ty_on_env_agree Σ1 Σ2 τ e :
  dom Σ1 = dom Σ2 →
  ty_env_agree_on (fv_cty τ ∪ fv_tm e) Σ1 Σ2 →
  denot_ty_on Σ1 τ e = denot_ty_on Σ2 τ e.
Proof.
Admitted.

Lemma FExprContIn_fv_lty_env
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

Lemma denot_ty_obligations_fv_subset (Σe Στ : lty_env) τ e φ S :
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

Lemma denot_ty_obligations_body_gas_fv_subset gas Σe Στ τ e :
  formula_fv (denot_ty_body_lvar_gas gas Σe Στ τ e) ⊆
    lty_env_atom_dom Σe ∪ lty_env_atom_dom Στ ∪ fv_cty τ →
  formula_fv (denot_ty_obligations Σe Στ τ e
    (denot_ty_body_lvar_gas gas Σe Στ τ e)) ⊆
    lty_env_atom_dom Σe ∪ lty_env_atom_dom Στ ∪ fv_cty τ.
Proof.
  intros Hbody.
  apply denot_ty_obligations_fv_subset.
  set_solver.
Qed.

Lemma denot_ty_gas_fv_subset gas :
  (∀ Σe Στ τ e,
    formula_fv (denot_ty_body_lvar_gas gas Σe Στ τ e) ⊆
      lty_env_atom_dom Σe ∪ lty_env_atom_dom Στ ∪ fv_cty τ) ∧
  (∀ Σe Στ τ e,
    formula_fv (denot_ty_lvar_gas gas Σe Στ τ e) ⊆
      lty_env_atom_dom Σe ∪ lty_env_atom_dom Στ ∪ fv_cty τ).
Proof.
  induction gas as [|gas [IHbody IHlvar]].
  - split; intros Σe Στ τ e.
    + cbn [denot_ty_body_lvar_gas formula_fv]. set_solver.
    + unfold denot_ty_lvar_gas.
      apply denot_ty_obligations_fv_subset.
      cbn [denot_ty_body_lvar_gas formula_fv]. set_solver.
  - assert (HbodyS : ∀ Σe Στ τ e,
      formula_fv (denot_ty_body_lvar_gas (S gas) Σe Στ τ e) ⊆
        lty_env_atom_dom Σe ∪ lty_env_atom_dom Στ ∪ fv_cty τ).
    {
      intros Σe Στ τ e.
      destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τ|τx τ];
        cbn [denot_ty_body_lvar_gas fv_cty].
      - destruct φ as [D p]. cbn [qual_vars qual_dom].
        pose proof (FExprContIn_fv_lty_env Σe e
          (FAnd (FResultBasicWorld Στ b (qual_vars (qual D p)))
            (FFibVars (qual_vars (qual D p))
              (FOver (FTypeQualifier (qual D p)))))) as Hcont.
        cbn [qual_vars qual_dom formula_fv] in Hcont.
        rewrite FResultBasicWorld_fv in Hcont.
        unfold lty_env_bvar_scope in Hcont.
        rewrite !lvars_fv_union, lvars_fv_of_bvars,
          lvars_fv_singleton_bound in Hcont.
        rewrite formula_fv_FTypeQualifier in Hcont.
        cbn [qual_dom] in Hcont.
        set_solver.
      - destruct φ as [D p]. cbn [qual_vars qual_dom].
        pose proof (FExprContIn_fv_lty_env Σe e
          (FAnd (FResultBasicWorld Στ b (qual_vars (qual D p)))
            (FFibVars (qual_vars (qual D p))
              (FUnder (FTypeQualifier (qual D p)))))) as Hcont.
        cbn [qual_vars qual_dom formula_fv] in Hcont.
        rewrite FResultBasicWorld_fv in Hcont.
        unfold lty_env_bvar_scope in Hcont.
        rewrite !lvars_fv_union, lvars_fv_of_bvars,
          lvars_fv_singleton_bound in Hcont.
        rewrite formula_fv_FTypeQualifier in Hcont.
        cbn [qual_dom] in Hcont.
        set_solver.
      - assert (H1 : formula_fv (denot_ty_obligations Σe Στ τ1 e
            (denot_ty_body_lvar_gas gas Σe Στ τ1 e)) ⊆
          lty_env_atom_dom Σe ∪ lty_env_atom_dom Στ ∪ fv_cty τ1)
          by (apply denot_ty_obligations_body_gas_fv_subset; apply IHbody).
        assert (H2 : formula_fv (denot_ty_obligations Σe Στ τ2 e
            (denot_ty_body_lvar_gas gas Σe Στ τ2 e)) ⊆
          lty_env_atom_dom Σe ∪ lty_env_atom_dom Στ ∪ fv_cty τ2)
          by (apply denot_ty_obligations_body_gas_fv_subset; apply IHbody).
        set_solver.
      - assert (H1 : formula_fv (denot_ty_obligations Σe Στ τ1 e
            (denot_ty_body_lvar_gas gas Σe Στ τ1 e)) ⊆
          lty_env_atom_dom Σe ∪ lty_env_atom_dom Στ ∪ fv_cty τ1)
          by (apply denot_ty_obligations_body_gas_fv_subset; apply IHbody).
        assert (H2 : formula_fv (denot_ty_obligations Σe Στ τ2 e
            (denot_ty_body_lvar_gas gas Σe Στ τ2 e)) ⊆
          lty_env_atom_dom Σe ∪ lty_env_atom_dom Στ ∪ fv_cty τ2)
          by (apply denot_ty_obligations_body_gas_fv_subset; apply IHbody).
        set_solver.
      - assert (H1 : formula_fv (denot_ty_obligations Σe Στ τ1 e
            (denot_ty_body_lvar_gas gas Σe Στ τ1 e)) ⊆
          lty_env_atom_dom Σe ∪ lty_env_atom_dom Στ ∪ fv_cty τ1)
          by (apply denot_ty_obligations_body_gas_fv_subset; apply IHbody).
        assert (H2 : formula_fv (denot_ty_obligations Σe Στ τ2 e
            (denot_ty_body_lvar_gas gas Σe Στ τ2 e)) ⊆
          lty_env_atom_dom Σe ∪ lty_env_atom_dom Στ ∪ fv_cty τ2)
          by (apply denot_ty_obligations_body_gas_fv_subset; apply IHbody).
        set_solver.
      - set (Σex := <[LVBound 0:=erase_ty τx]>Σe).
        set (Στx := <[LVBound 0:=erase_ty τx]>Στ).
        assert (Hx : formula_fv (denot_ty_obligations Σex Στ τx
              (tret (vbvar 0))
              (denot_ty_body_lvar_gas gas Σex Στ τx
                (tret (vbvar 0)))) ⊆
            lty_env_atom_dom Σex ∪ lty_env_atom_dom Στ ∪ fv_cty τx)
          by (apply denot_ty_obligations_body_gas_fv_subset; apply IHbody).
        assert (Hbody : formula_fv (denot_ty_obligations Σex Στx τ
              (tapp_tm e (vbvar 0))
              (denot_ty_body_lvar_gas gas Σex Στx τ
                (tapp_tm e (vbvar 0)))) ⊆
            lty_env_atom_dom Σex ∪ lty_env_atom_dom Στx ∪ fv_cty τ)
          by (apply denot_ty_obligations_body_gas_fv_subset; apply IHbody).
        subst Σex Στx.
        rewrite !lty_env_atom_dom_insert_bound in Hx.
        rewrite !lty_env_atom_dom_insert_bound in Hbody.
        set_solver.
      - set (Σex := <[LVBound 0:=erase_ty τx]>Σe).
        set (Στx := <[LVBound 0:=erase_ty τx]>Στ).
        assert (Hx : formula_fv (denot_ty_obligations Σex Στ τx
              (tret (vbvar 0))
              (denot_ty_body_lvar_gas gas Σex Στ τx
                (tret (vbvar 0)))) ⊆
            lty_env_atom_dom Σex ∪ lty_env_atom_dom Στ ∪ fv_cty τx)
          by (apply denot_ty_obligations_body_gas_fv_subset; apply IHbody).
        assert (Hbody : formula_fv (denot_ty_obligations Σex Στx τ
              (tapp_tm e (vbvar 0))
              (denot_ty_body_lvar_gas gas Σex Στx τ
                (tapp_tm e (vbvar 0)))) ⊆
            lty_env_atom_dom Σex ∪ lty_env_atom_dom Στx ∪ fv_cty τ)
          by (apply denot_ty_obligations_body_gas_fv_subset; apply IHbody).
        subst Σex Στx.
        rewrite !lty_env_atom_dom_insert_bound in Hx.
        rewrite !lty_env_atom_dom_insert_bound in Hbody.
        set_solver.
    }
    split; [exact HbodyS |].
    intros Σe Στ τ e.
    unfold denot_ty_lvar_gas.
    apply denot_ty_obligations_body_gas_fv_subset.
    apply HbodyS.
Qed.

Lemma denot_ty_body_lvar_gas_fv_subset gas Σe Στ τ e :
  formula_fv (denot_ty_body_lvar_gas gas Σe Στ τ e) ⊆
    lty_env_atom_dom Σe ∪ lty_env_atom_dom Στ ∪ fv_cty τ.
Proof.
  exact (proj1 (denot_ty_gas_fv_subset gas) Σe Στ τ e).
Qed.

Lemma denot_ty_lvar_gas_fv_subset gas Σe Στ τ e :
  formula_fv (denot_ty_lvar_gas gas Σe Στ τ e) ⊆
    lty_env_atom_dom Σe ∪ lty_env_atom_dom Στ ∪ fv_cty τ.
Proof.
  exact (proj2 (denot_ty_gas_fv_subset gas) Σe Στ τ e).
Qed.

Lemma denot_ty_lvar_fv_subset Σe Στ τ e :
  formula_fv (denot_ty_lvar Σe Στ τ e) ⊆
    lty_env_atom_dom Σe ∪ lty_env_atom_dom Στ ∪ fv_cty τ.
Proof.
  unfold denot_ty_lvar.
  apply denot_ty_lvar_gas_fv_subset.
Qed.

Lemma denot_ty_body_lvar_fv_subset Σe Στ τ e :
  formula_fv (denot_ty_body_lvar Σe Στ τ e) ⊆
    lty_env_atom_dom Σe ∪ lty_env_atom_dom Στ ∪ fv_cty τ.
Proof.
  unfold denot_ty_body_lvar.
  apply denot_ty_body_lvar_gas_fv_subset.
Qed.

Lemma denot_ty_on_fv_subset Σ τ e :
  formula_fv (denot_ty_on Σ τ e) ⊆ dom Σ ∪ fv_cty τ.
Proof.
  unfold denot_ty_on.
  pose proof (denot_ty_lvar_fv_subset
    (atom_env_to_lty_env Σ) (atom_env_to_lty_env Σ) τ e) as Hfv.
  rewrite !atom_env_to_lty_env_atom_dom in Hfv.
  set_solver.
Qed.

Lemma denot_ty_body_fv_subset Σ τ e :
  formula_fv (denot_ty_body Σ τ e) ⊆ dom Σ ∪ fv_cty τ.
Proof.
  unfold denot_ty_body.
  pose proof (denot_ty_body_lvar_fv_subset
    (atom_env_to_lty_env Σ) (atom_env_to_lty_env Σ) τ e) as Hfv.
  rewrite !atom_env_to_lty_env_atom_dom in Hfv.
  set_solver.
Qed.

Lemma denot_ty_on_fv_subset_env
    (Σ : gmap atom ty) (τ : choice_ty) e :
  fv_cty τ ⊆ dom Σ →
  formula_fv (denot_ty_on Σ τ e) ⊆ dom Σ.
Proof.
  intros Hfv.
  pose proof (denot_ty_on_fv_subset Σ τ e) as Hφ.
  set_solver.
Qed.

Lemma denot_ty_body_fv_subset_env
    (Σ : gmap atom ty) (τ : choice_ty) e :
  fv_cty τ ⊆ dom Σ →
  formula_fv (denot_ty_body Σ τ e) ⊆ dom Σ.
Proof.
  intros Hfv.
  pose proof (denot_ty_body_fv_subset Σ τ e) as Hφ.
  set_solver.
Qed.

Lemma denot_ty_formula_fv_subset τ e :
  formula_fv (denot_ty τ e) ⊆ fv_cty τ.
Proof.
  unfold denot_ty, denot_ty_under.
  pose proof (denot_ty_on_fv_subset ∅ τ e) as Hfv.
  intros z Hz. apply Hfv in Hz. set_solver.
Qed.

Lemma denot_ty_under_fv_subset Σ τ e :
  formula_fv (denot_ty_under Σ τ e) ⊆ dom Σ ∪ fv_cty τ.
Proof.
  apply denot_ty_on_fv_subset.
Qed.

Lemma denot_ty_in_ctx_under_fv_subset Σ Γ τ e :
  formula_fv (denot_ty_in_ctx_under Σ Γ τ e) ⊆
    dom (erase_ctx_under Σ Γ) ∪ fv_cty τ.
Proof.
  unfold denot_ty_in_ctx_under.
  apply denot_ty_on_fv_subset.
Qed.

Lemma denot_ty_on_env_fv_subset Σ τ e :
  dom Σ ⊆ formula_fv (denot_ty_on Σ τ e).
Proof.
  unfold denot_ty_on, denot_ty_lvar, denot_ty_lvar_gas.
  unfold denot_ty_obligations, FBasicTypingIn, FClosedResourceIn,
    FStrongTotalIn, FStoreResourceAtom, FResourceAtom.
  cbn [formula_fv stale stale_logic_qualifier lqual_dom].
  denot_lvars_norm.
  rewrite !atom_env_to_lty_env_dom.
  rewrite !lvars_fv_union, !lvars_fv_of_atoms.
  set_solver.
Qed.

Lemma denot_ty_on_result_atom_fv Σ x τ :
  x ∈ dom Σ →
  x ∈ formula_fv (denot_ty_on Σ τ (tret (vfvar x))).
Proof.
  intros Hx.
  pose proof (denot_ty_on_env_fv_subset Σ τ (tret (vfvar x))) as Hfv.
  apply Hfv. exact Hx.
Qed.

Lemma denot_ty_under_result_atom_fv Σ x τ :
  x ∈ dom Σ →
  x ∈ formula_fv (denot_ty_under Σ τ (tret (vfvar x))).
Proof.
  unfold denot_ty_under.
  apply denot_ty_on_result_atom_fv.
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
  - apply res_restrict_mono. apply denot_ty_under_fv_subset.
  - apply res_models_restrict_fv. exact Hm.
Qed.

(** ** Context denotation

    [denot_ctx_under Σ Γ] is the formula that holds when [Γ] is satisfied
    under the ambient erased basic environment [Σ].  The public
    [denot_ctx Γ] instantiates [Σ] with [erase_ctx Γ], so later binders in a
    comma context can be checked against earlier erased bindings. *)
