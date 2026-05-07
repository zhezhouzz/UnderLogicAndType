(** * CoreLang multi-substitution properties

    This file migrates the reusable part of UnderType/HATs instantiation
    infrastructure.  The definitions are phrased through small typeclasses so
    later syntactic categories can reuse the same multi-substitution facts once
    they provide the corresponding single-substitution lemmas. *)

From ChoicePrelude Require Import Store.
From CoreLang Require Import Instantiation LocallyNamelessExtra LocallyNamelessInstances.
From LocallyNameless Require Import Classes Tactics.

Lemma closed_env_insert σ x v :
  σ !! x = None ->
  closed_env (<[x := v]> σ) ->
  stale v = ∅ /\ closed_env σ.
Proof.
  intros Hfresh Hclosed.
  unfold closed_env in *.
  apply map_Forall_insert in Hclosed; [exact Hclosed | exact Hfresh].
Qed.

Lemma closed_env_lookup σ x v :
  closed_env σ ->
  σ !! x = Some v ->
  stale v = ∅.
Proof.
  unfold closed_env. intros Hclosed Hlookup.
  exact (map_Forall_lookup_1 _ _ _ _ Hclosed Hlookup).
Qed.

Lemma closed_env_restrict σ X :
  closed_env σ ->
  closed_env (map_restrict value σ X).
Proof.
  unfold closed_env. intros Hclosed.
  apply map_Forall_lookup_2. intros x v Hlookup.
  apply map_restrict_lookup_some in Hlookup as [_ Hlookup].
  exact (map_Forall_lookup_1 _ _ _ _ Hclosed Hlookup).
Qed.

Definition lc_env (σ : env) : Prop :=
  map_Forall (fun _ v => is_lc v) σ.

Lemma lc_env_insert σ x v :
  σ !! x = None ->
  lc_env (<[x := v]> σ) ->
  is_lc v /\ lc_env σ.
Proof.
  intros Hfresh Hlc.
  unfold lc_env in *.
  apply map_Forall_insert in Hlc; [exact Hlc | exact Hfresh].
Qed.

Lemma lc_env_lookup σ x v :
  lc_env σ ->
  σ !! x = Some v ->
  is_lc v.
Proof.
  unfold lc_env. intros Hlc Hlookup.
  exact (map_Forall_lookup_1 _ _ _ _ Hlc Hlookup).
Qed.

Ltac gen_closed_env :=
  repeat
    match goal with
    | H : closed_env (<[?x := _]> ?σ), Hfresh : ?σ !! ?x = None |- _ =>
        let Hv := fresh "Hclosed_value" in
        let Hσ := fresh "Hclosed_env" in
        destruct (closed_env_insert σ x _ Hfresh H) as [Hv Hσ];
        clear H
    | H : closed_env ?σ, Hlookup : ?σ !! ?x = Some ?v |- _ =>
        let Hv := fresh "Hclosed_value" in
        pose proof (closed_env_lookup σ x v H Hlookup) as Hv
    end.

Ltac gen_lc_env :=
  repeat
    match goal with
    | H : lc_env (<[?x := _]> ?σ), Hfresh : ?σ !! ?x = None |- _ =>
        let Hv := fresh "Hlc_value" in
        let Hσ := fresh "Hlc_env" in
        destruct (lc_env_insert σ x _ Hfresh H) as [Hv Hσ];
        clear H
    | H : lc_env ?σ, Hlookup : ?σ !! ?x = Some ?v |- _ =>
        let Hv := fresh "Hlc_value" in
        pose proof (lc_env_lookup σ x v H Hlookup) as Hv
    end.

(** Single-substitutions commute when the two substituted values are closed.
    This is the exact hypothesis needed by [map_fold_insert_L]. *)
Class SubstCommuteClosed A `{Stale A} `{SubstV value A} :=
  subst_commute_closed :
    forall (x y : atom) (vx vy : value) (a : A),
      x <> y ->
      stale vx = ∅ ->
      stale vy = ∅ ->
      {x := vx} ({y := vy} a) = {y := vy} ({x := vx} a).

#[global] Instance SubstCommuteClosed_value : SubstCommuteClosed value.
Proof.
  intros x y vx vy v Hxy Hvx Hvy.
  apply subst_commute_value; auto; my_set_solver.
Qed.

#[global] Instance SubstCommuteClosed_tm : SubstCommuteClosed tm.
Proof.
  intros x y vx vy e Hxy Hvx Hvy.
  apply subst_commute_tm; auto; my_set_solver.
Qed.

Class MsubstInsert A `{SubstV value A} := msubst_insert :
  forall (σ : env) (x : atom) (vx : value) (a : A),
    closed_env σ ->
    stale vx = ∅ ->
    σ !! x = None ->
    m{<[x := vx]> σ} a = {x := vx} (m{σ} a).

Lemma MsubstInsert_all
    (A : Type)
    (staleA : Stale A)
    (substA : SubstV value A)
    (subst_commuteA : @SubstCommuteClosed A staleA substA) :
  @MsubstInsert A substA.
Proof.
  unfold MsubstInsert, msubst. intros σ x vx a Hclosed Hvx Hfresh.
  assert (Hclosed' : closed_env (<[x := vx]> σ)).
  { unfold closed_env in *. apply map_Forall_insert_2; [exact Hvx | exact Hclosed]. }
  apply map_fold_insert_L; [| exact Hfresh].
  intros y z vy vz acc Hyz Hy Hz.
  apply subst_commute_closed; auto.
  - exact (closed_env_lookup (<[x := vx]> σ) y vy Hclosed' Hy).
  - exact (closed_env_lookup (<[x := vx]> σ) z vz Hclosed' Hz).
Qed.

#[global] Instance MsubstInsert_value : MsubstInsert value.
Proof. eapply MsubstInsert_all; typeclasses eauto. Qed.

#[global] Instance MsubstInsert_tm : MsubstInsert tm.
Proof. eapply MsubstInsert_all; typeclasses eauto. Qed.

Ltac fold_msubst :=
  change (map_fold (fun x vx acc => {x := vx} acc) ?a ?σ) with (m{σ} a) in *.

Ltac rewrite_msubst_insert :=
  cbn; fold_msubst; rewrite !msubst_insert; eauto.

Class MsubstFresh A `{Stale A} `{SubstV value A} := msubst_fresh :
  forall (σ : env) (a : A),
    stale σ ∩ stale a = ∅ ->
    m{σ} a = a.

Lemma MsubstFresh_all
    (A : Type)
    (staleA : Stale A)
    (substA : SubstV value A)
    (subst_freshA : @SubstFresh A staleA substA) :
  @MsubstFresh A staleA substA.
Proof.
  unfold MsubstFresh. intros σ a.
  unfold msubst.
  refine (fin_maps.map_fold_ind
    (fun σ => dom σ ∩ stale a = ∅ ->
      map_fold (fun x vx acc => {x := vx} acc) a σ = a) _ _ σ).
  - intros _. reflexivity.
  - intros x vx σ' Hfresh Hfold IH Hdisj.
    rewrite Hfold. rewrite IH.
    + apply subst_freshA. rewrite dom_insert_L in Hdisj. set_solver.
    + rewrite dom_insert_L in Hdisj. set_solver.
Qed.

#[global] Instance MsubstFresh_value : MsubstFresh value.
Proof. eapply MsubstFresh_all; typeclasses eauto. Qed.

#[global] Instance MsubstFresh_tm : MsubstFresh tm.
Proof. eapply MsubstFresh_all; typeclasses eauto. Qed.

Lemma msubst_ret σ v :
  m{σ} (tret v) = tret (m{σ} v).
Proof.
  unfold msubst.
  refine (fin_maps.map_fold_ind
    (fun σ =>
      map_fold (fun x vx acc => {x := vx} acc) (tret v) σ =
      tret (map_fold (fun x vx acc => {x := vx} acc) v σ)) _ _ σ).
  - reflexivity.
  - intros x vx σ' Hfresh Hfold IH.
    rewrite (Hfold value (fun x vx acc => {x := vx} acc) v).
    setoid_rewrite (Hfold tm (fun x vx acc => {x := vx} acc) (tret v)).
    rewrite IH. reflexivity.
Qed.

Lemma msubst_lete σ e1 e2 :
  m{σ} (tlete e1 e2) = tlete (m{σ} e1) (m{σ} e2).
Proof.
  unfold msubst.
  refine (fin_maps.map_fold_ind
    (fun σ =>
      map_fold (fun x vx acc => {x := vx} acc) (tlete e1 e2) σ =
      tlete
        (map_fold (fun x vx acc => {x := vx} acc) e1 σ)
        (map_fold (fun x vx acc => {x := vx} acc) e2 σ)) _ _ σ).
  - reflexivity.
  - intros x vx σ' Hfresh Hfold IH.
    rewrite (Hfold tm (fun x vx acc => {x := vx} acc) e1).
    rewrite (Hfold tm (fun x vx acc => {x := vx} acc) e2).
    setoid_rewrite (Hfold tm (fun x vx acc => {x := vx} acc) (tlete e1 e2)).
    rewrite IH. reflexivity.
Qed.

Lemma msubst_fvar_lookup_closed σ x v :
  closed_env σ →
  σ !! x = Some v →
  m{σ} (vfvar x) = v.
Proof.
  unfold msubst.
  refine (fin_maps.map_fold_ind
    (fun σ => closed_env σ →
      σ !! x = Some v →
      map_fold (fun y vy acc => {y := vy} acc) (vfvar x) σ = v) _ _ σ).
  - intros _ Hlookup. rewrite lookup_empty in Hlookup. discriminate.
  - intros y vy σ' Hfresh Hfold IH Hclosed Hlookup.
    destruct (closed_env_insert σ' y vy Hfresh Hclosed) as [Hvy Hclosed'].
    rewrite Hfold.
    change (map_fold (fun y vy acc => {y := vy} acc) (vfvar x) σ')
      with (m{σ'} (vfvar x)).
    rewrite lookup_insert_Some in Hlookup.
    destruct Hlookup as [[-> ->] | [Hxy Hlookup]].
    + rewrite (msubst_fresh σ' (vfvar x))
        by (change (dom σ' ∩ {[x]} = ∅);
            apply not_elem_of_dom in Hfresh; set_solver).
      change (value_subst x v (vfvar x) = v).
      simpl. rewrite decide_True by reflexivity. reflexivity.
    + replace (m{σ'} (vfvar x)) with v by (symmetry; apply IH; assumption).
      apply subst_fresh.
      rewrite (closed_env_lookup σ' x v Hclosed' Hlookup). set_solver.
Qed.

Lemma msubst_ret_fvar_lookup_closed σ x v :
  closed_env σ →
  σ !! x = Some v →
  m{σ} (tret (vfvar x)) = tret v.
Proof.
  unfold msubst.
  refine (fin_maps.map_fold_ind
    (fun σ => closed_env σ →
      σ !! x = Some v →
      map_fold (fun y vy acc => {y := vy} acc) (tret (vfvar x)) σ = tret v) _ _ σ).
  - intros _ Hlookup. rewrite lookup_empty in Hlookup. discriminate.
  - intros y vy σ' Hfresh Hfold IH Hclosed Hlookup.
    destruct (closed_env_insert σ' y vy Hfresh Hclosed) as [Hvy Hclosed'].
    rewrite Hfold.
    change (map_fold (fun y vy acc => {y := vy} acc) (tret (vfvar x)) σ')
      with (m{σ'} (tret (vfvar x))).
    rewrite lookup_insert_Some in Hlookup.
    destruct Hlookup as [[-> ->] | [Hxy Hlookup]].
    + rewrite (msubst_fresh σ' (tret (vfvar x)))
        by (change (dom σ' ∩ {[x]} = ∅);
            apply not_elem_of_dom in Hfresh; set_solver).
      change (tm_subst x v (tret (vfvar x)) = tret v).
      simpl. rewrite decide_True by reflexivity. reflexivity.
    + replace (m{σ'} (tret (vfvar x))) with (tret v)
        by (symmetry; apply IH; assumption).
      apply subst_fresh.
      change (y ∉ stale v).
      rewrite (closed_env_lookup σ' x v Hclosed' Hlookup). set_solver.
Qed.

Class MsubstFv A `{Stale A} `{SubstV value A} := msubst_fv :
  forall (σ : env) (a : A),
    closed_env σ ->
    stale (m{σ} a) ⊆ stale a.

Lemma MsubstFv_all
    (A : Type)
    (staleA : Stale A)
    (substA : SubstV value A)
    (fv_of_subst_closedA : @FvOfSubstClosed A staleA substA) :
  @MsubstFv A staleA substA.
Proof.
  unfold MsubstFv. intros σ a.
  unfold msubst.
  refine (fin_maps.map_fold_ind
    (fun σ => closed_env σ ->
      stale (map_fold (fun x vx acc => {x := vx} acc) a σ) ⊆ stale a) _ _ σ).
  - intros _. set_solver.
  - intros x vx σ' Hfresh Hfold IH Hclosed.
    destruct (closed_env_insert σ' x vx Hfresh Hclosed) as [Hvx Hclosed'].
    rewrite Hfold.
    rewrite fv_of_subst_closedA by exact Hvx.
    pose proof (IH Hclosed') as HIH.
    set_solver.
Qed.

#[global] Instance MsubstFv_value : MsubstFv value.
Proof. eapply MsubstFv_all; typeclasses eauto. Qed.

#[global] Instance MsubstFv_tm : MsubstFv tm.
Proof. eapply MsubstFv_all; typeclasses eauto. Qed.

Class MsubstRestrict A `{Stale A} `{SubstV value A} := msubst_restrict :
  forall (σ : env) (X : aset) (a : A),
    closed_env σ ->
    stale a ⊆ X ->
    m{map_restrict value σ X} a = m{σ} a.

Lemma MsubstRestrict_all
    (A : Type)
    (staleA : Stale A)
    (substA : SubstV value A)
    (subst_freshA : @SubstFresh A staleA substA)
    (msubst_insertA : @MsubstInsert A substA)
    (msubst_fvA : @MsubstFv A staleA substA) :
  @MsubstRestrict A staleA substA.
Proof.
  unfold MsubstRestrict.
  intros σ X a Hclosed HaX.
  unfold msubst at 2.
  revert Hclosed.
  refine (fin_maps.map_fold_ind
    (fun (σ : env) =>
      closed_env σ ->
      map_fold (fun x vx acc => {x := vx} acc) a
        (map_restrict value σ X) =
      map_fold (fun x vx acc => {x := vx} acc) a σ) _ _ σ).
  - replace (map_restrict value (∅ : env) X) with (∅ : env)
      by (symmetry; apply map_restrict_idemp; set_solver).
    reflexivity.
  - intros x vx σ' Hfresh Hfold IH Hclosed'.
    destruct (closed_env_insert σ' x vx Hfresh Hclosed') as [Hvx Hclosedσ].
    rewrite Hfold.
    destruct (decide (x ∈ X)) as [Hx | Hx].
    + unfold map_restrict at 1.
      rewrite map_filter_insert_True by exact Hx.
      fold (map_restrict value σ' X).
      change (m{<[x := vx]> (map_restrict value σ' X)} a =
              {x := vx} (m{σ'} a)).
      assert (map_restrict value σ' X !! x = None) as Hfresh_restrict.
      {
        unfold map_restrict.
        apply map_lookup_filter_None_2. left. exact Hfresh.
      }
      rewrite msubst_insert by
        (try exact (closed_env_restrict σ' X Hclosedσ);
         try exact Hvx; exact Hfresh_restrict).
      assert (HIH : m{map_restrict value σ' X} a = m{σ'} a).
      { change (map_fold (fun x vx acc => {x := vx} acc) a
          (map_restrict value σ' X) =
          map_fold (fun x vx acc => {x := vx} acc) a σ').
        exact (IH Hclosedσ). }
      change ({x := vx} (m{map_restrict value σ' X} a) =
              {x := vx} (m{σ'} a)).
      rewrite HIH.
      reflexivity.
    + unfold map_restrict at 1.
      rewrite map_filter_insert_not by (intros vi; exact Hx).
      fold (map_restrict value σ' X).
      assert (HIH : m{map_restrict value σ' X} a = m{σ'} a).
      { change (map_fold (fun x vx acc => {x := vx} acc) a
          (map_restrict value σ' X) =
          map_fold (fun x vx acc => {x := vx} acc) a σ').
        exact (IH Hclosedσ). }
      change (m{map_restrict value σ' X} a =
              {x := vx} (m{σ'} a)).
      rewrite HIH.
      symmetry. apply subst_freshA.
      pose proof (msubst_fv σ' a Hclosedσ) as Hfv.
      set_solver.
Qed.

#[global] Instance MsubstRestrict_value : MsubstRestrict value.
Proof. eapply MsubstRestrict_all; typeclasses eauto. Qed.

#[global] Instance MsubstRestrict_tm : MsubstRestrict tm.
Proof. eapply MsubstRestrict_all; typeclasses eauto. Qed.

Class MsubstOpen A `{Open value A} `{SubstV value A} := msubst_open :
  forall (a : A) (k : nat) (u : value) (σ : env),
    closed_env σ ->
    lc_env σ ->
    is_lc u ->
    m{σ} ({k ~> u} a) = {k ~> m{σ} u} (m{σ} a).

Lemma MsubstOpen_all
    (A : Type)
    (openA : Open value A)
    (substA : SubstV value A)
    (subst_openA : @SubstOpen A openA substA) :
  @MsubstOpen A openA substA.
Proof.
  unfold MsubstOpen. intros a k u σ.
  unfold msubst.
  refine (fin_maps.map_fold_ind
    (fun σ => closed_env σ -> lc_env σ -> is_lc u ->
      map_fold (fun x vx acc => {x := vx} acc) ({k ~> u} a) σ =
      {k ~> map_fold (fun x vx acc => {x := vx} acc) u σ}
        (map_fold (fun x vx acc => {x := vx} acc) a σ)) _ _ σ).
  - intros _ _ _. reflexivity.
  - intros x vx σ' Hfresh Hfold IH Hclosed Hlc Hu.
    destruct (closed_env_insert σ' x vx Hfresh Hclosed) as [Hvx_closed Hclosed'].
    destruct (lc_env_insert σ' x vx Hfresh Hlc) as [Hvx_lc Hlc'].
    rewrite !Hfold.
    rewrite IH by eauto.
    rewrite subst_openA by exact Hvx_lc.
    reflexivity.
Qed.

#[global] Instance MsubstOpen_value : MsubstOpen value.
Proof. eapply MsubstOpen_all; typeclasses eauto. Qed.

#[global] Instance MsubstOpen_tm : MsubstOpen tm.
Proof. eapply MsubstOpen_all; typeclasses eauto. Qed.

Class MsubstOpenVar A `{Open value A} `{SubstV value A} := msubst_open_var :
  forall (a : A) (k : nat) (x : atom) (σ : env),
    closed_env σ ->
    lc_env σ ->
    x ∉ dom σ ->
    m{σ} ({k ~> vfvar x} a) = {k ~> vfvar x} (m{σ} a).

Lemma MsubstOpenVar_all
    (A : Type)
    (openA : Open value A)
    (substA : SubstV value A)
    (msubst_openA : @MsubstOpen A openA substA)
    (msubst_fresh_valueA : @MsubstFresh value stale_value_inst subst_value_inst) :
  @MsubstOpenVar A openA substA.
Proof.
  unfold MsubstOpenVar. intros a k x σ Hclosed Hlc_env Hfresh.
  rewrite msubst_open by (try exact Hclosed; try exact Hlc_env; exact (LC_fvar x)).
  rewrite (msubst_fresh σ (vfvar x))
    by (change (dom σ ∩ {[x]} = ∅); set_solver).
  reflexivity.
Qed.

#[global] Instance MsubstOpenVar_value : MsubstOpenVar value.
Proof. eapply MsubstOpenVar_all; typeclasses eauto. Qed.

#[global] Instance MsubstOpenVar_tm : MsubstOpenVar tm.
Proof. eapply MsubstOpenVar_all; typeclasses eauto. Qed.

Class MsubstIntro A `{Stale A} `{Open value A} `{SubstV value A} :=
  msubst_intro :
    forall (a : A) (k : nat) (vx : value) (x : atom) (σ : env),
      closed_env σ ->
      stale vx = ∅ ->
      is_lc vx ->
      lc_env σ ->
      x ∉ dom σ ∪ stale a ->
      {k ~> vx} (m{σ} a) =
      m{<[x := vx]> σ} ({k ~> vfvar x} a).

Lemma MsubstIntro_all
    (A : Type)
    (staleA : Stale A)
    (openA : Open value A)
    (substA : SubstV value A)
    (subst_introA : @SubstIntro A staleA openA substA)
    (msubst_insertA : @MsubstInsert A substA)
    (msubst_openA : @MsubstOpen A openA substA)
    (msubst_fresh_valueA : @MsubstFresh value stale_value_inst subst_value_inst)
    (msubst_fvA : @MsubstFv A staleA substA) :
  @MsubstIntro A staleA openA substA.
Proof.
  unfold MsubstIntro. intros a k vx x σ Hclosed Hvx_closed Hvx_lc Hlc_env Hfresh.
  rewrite (msubst_insert σ x vx)
    by (try exact Hclosed; try exact Hvx_closed; apply not_elem_of_dom; set_solver).
  rewrite msubst_open by (try exact Hclosed; try exact Hlc_env; exact (LC_fvar x)).
  rewrite (msubst_fresh σ (vfvar x))
    by (change (dom σ ∩ {[x]} = ∅); set_solver).
  rewrite subst_introA.
  - reflexivity.
  - pose proof (msubst_fv σ a Hclosed) as Hfv. set_solver.
  - exact Hvx_lc.
Qed.

#[global] Instance MsubstIntro_value : MsubstIntro value.
Proof. eapply MsubstIntro_all; typeclasses eauto. Qed.

#[global] Instance MsubstIntro_tm : MsubstIntro tm.
Proof. eapply MsubstIntro_all; typeclasses eauto. Qed.

Class MsubstLc A `{SubstV value A} `{Lc A} := msubst_lc :
  forall (σ : env) (a : A),
    lc_env σ ->
    is_lc a ->
    is_lc (m{σ} a).

Lemma MsubstLc_all
    (A : Type)
    (substA : SubstV value A)
    (lcA : Lc A)
    (subst_lcA : @SubstLc A substA lcA) :
  @MsubstLc A substA lcA.
Proof.
  unfold MsubstLc. intros σ a.
  unfold msubst.
  refine (fin_maps.map_fold_ind
    (fun σ => lc_env σ ->
      is_lc a ->
      is_lc (map_fold (fun x vx acc => {x := vx} acc) a σ)) _ _ σ).
  - intros _ Hlc. exact Hlc.
  - intros x vx σ' Hfresh Hfold IH Hlc_env Ha.
    destruct (lc_env_insert σ' x vx Hfresh Hlc_env) as [Hvx Hlc_env'].
    rewrite Hfold.
    apply subst_lcA.
    + apply IH; [exact Hlc_env' | exact Ha].
    + exact Hvx.
Qed.

#[global] Instance MsubstLc_value : MsubstLc value.
Proof. eapply MsubstLc_all; typeclasses eauto. Qed.

#[global] Instance MsubstLc_tm : MsubstLc tm.
Proof. eapply MsubstLc_all; typeclasses eauto. Qed.

Ltac msubst_simp :=
  repeat match goal with
  | |- context [m{∅} _] => rewrite msubst_empty
  | H : context [m{∅} _] |- _ => rewrite msubst_empty in H
  | |- context [m{?σ} ?a] => rewrite (msubst_fresh σ a) by set_solver
  | H : context [m{?σ} ?a] |- _ => rewrite (msubst_fresh σ a) in H by set_solver
  | |- context [m{<[?x := ?vx]> ?σ} _] =>
      rewrite (msubst_insert σ x vx); eauto
  | H : context [m{<[?x := ?vx]> ?σ} _] |- _ =>
      rewrite (msubst_insert σ x vx) in H; eauto
  end.
