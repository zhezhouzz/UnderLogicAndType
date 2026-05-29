From ContextLogic Require Export LogicQualifier.
From ContextBase Require Import BaseTactics LogicVarOpenEnv LogicVarShift.
From Stdlib Require Import Logic.FunctionalExtensionality Logic.PropExtensionality.

(** * Context Logic syntax

    Formulas track lvar support first; atom free variables are the projection
    [lvars_fv].  Exists is intentionally absent in this phase because the type
    denotation path does not need it yet. *)

Section Formula.

Context {V : Type} `{ValueSig V}.

Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation LogicQualifierT := (logic_qualifier (V := V)) (only parsing).
Local Notation LStoreT := (gmap logic_var V) (only parsing).

Inductive Formula : Type :=
  | FTrue
  | FFalse
  | FAtom    (a : LogicQualifierT)
  | FAnd     (p q : Formula)
  | FOr      (p q : Formula)
  | FImpl    (p q : Formula)
  | FStar    (p q : Formula)
  | FWand    (p q : Formula)
  | FPlus    (p q : Formula)
  | FForall  (p : Formula)
  | FOver    (p : Formula)
  | FUnder   (p : Formula)
  | FFibVars (D : lvset) (p : Formula).

Fixpoint formula_lvars (φ : Formula) : lvset :=
  match φ with
  | FTrue | FFalse => ∅
  | FAtom q => lqual_lvars q
  | FAnd p q | FOr p q | FImpl p q
  | FStar p q | FWand p q | FPlus p q =>
      formula_lvars p ∪ formula_lvars q
  | FForall p => formula_lvars p
  | FOver p | FUnder p => formula_lvars p
  | FFibVars D p => D ∪ formula_lvars p
  end.

Definition formula_fv (φ : Formula) : aset :=
  lvars_fv (formula_lvars φ).

Definition formula_stale : Formula → aset := formula_fv.

#[global] Instance stale_formula : Stale Formula := formula_fv.
Arguments stale_formula /.

Lemma formula_fv_true :
  formula_fv FTrue = ∅.
Proof. reflexivity. Qed.

Lemma formula_fv_false :
  formula_fv FFalse = ∅.
Proof. reflexivity. Qed.

Lemma formula_fv_atom q :
  formula_fv (FAtom q) = lvars_fv (lqual_lvars q).
Proof. reflexivity. Qed.

Lemma formula_fv_and p q :
  formula_fv (FAnd p q) = formula_fv p ∪ formula_fv q.
Proof. unfold formula_fv; cbn [formula_lvars]; apply lvars_fv_union. Qed.

Lemma formula_fv_or p q :
  formula_fv (FOr p q) = formula_fv p ∪ formula_fv q.
Proof. unfold formula_fv; cbn [formula_lvars]; apply lvars_fv_union. Qed.

Lemma formula_fv_impl p q :
  formula_fv (FImpl p q) = formula_fv p ∪ formula_fv q.
Proof. unfold formula_fv; cbn [formula_lvars]; apply lvars_fv_union. Qed.

Lemma formula_fv_star p q :
  formula_fv (FStar p q) = formula_fv p ∪ formula_fv q.
Proof. unfold formula_fv; cbn [formula_lvars]; apply lvars_fv_union. Qed.

Lemma formula_fv_wand p q :
  formula_fv (FWand p q) = formula_fv p ∪ formula_fv q.
Proof. unfold formula_fv; cbn [formula_lvars]; apply lvars_fv_union. Qed.

Lemma formula_fv_plus p q :
  formula_fv (FPlus p q) = formula_fv p ∪ formula_fv q.
Proof. unfold formula_fv; cbn [formula_lvars]; apply lvars_fv_union. Qed.

Lemma formula_fv_forall p :
  formula_fv (FForall p) = formula_fv p.
Proof. reflexivity. Qed.

Lemma formula_fv_over p :
  formula_fv (FOver p) = formula_fv p.
Proof. reflexivity. Qed.

Lemma formula_fv_under p :
  formula_fv (FUnder p) = formula_fv p.
Proof. reflexivity. Qed.

Lemma formula_fv_fibvars D p :
  formula_fv (FFibVars D p) = lvars_fv D ∪ formula_fv p.
Proof. unfold formula_fv; cbn [formula_lvars]; apply lvars_fv_union. Qed.

Fixpoint formula_measure (φ : Formula) : nat :=
  match φ with
  | FTrue | FFalse | FAtom _ => 1
  | FAnd p q | FOr p q | FImpl p q | FStar p q | FWand p q | FPlus p q =>
      1 + formula_measure p + formula_measure q
  | FForall p | FOver p | FUnder p | FFibVars _ p =>
      1 + formula_measure p
  end.

Fixpoint formula_mlsubst (ρ : LStoreT) (φ : Formula) : Formula :=
  match φ with
  | FTrue => FTrue
  | FFalse => FFalse
  | FAtom q => FAtom (lqual_mlsubst ρ q)
  | FAnd p q => FAnd (formula_mlsubst ρ p) (formula_mlsubst ρ q)
  | FOr p q => FOr (formula_mlsubst ρ p) (formula_mlsubst ρ q)
  | FImpl p q => FImpl (formula_mlsubst ρ p) (formula_mlsubst ρ q)
  | FStar p q => FStar (formula_mlsubst ρ p) (formula_mlsubst ρ q)
  | FWand p q => FWand (formula_mlsubst ρ p) (formula_mlsubst ρ q)
  | FPlus p q => FPlus (formula_mlsubst ρ p) (formula_mlsubst ρ q)
  | FForall p => FForall (formula_mlsubst ρ p)
  | FOver p => FOver (formula_mlsubst ρ p)
  | FUnder p => FUnder (formula_mlsubst ρ p)
  | FFibVars D p =>
      FFibVars (D ∖ dom (ρ : gmap logic_var V)) (formula_mlsubst ρ p)
  end.

Definition formula_msubst_store (σ : Store (V := V)) (φ : Formula) : Formula :=
  formula_mlsubst (lstore_lift_free σ) φ.

Lemma formula_mlsubst_preserves_measure ρ φ :
  formula_measure (formula_mlsubst ρ φ) = formula_measure φ.
Proof.
  induction φ; simpl; eauto; lia.
Qed.

Lemma formula_msubst_store_preserves_measure σ φ :
  formula_measure (formula_msubst_store σ φ) = formula_measure φ.
Proof. apply formula_mlsubst_preserves_measure. Qed.

Lemma formula_mlsubst_fv_subset ρ φ :
  formula_fv (formula_mlsubst ρ φ) ⊆ formula_fv φ.
Proof.
  induction φ;
    unfold formula_fv in *; cbn [formula_mlsubst formula_lvars];
    try set_solver.
  - destruct a as [D P]. cbn [lqual_mlsubst lqual_lvars].
    eapply lvars_fv_mono. set_solver.
  - rewrite !lvars_fv_union. set_solver.
  - rewrite !lvars_fv_union. set_solver.
  - rewrite !lvars_fv_union. set_solver.
  - rewrite !lvars_fv_union. set_solver.
  - rewrite !lvars_fv_union. set_solver.
  - rewrite !lvars_fv_union. set_solver.
  - rewrite !lvars_fv_union.
    pose proof (lvars_fv_mono (D ∖ dom (ρ : gmap logic_var V)) D ltac:(set_solver)).
    set_solver.
Qed.

Lemma formula_msubst_store_fv_subset σ φ :
  formula_fv (formula_msubst_store σ φ) ⊆ formula_fv φ.
Proof. apply formula_mlsubst_fv_subset. Qed.

Fixpoint formula_open (k : nat) (x : atom) (φ : Formula) : Formula :=
  match φ with
  | FTrue => FTrue
  | FFalse => FFalse
  | FAtom q => FAtom (lqual_open k x q)
  | FAnd p q => FAnd (formula_open k x p) (formula_open k x q)
  | FOr p q => FOr (formula_open k x p) (formula_open k x q)
  | FImpl p q => FImpl (formula_open k x p) (formula_open k x q)
  | FStar p q => FStar (formula_open k x p) (formula_open k x q)
  | FWand p q => FWand (formula_open k x p) (formula_open k x q)
  | FPlus p q => FPlus (formula_open k x p) (formula_open k x q)
  | FForall p => FForall (formula_open (S k) x p)
  | FOver p => FOver (formula_open k x p)
  | FUnder p => FUnder (formula_open k x p)
  | FFibVars D p => FFibVars (lvars_open k x D) (formula_open k x p)
  end.

Lemma formula_open_true k x :
  formula_open k x FTrue = FTrue.
Proof. reflexivity. Qed.

Lemma formula_open_false k x :
  formula_open k x FFalse = FFalse.
Proof. reflexivity. Qed.

Lemma formula_open_atom k x q :
  formula_open k x (FAtom q) = FAtom (lqual_open k x q).
Proof. reflexivity. Qed.

Lemma formula_open_and k x p q :
  formula_open k x (FAnd p q) =
  FAnd (formula_open k x p) (formula_open k x q).
Proof. reflexivity. Qed.

Lemma formula_open_or k x p q :
  formula_open k x (FOr p q) =
  FOr (formula_open k x p) (formula_open k x q).
Proof. reflexivity. Qed.

Lemma formula_open_impl k x p q :
  formula_open k x (FImpl p q) =
  FImpl (formula_open k x p) (formula_open k x q).
Proof. reflexivity. Qed.

Lemma formula_open_star k x p q :
  formula_open k x (FStar p q) =
  FStar (formula_open k x p) (formula_open k x q).
Proof. reflexivity. Qed.

Lemma formula_open_wand k x p q :
  formula_open k x (FWand p q) =
  FWand (formula_open k x p) (formula_open k x q).
Proof. reflexivity. Qed.

Lemma formula_open_plus k x p q :
  formula_open k x (FPlus p q) =
  FPlus (formula_open k x p) (formula_open k x q).
Proof. reflexivity. Qed.

Lemma formula_open_forall k x p :
  formula_open k x (FForall p) =
  FForall (formula_open (S k) x p).
Proof. reflexivity. Qed.

Lemma formula_open_over k x p :
  formula_open k x (FOver p) =
  FOver (formula_open k x p).
Proof. reflexivity. Qed.

Lemma formula_open_under k x p :
  formula_open k x (FUnder p) =
  FUnder (formula_open k x p).
Proof. reflexivity. Qed.

Lemma formula_open_fibvars k x D p :
  formula_open k x (FFibVars D p) =
  FFibVars (lvars_open k x D) (formula_open k x p).
Proof. reflexivity. Qed.

Lemma formula_open_preserves_measure k x φ :
  formula_measure (formula_open k x φ) = formula_measure φ.
Proof.
  revert k. induction φ; intros k; simpl; eauto; lia.
Qed.

Lemma formula_open_commute_fresh i j x y φ :
  i <> j ->
  x <> y ->
  formula_open i x (formula_open j y φ) =
  formula_open j y (formula_open i x φ).
Proof.
  intros Hij Hxy.
  induction φ in i, j, Hij |- *; cbn [formula_open]; try reflexivity.
  - rewrite lqual_open_commute_fresh by assumption. reflexivity.
  - rewrite IHφ1 by assumption. rewrite IHφ2 by assumption. reflexivity.
  - rewrite IHφ1 by assumption. rewrite IHφ2 by assumption. reflexivity.
  - rewrite IHφ1 by assumption. rewrite IHφ2 by assumption. reflexivity.
  - rewrite IHφ1 by assumption. rewrite IHφ2 by assumption. reflexivity.
  - rewrite IHφ1 by assumption. rewrite IHφ2 by assumption. reflexivity.
  - rewrite IHφ1 by assumption. rewrite IHφ2 by assumption. reflexivity.
  - rewrite IHφ by lia. reflexivity.
  - rewrite IHφ by assumption. reflexivity.
  - rewrite IHφ by assumption. reflexivity.
  - rewrite lvars_open_commute_fresh by assumption.
    rewrite IHφ by assumption. reflexivity.
Qed.

Definition formula_open_env (η : gmap nat atom) (φ : Formula) : Formula :=
  map_fold (fun k x acc => formula_open k x acc) φ η.

Lemma formula_open_env_empty φ :
  formula_open_env ∅ φ = φ.
Proof.
  unfold formula_open_env. rewrite map_fold_empty. reflexivity.
Qed.

Lemma formula_open_env_singleton k x φ :
  formula_open_env (<[k := x]> ∅) φ = formula_open k x φ.
Proof.
  unfold formula_open_env.
  change (<[k := x]> (∅ : gmap nat atom)) with ({[k := x]} : gmap nat atom).
  rewrite map_fold_singleton. reflexivity.
Qed.

Lemma formula_open_env_insert_fresh η k x φ :
  η !! k = None ->
  open_env_avoids_atom x η ->
  open_env_values_inj η ->
  formula_open_env (<[k := x]> η) φ =
  formula_open k x (formula_open_env η φ).
Proof.
  intros Hfresh Havoid Hinj.
  unfold formula_open_env.
  apply (map_fold_insert_L (M:=gmap nat) (A:=atom) (B:=Formula)
    (fun k x acc => formula_open k x acc) φ k x η).
  - intros i j xi xj acc Hij Hi Hj.
    apply formula_open_commute_fresh; [exact Hij|].
    intros Heq. subst xj.
    pose proof (open_env_values_inj_insert k x η Hfresh Havoid Hinj)
      as Hinj'.
    apply Hij. eapply Hinj'; eassumption.
  - exact Hfresh.
Qed.

Lemma formula_open_env_true η :
  formula_open_env η FTrue = FTrue.
Proof.
  unfold formula_open_env.
  refine (fin_maps.map_fold_ind
    (fun η => map_fold (fun k x acc => formula_open k x acc) FTrue η = FTrue)
    _ _ η).
  - rewrite map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH. rewrite Hfold, IH. reflexivity.
Qed.

Lemma formula_open_env_false η :
  formula_open_env η FFalse = FFalse.
Proof.
  unfold formula_open_env.
  refine (fin_maps.map_fold_ind
    (fun η => map_fold (fun k x acc => formula_open k x acc) FFalse η = FFalse)
    _ _ η).
  - rewrite map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH. rewrite Hfold, IH. reflexivity.
Qed.

Lemma formula_open_env_and η φ ψ :
  formula_open_env η (FAnd φ ψ) =
  FAnd (formula_open_env η φ) (formula_open_env η ψ).
Proof.
  unfold formula_open_env.
  refine (fin_maps.map_fold_ind
    (fun η => map_fold (fun k x acc => formula_open k x acc) (FAnd φ ψ) η =
      FAnd
        (map_fold (fun k x acc => formula_open k x acc) φ η)
        (map_fold (fun k x acc => formula_open k x acc) ψ η)) _ _ η).
  - rewrite !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite !Hfold. cbn [formula_open]. rewrite IH. reflexivity.
Qed.

Lemma formula_open_env_or η φ ψ :
  formula_open_env η (FOr φ ψ) =
  FOr (formula_open_env η φ) (formula_open_env η ψ).
Proof.
  unfold formula_open_env.
  refine (fin_maps.map_fold_ind
    (fun η => map_fold (fun k x acc => formula_open k x acc) (FOr φ ψ) η =
      FOr
        (map_fold (fun k x acc => formula_open k x acc) φ η)
        (map_fold (fun k x acc => formula_open k x acc) ψ η)) _ _ η).
  - rewrite !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite !Hfold. cbn [formula_open]. rewrite IH. reflexivity.
Qed.

Lemma formula_open_env_impl η φ ψ :
  formula_open_env η (FImpl φ ψ) =
  FImpl (formula_open_env η φ) (formula_open_env η ψ).
Proof.
  unfold formula_open_env.
  refine (fin_maps.map_fold_ind
    (fun η => map_fold (fun k x acc => formula_open k x acc) (FImpl φ ψ) η =
      FImpl
        (map_fold (fun k x acc => formula_open k x acc) φ η)
        (map_fold (fun k x acc => formula_open k x acc) ψ η)) _ _ η).
  - rewrite !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite !Hfold. cbn [formula_open]. rewrite IH. reflexivity.
Qed.

Lemma formula_open_env_star η φ ψ :
  formula_open_env η (FStar φ ψ) =
  FStar (formula_open_env η φ) (formula_open_env η ψ).
Proof.
  unfold formula_open_env.
  refine (fin_maps.map_fold_ind
    (fun η => map_fold (fun k x acc => formula_open k x acc) (FStar φ ψ) η =
      FStar
        (map_fold (fun k x acc => formula_open k x acc) φ η)
        (map_fold (fun k x acc => formula_open k x acc) ψ η)) _ _ η).
  - rewrite !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite !Hfold. cbn [formula_open]. rewrite IH. reflexivity.
Qed.

Lemma formula_open_env_wand η φ ψ :
  formula_open_env η (FWand φ ψ) =
  FWand (formula_open_env η φ) (formula_open_env η ψ).
Proof.
  unfold formula_open_env.
  refine (fin_maps.map_fold_ind
    (fun η => map_fold (fun k x acc => formula_open k x acc) (FWand φ ψ) η =
      FWand
        (map_fold (fun k x acc => formula_open k x acc) φ η)
        (map_fold (fun k x acc => formula_open k x acc) ψ η)) _ _ η).
  - rewrite !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite !Hfold. cbn [formula_open]. rewrite IH. reflexivity.
Qed.

Lemma formula_open_env_plus η φ ψ :
  formula_open_env η (FPlus φ ψ) =
  FPlus (formula_open_env η φ) (formula_open_env η ψ).
Proof.
  unfold formula_open_env.
  refine (fin_maps.map_fold_ind
    (fun η => map_fold (fun k x acc => formula_open k x acc) (FPlus φ ψ) η =
      FPlus
        (map_fold (fun k x acc => formula_open k x acc) φ η)
        (map_fold (fun k x acc => formula_open k x acc) ψ η)) _ _ η).
  - rewrite !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite !Hfold. cbn [formula_open]. rewrite IH. reflexivity.
Qed.

Lemma formula_open_env_over η φ :
  formula_open_env η (FOver φ) =
  FOver (formula_open_env η φ).
Proof.
  unfold formula_open_env.
  refine (fin_maps.map_fold_ind
    (fun η => map_fold (fun k x acc => formula_open k x acc) (FOver φ) η =
      FOver (map_fold (fun k x acc => formula_open k x acc) φ η)) _ _ η).
  - rewrite !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite !Hfold. cbn [formula_open]. rewrite IH. reflexivity.
Qed.

Lemma formula_open_env_under η φ :
  formula_open_env η (FUnder φ) =
  FUnder (formula_open_env η φ).
Proof.
  unfold formula_open_env.
  refine (fin_maps.map_fold_ind
    (fun η => map_fold (fun k x acc => formula_open k x acc) (FUnder φ) η =
      FUnder (map_fold (fun k x acc => formula_open k x acc) φ η)) _ _ η).
  - rewrite !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite !Hfold. cbn [formula_open]. rewrite IH. reflexivity.
Qed.

Lemma formula_open_env_fibvars η D φ :
  open_env_fresh_for_lvars η D ->
  formula_open_env η (FFibVars D φ) =
  FFibVars (lvars_open_env η D) (formula_open_env η φ).
Proof.
  induction η as [|k x η Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - intros _. rewrite formula_open_env_empty, lvars_open_env_empty.
    reflexivity.
  - intros Henv.
    pose proof (open_env_fresh_for_lvars_insert_head η k x D Hfresh Henv)
      as Hhead.
    pose proof (open_env_fresh_for_lvars_insert_tail η k x D Hfresh Henv)
      as Htail.
    unfold formula_open_env.
    rewrite !Hfold.
    fold (formula_open_env η (FFibVars D φ)).
    fold (formula_open_env η φ).
    rewrite IH by exact Htail.
    cbn [formula_open].
    rewrite lvars_open_env_insert_fresh by (exact Hfresh || exact Hhead).
    reflexivity.
Qed.

Lemma formula_open_env_forall η φ :
  open_env_values_inj η ->
  formula_open_env η (FForall φ) =
  FForall (formula_open_env ((kmap S η)) φ).
Proof.
  induction η as [|k x η Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - intros _. rewrite formula_open_env_empty, kmap_empty,
      formula_open_env_empty.
    reflexivity.
  - intros Hinj.
    pose proof (open_env_values_inj_insert_inv η k x Hfresh Hinj)
      as [Hinjη Havoid].
    rewrite formula_open_env_insert_fresh by assumption.
    rewrite IH by exact Hinjη.
    cbn [formula_open].
    rewrite open_env_lift_insert.
    rewrite formula_open_env_insert_fresh
      by (try better_base_solver;
          try apply open_env_values_inj_lift; assumption).
    reflexivity.
Qed.

Fixpoint formula_lvars_at (d : nat) (φ : Formula) : lvset :=
  match φ with
  | FTrue | FFalse => ∅
  | FAtom q => lvars_at_depth d (lqual_lvars q)
  | FAnd p q | FOr p q | FImpl p q
  | FStar p q | FWand p q | FPlus p q =>
      formula_lvars_at d p ∪ formula_lvars_at d q
  | FForall p => formula_lvars_at (S d) p
  | FOver p | FUnder p => formula_lvars_at d p
  | FFibVars D p => lvars_at_depth d D ∪ formula_lvars_at d p
  end.

Lemma formula_lvars_at_fv d (φ : Formula) :
  lvars_fv (formula_lvars_at d φ) = formula_fv φ.
Proof.
  induction φ in d |- *; cbn [formula_lvars_at];
    rewrite ?lvars_fv_lvars_at_depth, ?lvars_fv_union,
      ?IHφ1, ?IHφ2, ?IHφ;
    rewrite ?formula_fv_true, ?formula_fv_false, ?formula_fv_atom,
      ?formula_fv_and, ?formula_fv_or, ?formula_fv_impl,
      ?formula_fv_star, ?formula_fv_wand, ?formula_fv_plus,
      ?formula_fv_forall, ?formula_fv_over, ?formula_fv_under,
      ?formula_fv_fibvars;
    rewrite ?lvars_fv_lvars_at_depth;
    reflexivity.
Qed.

Lemma formula_lvars_at_open d k y (φ : Formula) :
  formula_lvars_at d (formula_open (d + k) y φ) =
  lvars_open k y (formula_lvars_at d φ).
Proof.
  induction φ in d, k |- *; cbn [formula_open formula_lvars_at].
  - set_solver.
  - set_solver.
  - match goal with
    | |- context [lqual_open _ _ ?q] => destruct q as [D P]
    end.
    cbn [lqual_open lqual_lvars lqual_dom].
    apply lvars_at_depth_open.
  - rewrite IHφ1, IHφ2.
    symmetry. rewrite lvars_open_union. reflexivity.
  - rewrite IHφ1, IHφ2.
    symmetry. rewrite lvars_open_union. reflexivity.
  - rewrite IHφ1, IHφ2.
    symmetry. rewrite lvars_open_union. reflexivity.
  - rewrite IHφ1, IHφ2.
    symmetry. rewrite lvars_open_union. reflexivity.
  - rewrite IHφ1, IHφ2.
    symmetry. rewrite lvars_open_union. reflexivity.
  - rewrite IHφ1, IHφ2.
    symmetry. rewrite lvars_open_union. reflexivity.
  - replace (S (d + k)) with (S d + k) by lia.
    apply IHφ.
  - apply IHφ.
  - apply IHφ.
  - rewrite lvars_at_depth_open.
    rewrite IHφ.
    symmetry. rewrite lvars_open_union. reflexivity.
Qed.

Lemma formula_open_fv_subset k x φ :
  formula_fv (formula_open k x φ) ⊆ formula_fv φ ∪ {[x]}.
Proof.
  revert k. induction φ; intros k;
    unfold formula_fv in *;
    cbn [formula_lvars formula_open].
  - set_solver.
  - set_solver.
  - destruct a as [D P]. cbn [lqual_fv lqual_dom lqual_open].
    apply lvars_fv_open_subset.
  - rewrite !lvars_fv_union. specialize (IHφ1 k). specialize (IHφ2 k).
    set_solver.
  - rewrite !lvars_fv_union. specialize (IHφ1 k). specialize (IHφ2 k).
    set_solver.
  - rewrite !lvars_fv_union. specialize (IHφ1 k). specialize (IHφ2 k).
    set_solver.
  - rewrite !lvars_fv_union. specialize (IHφ1 k). specialize (IHφ2 k).
    set_solver.
  - rewrite !lvars_fv_union. specialize (IHφ1 k). specialize (IHφ2 k).
    set_solver.
  - rewrite !lvars_fv_union. specialize (IHφ1 k). specialize (IHφ2 k).
    set_solver.
  - apply IHφ.
  - apply IHφ.
  - apply IHφ.
  - rewrite !lvars_fv_union.
    pose proof (lvars_fv_open_subset k x D) as HD.
    specialize (IHφ k). set_solver.
Qed.

Lemma formula_open_fv_subset_env k x φ X :
  formula_fv φ ⊆ X →
  formula_fv (formula_open k x φ) ⊆ X ∪ {[x]}.
Proof.
  intros Hfv.
  pose proof (formula_open_fv_subset k x φ) as Hopen.
  set_solver.
Qed.

Lemma formula_measure_pos (φ : Formula) :
  0 < formula_measure φ.
Proof. induction φ; simpl; lia. Qed.

Definition FPure (P : Prop) : Formula :=
  FAtom (lqual ∅ (λ _, P)).

Definition FResourceAtom {A : Type} `{IntoLVars A}
    (D : A) (P : LWorldOn (V := V) (into_lvars D) → Prop) : Formula :=
  FAtom (lqual (into_lvars D) P).

Lemma formula_fv_FResourceAtom_lvars D P :
  formula_fv (FResourceAtom D P) = lvars_fv D.
Proof. reflexivity. Qed.

Lemma formula_open_FResourceAtom_lvars k x (D : lvset) P :
  formula_open k x (FResourceAtom D P) =
  FResourceAtom (lvars_open k x D)
    (λ w, P (lworld_on_open_back k x D w)).
Proof. reflexivity. Qed.

Lemma FResourceAtom_ext (D : lvset) P1 P2 :
  (∀ m, P1 m ↔ P2 m) →
  FResourceAtom D P1 = FResourceAtom D P2.
Proof.
  intros HP. unfold FResourceAtom. simpl.
  f_equal. f_equal.
  apply functional_extensionality. intros m.
  apply propositional_extensionality. apply HP.
Qed.

End Formula.

(** * ContextLogic.FormulaSyntax

    Small normalization tactics for formula syntax proofs.  These live below
    formula semantics so lower-layer proofs can use them without importing the
    denotation-level automation. *)


Ltac formula_fv_syntax_norm :=
  unfold formula_fv;
  cbn [formula_lvars];
  rewrite ?formula_fv_true, ?formula_fv_false, ?formula_fv_atom;
  rewrite ?formula_fv_and, ?formula_fv_or, ?formula_fv_impl;
  rewrite ?formula_fv_star, ?formula_fv_wand, ?formula_fv_plus;
  rewrite ?formula_fv_forall, ?formula_fv_over, ?formula_fv_under;
  rewrite ?formula_fv_fibvars;
  rewrite ?lvars_fv_union.

Ltac formula_fv_syntax_norm_in H :=
  unfold formula_fv in H;
  cbn [formula_lvars] in H;
  rewrite ?formula_fv_true in H;
  rewrite ?formula_fv_false in H;
  rewrite ?formula_fv_atom in H;
  rewrite ?formula_fv_and in H;
  rewrite ?formula_fv_or in H;
  rewrite ?formula_fv_impl in H;
  rewrite ?formula_fv_star in H;
  rewrite ?formula_fv_wand in H;
  rewrite ?formula_fv_plus in H;
  rewrite ?formula_fv_forall in H;
  rewrite ?formula_fv_over in H;
  rewrite ?formula_fv_under in H;
  rewrite ?formula_fv_fibvars in H;
  rewrite ?lvars_fv_union in H.

Ltac formula_open_syntax_norm :=
  rewrite ?formula_open_true, ?formula_open_false, ?formula_open_atom;
  rewrite ?formula_open_and, ?formula_open_or, ?formula_open_impl;
  rewrite ?formula_open_star, ?formula_open_wand, ?formula_open_plus;
  rewrite ?formula_open_forall;
  rewrite ?formula_open_over, ?formula_open_under, ?formula_open_fibvars.

Ltac formula_open_syntax_norm_in H :=
  rewrite ?formula_open_true in H;
  rewrite ?formula_open_false in H;
  rewrite ?formula_open_atom in H;
  rewrite ?formula_open_and in H;
  rewrite ?formula_open_or in H;
  rewrite ?formula_open_impl in H;
  rewrite ?formula_open_star in H;
  rewrite ?formula_open_wand in H;
  rewrite ?formula_open_plus in H;
  rewrite ?formula_open_forall in H;
  rewrite ?formula_open_over in H;
  rewrite ?formula_open_under in H;
  rewrite ?formula_open_fibvars in H.

Ltac formula_open_env_syntax_norm :=
  rewrite ?formula_open_env_true, ?formula_open_env_false;
  rewrite ?formula_open_env_and, ?formula_open_env_or, ?formula_open_env_impl;
  rewrite ?formula_open_env_star, ?formula_open_env_wand, ?formula_open_env_plus;
  rewrite ?formula_open_env_over, ?formula_open_env_under;
  try rewrite ?formula_open_env_fibvars by eauto;
  try rewrite ?formula_open_env_forall by eauto.

Ltac formula_open_env_syntax_norm_in H :=
  rewrite ?formula_open_env_true in H;
  rewrite ?formula_open_env_false in H;
  rewrite ?formula_open_env_and in H;
  rewrite ?formula_open_env_or in H;
  rewrite ?formula_open_env_impl in H;
  rewrite ?formula_open_env_star in H;
  rewrite ?formula_open_env_wand in H;
  rewrite ?formula_open_env_plus in H;
  rewrite ?formula_open_env_over in H;
  rewrite ?formula_open_env_under in H;
  try rewrite ?formula_open_env_fibvars in H by eauto;
  try rewrite ?formula_open_env_forall in H by eauto.

Ltac formula_syntax_norm :=
  formula_fv_syntax_norm;
  formula_open_syntax_norm;
  formula_open_env_syntax_norm.

Ltac formula_syntax_norm_in H :=
  formula_fv_syntax_norm_in H;
  formula_open_syntax_norm_in H;
  formula_open_env_syntax_norm_in H.
