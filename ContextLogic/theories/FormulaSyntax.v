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

Lemma formula_mlsubst_union
    (ρ1 ρ2 : LStoreT) (φ : Formula) :
  storeA_compat ρ1 ρ2 ->
  formula_mlsubst ρ2 (formula_mlsubst ρ1 φ) =
  formula_mlsubst (ρ1 ∪ ρ2) φ.
Proof.
  intros Hcompat.
  induction φ; cbn [formula_mlsubst];
    try (rewrite ?IHφ1, ?IHφ2, ?IHφ; eauto using storeA_compat_restrict_r; reflexivity).
  - f_equal. apply lqual_mlsubst_union. exact Hcompat.
  - rewrite IHφ by exact Hcompat.
    f_equal.
    rewrite dom_union_L.
    set_solver.
Qed.

Lemma formula_msubst_store_fibvars σ D φ :
  formula_msubst_store σ (FFibVars D φ) =
  FFibVars (D ∖ lvars_of_atoms (dom (σ : Store (V := V))))
    (formula_msubst_store σ φ).
Proof.
  unfold formula_msubst_store. cbn [formula_mlsubst].
  rewrite dom_lstore_lift_free. reflexivity.
Qed.

Lemma formula_msubst_store_restrict_fv_subset
    (σ : Store (V := V)) (φ : Formula) (X : aset) :
  formula_fv φ ⊆ X ->
  formula_msubst_store σ φ =
  formula_msubst_store (store_restrict σ X) φ.
Proof.
  revert X.
  induction φ; intros X Hsub;
    unfold formula_msubst_store; cbn [formula_mlsubst];
    try reflexivity.
  - change (FAtom (lqual_msubst_store σ a) =
      FAtom (lqual_msubst_store (store_restrict σ X) a)).
    f_equal. apply lqual_msubst_store_restrict_subset.
    rewrite formula_fv_atom in Hsub. exact Hsub.
  - fold (formula_msubst_store σ φ1).
    fold (formula_msubst_store σ φ2).
    fold (formula_msubst_store (store_restrict σ X) φ1).
    fold (formula_msubst_store (store_restrict σ X) φ2).
    rewrite (IHφ1 X), (IHφ2 X); [reflexivity| |];
      rewrite formula_fv_and in Hsub; set_solver.
  - fold (formula_msubst_store σ φ1).
    fold (formula_msubst_store σ φ2).
    fold (formula_msubst_store (store_restrict σ X) φ1).
    fold (formula_msubst_store (store_restrict σ X) φ2).
    rewrite (IHφ1 X), (IHφ2 X); [reflexivity| |];
      rewrite formula_fv_or in Hsub; set_solver.
  - fold (formula_msubst_store σ φ1).
    fold (formula_msubst_store σ φ2).
    fold (formula_msubst_store (store_restrict σ X) φ1).
    fold (formula_msubst_store (store_restrict σ X) φ2).
    rewrite (IHφ1 X), (IHφ2 X); [reflexivity| |];
      rewrite formula_fv_impl in Hsub; set_solver.
  - fold (formula_msubst_store σ φ1).
    fold (formula_msubst_store σ φ2).
    fold (formula_msubst_store (store_restrict σ X) φ1).
    fold (formula_msubst_store (store_restrict σ X) φ2).
    rewrite (IHφ1 X), (IHφ2 X); [reflexivity| |];
      rewrite formula_fv_star in Hsub; set_solver.
  - fold (formula_msubst_store σ φ1).
    fold (formula_msubst_store σ φ2).
    fold (formula_msubst_store (store_restrict σ X) φ1).
    fold (formula_msubst_store (store_restrict σ X) φ2).
    rewrite (IHφ1 X), (IHφ2 X); [reflexivity| |];
      rewrite formula_fv_wand in Hsub; set_solver.
  - fold (formula_msubst_store σ φ1).
    fold (formula_msubst_store σ φ2).
    fold (formula_msubst_store (store_restrict σ X) φ1).
    fold (formula_msubst_store (store_restrict σ X) φ2).
    rewrite (IHφ1 X), (IHφ2 X); [reflexivity| |];
      rewrite formula_fv_plus in Hsub; set_solver.
  - fold (formula_msubst_store σ φ).
    fold (formula_msubst_store (store_restrict σ X) φ).
    rewrite (IHφ X); [reflexivity|].
    rewrite formula_fv_forall in Hsub. exact Hsub.
  - fold (formula_msubst_store σ φ).
    fold (formula_msubst_store (store_restrict σ X) φ).
    rewrite (IHφ X); [reflexivity|].
    rewrite formula_fv_over in Hsub. exact Hsub.
  - fold (formula_msubst_store σ φ).
    fold (formula_msubst_store (store_restrict σ X) φ).
    rewrite (IHφ X); [reflexivity|].
    rewrite formula_fv_under in Hsub. exact Hsub.
  - fold (formula_msubst_store σ φ).
    fold (formula_msubst_store (store_restrict σ X) φ).
    rewrite (IHφ X).
    2:{ rewrite formula_fv_fibvars in Hsub. set_solver. }
    f_equal.
    change (D ∖ dom (lstore_lift_free σ : LStoreT) =
      D ∖ dom (lstore_lift_free (store_restrict σ X) : LStoreT)).
    assert (HρD :
      storeA_restrict
        (lstore_lift_free (store_restrict σ X) : LStoreT) D =
      storeA_restrict (lstore_lift_free σ : LStoreT) D).
    {
      apply lstore_lift_free_restrict_lvars_subset_eq.
      rewrite formula_fv_fibvars in Hsub. set_solver.
    }
    pose proof (f_equal (fun s : gmap logic_var V => dom s) HρD)
      as Hdom_restrict.
    rewrite !storeA_restrict_dom in Hdom_restrict.
    apply set_eq. intros v.
    rewrite !elem_of_difference.
    set_solver.
Qed.

Lemma formula_msubst_store_restrict_fv
    (σ : Store (V := V)) (φ : Formula) :
  formula_msubst_store σ φ =
  formula_msubst_store (store_restrict σ (formula_fv φ)) φ.
Proof.
  apply formula_msubst_store_restrict_fv_subset. reflexivity.
Qed.

Lemma formula_msubst_store_union
    (σ1 σ2 : Store (V := V)) (φ : Formula) :
  storeA_compat σ1 σ2 ->
  formula_msubst_store σ2 (formula_msubst_store σ1 φ) =
  formula_msubst_store (σ1 ∪ σ2) φ.
Proof.
  intros Hcompat.
  unfold formula_msubst_store.
  rewrite formula_mlsubst_union.
  - f_equal.
    unfold lstore_lift_free.
    symmetry.
    change (storeA_map_key LVFree (σ1 ∪ σ2) =
      (storeA_map_key LVFree σ1 : gmap logic_var V) ∪
      storeA_map_key LVFree σ2).
    apply storeA_map_key_union.
    intros a b Hab. inversion Hab. reflexivity.
  - unfold storeA_compat, map_compat in *.
    intros v a b Hv1 Hv2.
    destruct v as [k | x].
    + rewrite lstore_lift_free_lookup_bound in Hv1. discriminate.
    + rewrite !lstore_lift_free_lookup_free in Hv1, Hv2.
      eapply Hcompat; eauto.
Qed.


Lemma formula_msubst_store_empty (σ : Store (V := V)) (φ : Formula) :
  dom (σ : gmap atom V) = ∅ ->
  formula_msubst_store σ φ = φ.
Proof.
  intros Hdom.
  assert (Hσ : (σ : gmap atom V) = ∅).
  {
    apply (map_eq (M:=gmap atom)). intros x.
    apply not_elem_of_dom.
    rewrite Hdom. set_solver.
  }
  rewrite Hσ.
  unfold formula_msubst_store, lstore_lift_free.
  rewrite kmap_empty.
  induction φ; cbn [formula_mlsubst];
    try (rewrite ?IHφ1, ?IHφ2, ?IHφ; reflexivity).
  - rewrite lqual_mlsubst_empty. reflexivity.
  - rewrite dom_empty_L, difference_empty_L, IHφ. reflexivity.
Qed.

Lemma formula_msubst_store_fresh (σ : Store (V := V)) (φ : Formula) :
  dom (σ : gmap atom V) ## formula_fv φ ->
  formula_msubst_store σ φ = φ.
Proof.
  induction φ; intros Hfresh;
    unfold formula_msubst_store; cbn [formula_mlsubst];
    try reflexivity.
  - change (FAtom (lqual_msubst_store σ a) = FAtom a).
    f_equal. apply lqual_msubst_store_fresh.
    rewrite formula_fv_atom in Hfresh. exact Hfresh.
  - fold (formula_msubst_store σ φ1).
    fold (formula_msubst_store σ φ2).
    rewrite IHφ1, IHφ2; [reflexivity| |].
    + rewrite formula_fv_and in Hfresh. set_solver.
    + rewrite formula_fv_and in Hfresh. set_solver.
  - fold (formula_msubst_store σ φ1).
    fold (formula_msubst_store σ φ2).
    rewrite IHφ1, IHφ2; [reflexivity| |].
    + rewrite formula_fv_or in Hfresh. set_solver.
    + rewrite formula_fv_or in Hfresh. set_solver.
  - fold (formula_msubst_store σ φ1).
    fold (formula_msubst_store σ φ2).
    rewrite IHφ1, IHφ2; [reflexivity| |].
    + rewrite formula_fv_impl in Hfresh. set_solver.
    + rewrite formula_fv_impl in Hfresh. set_solver.
  - fold (formula_msubst_store σ φ1).
    fold (formula_msubst_store σ φ2).
    rewrite IHφ1, IHφ2; [reflexivity| |].
    + rewrite formula_fv_star in Hfresh. set_solver.
    + rewrite formula_fv_star in Hfresh. set_solver.
  - fold (formula_msubst_store σ φ1).
    fold (formula_msubst_store σ φ2).
    rewrite IHφ1, IHφ2; [reflexivity| |].
    + rewrite formula_fv_wand in Hfresh. set_solver.
    + rewrite formula_fv_wand in Hfresh. set_solver.
  - fold (formula_msubst_store σ φ1).
    fold (formula_msubst_store σ φ2).
    rewrite IHφ1, IHφ2; [reflexivity| |].
    + rewrite formula_fv_plus in Hfresh. set_solver.
    + rewrite formula_fv_plus in Hfresh. set_solver.
  - fold (formula_msubst_store σ φ).
    rewrite IHφ; [reflexivity|].
    rewrite formula_fv_forall in Hfresh. exact Hfresh.
  - fold (formula_msubst_store σ φ).
    rewrite IHφ; [reflexivity|].
    rewrite formula_fv_over in Hfresh. exact Hfresh.
  - fold (formula_msubst_store σ φ).
    rewrite IHφ; [reflexivity|].
    rewrite formula_fv_under in Hfresh. exact Hfresh.
  - fold (formula_msubst_store σ φ).
    rewrite IHφ.
    + f_equal.
      apply set_eq. intros v.
      rewrite elem_of_difference.
      split.
      * intros [Hv _]. exact Hv.
      * intros HvD. split; [exact HvD|].
        destruct v as [k|x].
        -- intros Hbad.
           rewrite dom_lstore_lift_free in Hbad.
           unfold lvars_of_atoms in Hbad.
           apply elem_of_map in Hbad as [a [Hbad _]].
           discriminate.
        -- intros Hbad.
           rewrite dom_lstore_lift_free in Hbad.
           unfold lvars_of_atoms in Hbad.
           apply elem_of_map in Hbad as [a [Hax Ha]].
           inversion Hax; subst.
           rewrite formula_fv_fibvars in Hfresh.
           apply elem_of_disjoint in Hfresh.
           apply (Hfresh a Ha).
           apply elem_of_union_l. apply lvars_fv_elem. exact HvD.
    + rewrite formula_fv_fibvars in Hfresh. set_solver.
Qed.

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
  - destruct a as [D P]. cbn [lqual_mlsubst lqual_lvars] in *.
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

Lemma formula_mlsubst_lvars_restore ρ φ :
  formula_lvars φ ⊆ formula_lvars (formula_mlsubst ρ φ) ∪ dom ρ.
Proof.
  induction φ; cbn [formula_lvars formula_mlsubst].
  - set_solver.
  - set_solver.
  - destruct a as [D P]. cbn [lqual_mlsubst].
    change (D ⊆ (D ∖ dom (ρ : gmap logic_var V)) ∪ dom ρ).
    intros v Hv.
    destruct (decide (v ∈ dom (ρ : gmap logic_var V))); set_solver.
  - intros v Hv. apply elem_of_union in Hv as [Hv | Hv].
    + pose proof (IHφ1 v Hv). set_solver.
    + pose proof (IHφ2 v Hv). set_solver.
  - intros v Hv. apply elem_of_union in Hv as [Hv | Hv].
    + pose proof (IHφ1 v Hv). set_solver.
    + pose proof (IHφ2 v Hv). set_solver.
  - intros v Hv. apply elem_of_union in Hv as [Hv | Hv].
    + pose proof (IHφ1 v Hv). set_solver.
    + pose proof (IHφ2 v Hv). set_solver.
  - intros v Hv. apply elem_of_union in Hv as [Hv | Hv].
    + pose proof (IHφ1 v Hv). set_solver.
    + pose proof (IHφ2 v Hv). set_solver.
  - intros v Hv. apply elem_of_union in Hv as [Hv | Hv].
    + pose proof (IHφ1 v Hv). set_solver.
    + pose proof (IHφ2 v Hv). set_solver.
  - intros v Hv. apply elem_of_union in Hv as [Hv | Hv].
    + pose proof (IHφ1 v Hv). set_solver.
    + pose proof (IHφ2 v Hv). set_solver.
  - exact IHφ.
  - exact IHφ.
  - exact IHφ.
  - intros v Hv. apply elem_of_union in Hv as [Hv | Hv].
    + destruct (decide (v ∈ dom (ρ : gmap logic_var V))); set_solver.
    + pose proof (IHφ v Hv). set_solver.
Qed.

Lemma formula_mlsubst_fv_restore ρ φ :
  formula_fv φ ⊆ formula_fv (formula_mlsubst ρ φ) ∪ lvars_fv (dom ρ).
Proof.
  unfold formula_fv.
  pose proof (lvars_fv_mono (formula_lvars φ)
    (formula_lvars (formula_mlsubst ρ φ) ∪ dom ρ)
    (formula_mlsubst_lvars_restore ρ φ)) as Hfv.
  rewrite lvars_fv_union in Hfv. exact Hfv.
Qed.

Lemma formula_msubst_store_fv_restore σ φ :
  formula_fv φ ⊆ formula_fv (formula_msubst_store σ φ) ∪ dom (σ : Store (V := V)).
Proof.
  unfold formula_msubst_store.
  pose proof (formula_mlsubst_fv_restore (lstore_lift_free σ) φ) as Hrestore.
  rewrite dom_lstore_lift_free, lvars_fv_of_atoms in Hrestore.
  exact Hrestore.
Qed.

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

Lemma formula_open_msubst_store_fresh k y
    (σ : Store (V := V)) (φ : Formula) :
  y ∉ dom (σ : gmap atom V) ->
  formula_open k y (formula_msubst_store σ φ) =
  formula_msubst_store σ (formula_open k y φ).
Proof.
  intros Hy.
  induction φ in k |- *; cbn [formula_open formula_msubst_store formula_mlsubst];
    repeat match goal with
    | |- context[formula_mlsubst (lstore_lift_free ?σ0) ?p] =>
        change (formula_mlsubst (lstore_lift_free σ0) p)
          with (formula_msubst_store σ0 p)
    end;
    try reflexivity.
  - change (FAtom (lqual_open k y (lqual_msubst_store σ a)) =
      FAtom (lqual_msubst_store σ (lqual_open k y a))).
    rewrite lqual_open_msubst_store_fresh by exact Hy. reflexivity.
  - rewrite IHφ1 by exact Hy. rewrite IHφ2 by exact Hy. reflexivity.
  - rewrite IHφ1 by exact Hy. rewrite IHφ2 by exact Hy. reflexivity.
  - rewrite IHφ1 by exact Hy. rewrite IHφ2 by exact Hy. reflexivity.
  - rewrite IHφ1 by exact Hy. rewrite IHφ2 by exact Hy. reflexivity.
  - rewrite IHφ1 by exact Hy. rewrite IHφ2 by exact Hy. reflexivity.
  - rewrite IHφ1 by exact Hy. rewrite IHφ2 by exact Hy. reflexivity.
  - rewrite IHφ by exact Hy. reflexivity.
  - rewrite IHφ by exact Hy. reflexivity.
  - rewrite IHφ by exact Hy. reflexivity.
  - rewrite IHφ by exact Hy.
    f_equal.
    apply set_eq. intros z.
    rewrite elem_of_difference, !set_swap_elem, elem_of_difference.
    assert (Hbound : LVBound k ∉ dom (lstore_lift_free σ : LStoreT)).
    {
      rewrite dom_lstore_lift_free.
      intros Hbad.
      unfold lvars_of_atoms in Hbad.
      apply elem_of_map in Hbad as [a [Hbad _]].
      discriminate.
    }
    assert (Hfree : LVFree y ∉ dom (lstore_lift_free σ : LStoreT)).
    {
      rewrite dom_lstore_lift_free.
      intros Hbad.
      unfold lvars_of_atoms in Hbad.
      apply elem_of_map in Hbad as [a [Hyx Ha]].
      inversion Hyx; subst. exact (Hy Ha).
    }
    unfold swap.
    repeat destruct decide; subst; better_set_solver.
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

Ltac formula_msubst_syntax_norm_once :=
  match goal with
  | |- context[formula_msubst_store ?σ FTrue] =>
      change (formula_msubst_store σ FTrue) with FTrue
  | |- context[formula_msubst_store ?σ FFalse] =>
      change (formula_msubst_store σ FFalse) with FFalse
  | |- context[formula_msubst_store ?σ (FAtom ?q)] =>
      change (formula_msubst_store σ (FAtom q))
        with (FAtom (lqual_msubst_store σ q))
  | |- context[formula_msubst_store ?σ (FAnd ?p ?q)] =>
      change (formula_msubst_store σ (FAnd p q))
        with (FAnd (formula_msubst_store σ p) (formula_msubst_store σ q))
  | |- context[formula_msubst_store ?σ (FOr ?p ?q)] =>
      change (formula_msubst_store σ (FOr p q))
        with (FOr (formula_msubst_store σ p) (formula_msubst_store σ q))
  | |- context[formula_msubst_store ?σ (FImpl ?p ?q)] =>
      change (formula_msubst_store σ (FImpl p q))
        with (FImpl (formula_msubst_store σ p) (formula_msubst_store σ q))
  | |- context[formula_msubst_store ?σ (FStar ?p ?q)] =>
      change (formula_msubst_store σ (FStar p q))
        with (FStar (formula_msubst_store σ p) (formula_msubst_store σ q))
  | |- context[formula_msubst_store ?σ (FWand ?p ?q)] =>
      change (formula_msubst_store σ (FWand p q))
        with (FWand (formula_msubst_store σ p) (formula_msubst_store σ q))
  | |- context[formula_msubst_store ?σ (FPlus ?p ?q)] =>
      change (formula_msubst_store σ (FPlus p q))
        with (FPlus (formula_msubst_store σ p) (formula_msubst_store σ q))
  | |- context[formula_msubst_store ?σ (FForall ?p)] =>
      change (formula_msubst_store σ (FForall p))
        with (FForall (formula_msubst_store σ p))
  | |- context[formula_msubst_store ?σ (FOver ?p)] =>
      change (formula_msubst_store σ (FOver p))
        with (FOver (formula_msubst_store σ p))
  | |- context[formula_msubst_store ?σ (FUnder ?p)] =>
      change (formula_msubst_store σ (FUnder p))
        with (FUnder (formula_msubst_store σ p))
  | |- context[formula_msubst_store ?σ (FFibVars ?D ?p)] =>
      rewrite (formula_msubst_store_fibvars σ D p)
  end.

Ltac formula_msubst_syntax_norm_once_in H :=
  match type of H with
  | context[formula_msubst_store ?σ FTrue] =>
      change (formula_msubst_store σ FTrue) with FTrue in H
  | context[formula_msubst_store ?σ FFalse] =>
      change (formula_msubst_store σ FFalse) with FFalse in H
  | context[formula_msubst_store ?σ (FAtom ?q)] =>
      change (formula_msubst_store σ (FAtom q))
        with (FAtom (lqual_msubst_store σ q)) in H
  | context[formula_msubst_store ?σ (FAnd ?p ?q)] =>
      change (formula_msubst_store σ (FAnd p q))
        with (FAnd (formula_msubst_store σ p) (formula_msubst_store σ q)) in H
  | context[formula_msubst_store ?σ (FOr ?p ?q)] =>
      change (formula_msubst_store σ (FOr p q))
        with (FOr (formula_msubst_store σ p) (formula_msubst_store σ q)) in H
  | context[formula_msubst_store ?σ (FImpl ?p ?q)] =>
      change (formula_msubst_store σ (FImpl p q))
        with (FImpl (formula_msubst_store σ p) (formula_msubst_store σ q)) in H
  | context[formula_msubst_store ?σ (FStar ?p ?q)] =>
      change (formula_msubst_store σ (FStar p q))
        with (FStar (formula_msubst_store σ p) (formula_msubst_store σ q)) in H
  | context[formula_msubst_store ?σ (FWand ?p ?q)] =>
      change (formula_msubst_store σ (FWand p q))
        with (FWand (formula_msubst_store σ p) (formula_msubst_store σ q)) in H
  | context[formula_msubst_store ?σ (FPlus ?p ?q)] =>
      change (formula_msubst_store σ (FPlus p q))
        with (FPlus (formula_msubst_store σ p) (formula_msubst_store σ q)) in H
  | context[formula_msubst_store ?σ (FForall ?p)] =>
      change (formula_msubst_store σ (FForall p))
        with (FForall (formula_msubst_store σ p)) in H
  | context[formula_msubst_store ?σ (FOver ?p)] =>
      change (formula_msubst_store σ (FOver p))
        with (FOver (formula_msubst_store σ p)) in H
  | context[formula_msubst_store ?σ (FUnder ?p)] =>
      change (formula_msubst_store σ (FUnder p))
        with (FUnder (formula_msubst_store σ p)) in H
  | context[formula_msubst_store ?σ (FFibVars ?D ?p)] =>
      rewrite (formula_msubst_store_fibvars σ D p) in H
  end.

Ltac formula_msubst_syntax_norm :=
  repeat formula_msubst_syntax_norm_once.

Ltac formula_msubst_syntax_norm_in H :=
  repeat formula_msubst_syntax_norm_once_in H.

Ltac formula_syntax_norm :=
  formula_fv_syntax_norm;
  formula_open_syntax_norm;
  formula_open_env_syntax_norm;
  formula_msubst_syntax_norm.

Ltac formula_syntax_norm_in H :=
  formula_fv_syntax_norm_in H;
  formula_open_syntax_norm_in H;
  formula_open_env_syntax_norm_in H;
  formula_msubst_syntax_norm_in H.
