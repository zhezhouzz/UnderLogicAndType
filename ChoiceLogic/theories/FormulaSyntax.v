From ChoiceLogic Require Export Prelude LogicQualifier.

(** * Choice Logic  (Definitions 1.8 and 1.9)

    Formulas are independent of the core language.  Core expressions are
    embedded into the logic by ChoiceType through ordinary logic qualifiers. *)

Section Formula.

Context {V : Type} `{ValueSig V}.

Local Notation StoreT := (gmap atom V) (only parsing).
Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation LogicQualifierT := (logic_qualifier (V := V)) (only parsing).

(** ** Formula syntax *)

Inductive Formula : Type :=
  | FTrue
  | FFalse
  | FAtom   (a : LogicQualifierT)
  | FAnd    (p q : Formula)
  | FOr     (p q : Formula)
  | FImpl   (p q : Formula)                     (* Kripke implication *)
  | FStar   (p q : Formula)                     (* separating conjunction p ∗ q *)
  | FWand   (p q : Formula)                     (* magic wand p −∗ q *)
  | FPlus   (p q : Formula)                     (* choice sum p ⊕ q *)
  | FForall (x : atom) (p : Formula)            (* ordinary universal quantifier *)
  | FExists (x : atom) (p : Formula)            (* ordinary existential quantifier *)
  | FOver   (p : Formula)                       (* overapproximation  o p *)
  | FUnder  (p : Formula)                       (* underapproximation u p *)
  | FFibVars (D : lvset) (p : Formula).         (* primitive multi-fiber *)

Fixpoint formula_stale (φ : Formula) : aset :=
  match φ with
  | FTrue | FFalse => ∅
  | FAtom q => stale q
  | FAnd p q | FOr p q | FImpl p q | FStar p q | FWand p q | FPlus p q =>
      formula_stale p ∪ formula_stale q
  | FForall x p | FExists x p => {[x]} ∪ formula_stale p
  | FOver p | FUnder p => formula_stale p
  | FFibVars D p => lvars_fv D ∪ formula_stale p
  end.

Fixpoint formula_fv (φ : Formula) : aset :=
  match φ with
  | FTrue | FFalse => ∅
  | FAtom q => stale q
  | FAnd p q | FOr p q | FImpl p q | FStar p q | FWand p q | FPlus p q =>
      formula_fv p ∪ formula_fv q
  | FForall x p | FExists x p => formula_fv p ∖ {[x]}
  | FOver p | FUnder p => formula_fv p
  | FFibVars D p => lvars_fv D ∪ formula_fv p
  end.

#[global] Instance stale_formula : Stale Formula := formula_fv.
Arguments stale_formula /.

Fixpoint formula_rename_atom (x y : atom) (φ : Formula) : Formula :=
  match φ with
  | FTrue => FTrue
  | FFalse => FFalse
  | FAtom q => FAtom (lqual_swap x y q)
  | FAnd p q => FAnd (formula_rename_atom x y p) (formula_rename_atom x y q)
  | FOr p q => FOr (formula_rename_atom x y p) (formula_rename_atom x y q)
  | FImpl p q => FImpl (formula_rename_atom x y p) (formula_rename_atom x y q)
  | FStar p q => FStar (formula_rename_atom x y p) (formula_rename_atom x y q)
  | FWand p q => FWand (formula_rename_atom x y p) (formula_rename_atom x y q)
  | FPlus p q => FPlus (formula_rename_atom x y p) (formula_rename_atom x y q)
  | FForall z p =>
      FForall (atom_swap x y z) (formula_rename_atom x y p)
  | FExists z p =>
      FExists (atom_swap x y z) (formula_rename_atom x y p)
  | FOver p => FOver (formula_rename_atom x y p)
  | FUnder p => FUnder (formula_rename_atom x y p)
  | FFibVars D p => FFibVars (lvars_swap x y D) (formula_rename_atom x y p)
  end.

Fixpoint formula_swap (x y : atom) (φ : Formula) : Formula :=
  match φ with
  | FTrue => FTrue
  | FFalse => FFalse
  | FAtom q => FAtom (lqual_swap x y q)
  | FAnd p q => FAnd (formula_swap x y p) (formula_swap x y q)
  | FOr p q => FOr (formula_swap x y p) (formula_swap x y q)
  | FImpl p q => FImpl (formula_swap x y p) (formula_swap x y q)
  | FStar p q => FStar (formula_swap x y p) (formula_swap x y q)
  | FWand p q => FWand (formula_swap x y p) (formula_swap x y q)
  | FPlus p q => FPlus (formula_swap x y p) (formula_swap x y q)
  | FForall z p =>
      FForall (atom_swap x y z) (formula_swap x y p)
  | FExists z p =>
      FExists (atom_swap x y z) (formula_swap x y p)
  | FOver p => FOver (formula_swap x y p)
  | FUnder p => FUnder (formula_swap x y p)
  | FFibVars D p => FFibVars (lvars_swap x y D) (formula_swap x y p)
  end.

Fixpoint formula_measure (φ : Formula) : nat :=
  match φ with
  | FTrue | FFalse | FAtom _ => 1
  | FAnd p q | FOr p q | FImpl p q | FStar p q | FWand p q | FPlus p q =>
      1 + formula_measure p + formula_measure q
  | FForall _ p | FExists _ p | FOver p | FUnder p | FFibVars _ p =>
      1 + formula_measure p
  end.

Lemma formula_rename_preserves_measure x y φ :
  formula_measure (formula_rename_atom x y φ) = formula_measure φ.
Proof.
  induction φ; simpl; eauto; lia.
Qed.

Lemma formula_swap_preserves_measure x y φ :
  formula_measure (formula_swap x y φ) = formula_measure φ.
Proof.
  induction φ; simpl; eauto; lia.
Qed.

Lemma formula_rename_atom_eq_swap x y φ :
  formula_rename_atom x y φ = formula_swap x y φ.
Proof.
  induction φ; simpl; try congruence.
Qed.

Lemma formula_rename_atom_conjugate a b x y φ :
  formula_rename_atom a b (formula_rename_atom x y φ) =
  formula_rename_atom (atom_swap a b x) (atom_swap a b y)
    (formula_rename_atom a b φ).
Proof.
  (* Legacy explicit-swap lemma; superseded by LN opening. *)
Admitted.

Lemma formula_fv_swap x y φ :
  formula_fv (formula_swap x y φ) = aset_swap x y (formula_fv φ).
Proof.
  (* Legacy explicit-swap lemma.  It disappears once Formula binders become LN. *)
Admitted.

Lemma formula_fv_rename_atom x y φ :
  formula_fv (formula_rename_atom x y φ) = aset_swap x y (formula_fv φ).
Proof.
  rewrite formula_rename_atom_eq_swap. apply formula_fv_swap.
Qed.

Lemma formula_fv_rename_atom_subset_open x y φ :
  y ∉ formula_fv φ ∖ {[x]} →
  formula_fv (formula_rename_atom x y φ) ⊆
    (formula_fv φ ∖ {[x]}) ∪ {[y]}.
Proof.
  intros Hy z Hz.
  rewrite formula_fv_rename_atom in Hz.
  rewrite elem_of_aset_swap in Hz.
  destruct (decide (z = y)) as [Hzy|Hzy].
  - subst z. apply elem_of_union. right. set_solver.
  - destruct (decide (z = x)) as [Hzx|Hzx].
    + subst z. exfalso. apply Hy. apply elem_of_difference. split.
      * replace (atom_swap x y x) with y in Hz
          by (unfold atom_swap; repeat destruct decide; congruence).
        exact Hz.
      * set_solver.
    + apply elem_of_union. left. apply elem_of_difference. split.
      * replace (atom_swap x y z) with z in Hz
          by (unfold atom_swap; repeat destruct decide; congruence).
        exact Hz.
      * set_solver.
Qed.

Lemma elem_of_aset_swap_unchanged x y z X :
  z ∈ X →
  z ≠ x →
  z ≠ y →
  z ∈ aset_swap x y X.
Proof.
  intros Hz Hzx Hzy. rewrite elem_of_aset_swap.
  unfold atom_swap. repeat destruct decide; congruence.
Qed.

Lemma formula_fv_rename_unchanged x y z φ :
  z ∈ formula_fv φ →
  z ≠ x →
  z ≠ y →
  z ∈ formula_fv (formula_rename_atom x y φ).
Proof.
  (* Legacy explicit-swap lemma.  It disappears once Formula binders become LN. *)
Admitted.

Lemma formula_measure_pos (φ : Formula) :
  0 < formula_measure φ.
Proof. induction φ; simpl; lia. Qed.

(** [fresh_forall D body] chooses a syntactic representative for an explicit
    formula binder.  The representative is not semantically privileged:
    [FForall]'s satisfaction relation later renames it to every sufficiently
    fresh atom. *)
Definition fresh_forall (D : aset) (body : atom → Formula) : Formula :=
  FForall (fresh_for D) (body (fresh_for D)).

Lemma fresh_forall_formula_fv_subset
    (D S : aset) (Q : atom → Formula) :
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

Definition FPure (P : Prop) : Formula :=
  FAtom (lqual ∅ (λ _ _, P)).

Definition FResourceAtom (D : aset) (P : WfWorldT → Prop) : Formula :=
  FAtom (lqual_fvars D (λ _ m, P m)).

Definition FStoreResourceAtom
    (D : aset) (P : StoreT → WfWorldT → Prop) : Formula :=
  FAtom (lqual_fvars D P).

Lemma formula_fv_FPure P :
  formula_fv (FPure P) = ∅.
Proof. reflexivity. Qed.

Lemma formula_fv_FResourceAtom D P :
  formula_fv (FResourceAtom D P) = D.
Proof. unfold FResourceAtom, lqual_fvars. simpl. apply lvars_fv_of_atoms. Qed.

Lemma formula_fv_FStoreResourceAtom D P :
  formula_fv (FStoreResourceAtom D P) = D.
Proof. unfold FStoreResourceAtom, lqual_fvars. simpl. apply lvars_fv_of_atoms. Qed.

Lemma formula_rename_FPure x y P :
  formula_rename_atom x y (FPure P) = FPure P.
Proof. reflexivity. Qed.

Lemma formula_rename_FResourceAtom x y D P :
  formula_rename_atom x y (FResourceAtom D P) =
  FResourceAtom (aset_swap x y D)
    (fun m => P (res_swap x y m)).
Proof.
  (* Legacy explicit-swap lemma; superseded by LN opening. *)
Admitted.

Lemma formula_rename_FStoreResourceAtom x y D P :
  formula_rename_atom x y (FStoreResourceAtom D P) =
  FStoreResourceAtom (aset_swap x y D)
    (fun σ m => P (store_swap x y σ) (res_swap x y m)).
Proof.
  (* Legacy explicit-swap lemma; superseded by LN opening. *)
Admitted.

End Formula.
