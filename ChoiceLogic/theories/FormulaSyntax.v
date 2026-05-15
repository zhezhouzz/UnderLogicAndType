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
  | FForall (p : Formula)                       (* locally nameless universal quantifier *)
  | FExists (p : Formula)                       (* locally nameless existential quantifier *)
  | FOver   (p : Formula)                       (* overapproximation  o p *)
  | FUnder  (p : Formula)                       (* underapproximation u p *)
  | FFibVars (D : lvset) (p : Formula).         (* primitive multi-fiber *)

Fixpoint formula_stale (φ : Formula) : aset :=
  match φ with
  | FTrue | FFalse => ∅
  | FAtom q => stale q
  | FAnd p q | FOr p q | FImpl p q | FStar p q | FWand p q | FPlus p q =>
      formula_stale p ∪ formula_stale q
  | FForall p | FExists p => formula_stale p
  | FOver p | FUnder p => formula_stale p
  | FFibVars D p => lvars_fv D ∪ formula_stale p
  end.

Fixpoint formula_fv (φ : Formula) : aset :=
  match φ with
  | FTrue | FFalse => ∅
  | FAtom q => stale q
  | FAnd p q | FOr p q | FImpl p q | FStar p q | FWand p q | FPlus p q =>
      formula_fv p ∪ formula_fv q
  | FForall p | FExists p => formula_fv p
  | FOver p | FUnder p => formula_fv p
  | FFibVars D p => lvars_fv D ∪ formula_fv p
  end.

#[global] Instance stale_formula : Stale Formula := formula_fv.
Arguments stale_formula /.

Fixpoint formula_measure (φ : Formula) : nat :=
  match φ with
  | FTrue | FFalse | FAtom _ => 1
  | FAnd p q | FOr p q | FImpl p q | FStar p q | FWand p q | FPlus p q =>
      1 + formula_measure p + formula_measure q
  | FForall p | FExists p | FOver p | FUnder p | FFibVars _ p =>
      1 + formula_measure p
  end.

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
  | FExists p => FExists (formula_open (S k) x p)
  | FOver p => FOver (formula_open k x p)
  | FUnder p => FUnder (formula_open k x p)
  | FFibVars D p => FFibVars (lvars_open k x D) (formula_open k x p)
  end.

Lemma formula_open_preserves_measure k x φ :
  formula_measure (formula_open k x φ) = formula_measure φ.
Proof.
  revert k.
  induction φ; intros k; simpl; eauto; lia.
Qed.

Lemma formula_open_fv_subset k x φ :
  formula_fv (formula_open k x φ) ⊆ formula_fv φ ∪ {[x]}.
Proof.
Admitted.

Lemma formula_measure_pos (φ : Formula) :
  0 < formula_measure φ.
Proof. induction φ; simpl; lia. Qed.

Definition FPure (P : Prop) : Formula :=
  FAtom (lqual ∅ (λ _ _ _, P)).

Definition FResourceAtom {A : Type} `{IntoLVars A}
    (D : A) (P : WfWorldT → Prop) : Formula :=
  FAtom (lqual (into_lvars D) (λ _ _ m, P m)).

Definition FResourceAtomVars (D : lvset) (P : WfWorldT → Prop) : Formula :=
  @FResourceAtom lvset _ D P.

Definition FStoreResourceAtom {A : Type} `{IntoLVars A}
    (D : A) (P : gmap nat atom → StoreT → WfWorldT → Prop) : Formula :=
  FAtom (lqual (into_lvars D) P).

Definition FStoreResourceAtomVars
    (D : lvset) (P : gmap nat atom → StoreT → WfWorldT → Prop) : Formula :=
  @FStoreResourceAtom lvset _ D P.

Lemma formula_fv_FPure P :
  formula_fv (FPure P) = ∅.
Proof. reflexivity. Qed.

Lemma formula_fv_FResourceAtom (D : aset) P :
  formula_fv (FResourceAtom D P) = D.
Proof. unfold FResourceAtom. simpl. apply lvars_fv_of_atoms. Qed.

Lemma formula_fv_FResourceAtomVars D P :
  formula_fv (FResourceAtomVars D P) = lvars_fv D.
Proof. reflexivity. Qed.

Lemma formula_fv_FStoreResourceAtom (D : aset) P :
  formula_fv (FStoreResourceAtom D P) = D.
Proof. unfold FStoreResourceAtom. simpl. apply lvars_fv_of_atoms. Qed.

Lemma formula_fv_FStoreResourceAtomVars D P :
  formula_fv (FStoreResourceAtomVars D P) = lvars_fv D.
Proof. reflexivity. Qed.

End Formula.
