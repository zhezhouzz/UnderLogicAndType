From ContextLogic Require Export FormulaAtom.
From CoreLang Require Import Prelude.
From ContextBase Require Import BaseTactics LogicVarOpenEnv LogicVarShift.
From Stdlib Require Import Logic.FunctionalExtensionality Logic.PropExtensionality.

(** * Context Logic syntax

    Formulas track lvar support first; atom free variables are the projection
    [lvars_fv].  Exists is intentionally absent in this phase because the type
    denotation path does not need it yet. *)

Section Formula.

Context {V : Type} `{ValueSig V}.

Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation QualifierT := (qualifier (V := V)) (only parsing).
Local Notation LStoreT := (gmap logic_var V) (only parsing).

Inductive Formula : Type :=
  | FTrue
  | FFalse
  | FAtom    (a : QualifierT)
  | FAnd     (p q : Formula)
  | FOr      (p q : Formula)
  | FImpl    (p q : Formula)
  | FStar    (p q : Formula)
  | FBWand   (d : nat) (p q : Formula)
  | FPlus    (p q : Formula)
  | FForall  (p : Formula)
  | FOver    (p : Formula)
  | FUnder   (p : Formula)
  | FPersist (p : Formula)
  | FFibVars (D : lvset) (p : Formula).

Fixpoint formula_lvars_at (d : nat) (φ : Formula) : lvset :=
  match φ with
  | FTrue | FFalse => ∅
  | FAtom q => lvars_at_depth d (qual_vars q)
  | FAnd p q | FOr p q | FImpl p q
  | FStar p q | FPlus p q =>
      formula_lvars_at d p ∪ formula_lvars_at d q
  | FBWand n p q =>
      formula_lvars_at (d + n) p ∪ formula_lvars_at (d + n) q
  | FForall p => formula_lvars_at (S d) p
  | FOver p | FUnder p | FPersist p => formula_lvars_at d p
  | FFibVars D p => lvars_at_depth d D ∪ formula_lvars_at d p
  end.

Definition formula_lvars (φ : Formula) : lvset :=
  formula_lvars_at 0 φ.

Definition formula_fv (φ : Formula) : aset :=
  lvars_fv (formula_lvars φ).

Fixpoint formula_wf (φ : Formula) : Prop :=
  match φ with
  | FTrue | FFalse | FAtom _ => True
  | FAnd p q | FOr p q | FImpl p q
  | FStar p q | FPlus p q =>
      formula_wf p ∧ formula_wf q
  | FBWand d p q =>
      formula_wf p ∧
      formula_wf q ∧
      lvars_fv (formula_lvars_at d p) ⊆
        lvars_fv (formula_lvars_at 0 q)
  | FForall p | FOver p | FUnder p | FPersist p => formula_wf p
  | FFibVars _ p => formula_wf p
  end.

Definition formula_stale : Formula → aset := formula_fv.

#[global] Instance stale_formula : Stale Formula := formula_fv.
Arguments stale_formula /.


(** Syntax measures, substitution, fiber atoms, open and swap operations. *)
Fixpoint formula_measure (φ : Formula) : nat :=
  match φ with
  | FTrue | FFalse | FAtom _ => 1
  | FAnd p q | FOr p q | FImpl p q | FStar p q | FPlus p q
  | FBWand _ p q =>
      1 + formula_measure p + formula_measure q
  | FForall p | FOver p | FUnder p | FPersist p | FFibVars _ p =>
      1 + formula_measure p
  end.

Fixpoint formula_mlsubst (ρ : LStoreT) (φ : Formula) : Formula :=
  match φ with
  | FTrue => FTrue
  | FFalse => FFalse
  | FAtom q => FAtom (qual_mlsubst ρ q)
  | FAnd p q => FAnd (formula_mlsubst ρ p) (formula_mlsubst ρ q)
  | FOr p q => FOr (formula_mlsubst ρ p) (formula_mlsubst ρ q)
  | FImpl p q => FImpl (formula_mlsubst ρ p) (formula_mlsubst ρ q)
  | FStar p q => FStar (formula_mlsubst ρ p) (formula_mlsubst ρ q)
  | FBWand d p q => FBWand d (formula_mlsubst ρ p) (formula_mlsubst ρ q)
  | FPlus p q => FPlus (formula_mlsubst ρ p) (formula_mlsubst ρ q)
  | FForall p => FForall (formula_mlsubst ρ p)
  | FOver p => FOver (formula_mlsubst ρ p)
  | FUnder p => FUnder (formula_mlsubst ρ p)
  | FPersist p => FPersist (formula_mlsubst ρ p)
  | FFibVars D p =>
      FFibVars (D ∖ dom (ρ : gmap logic_var V)) (formula_mlsubst ρ p)
  end.

Definition formula_msubst_store (σ : Store (V := V)) (φ : Formula) : Formula :=
  formula_mlsubst (lstore_lift_free σ) φ.

Definition FFiberAtom (q : qualifier (V := V)) : Formula :=
  FFibVars (qual_vars q) (FAtom q).

Definition store_without_lvars (σ : Store (V := V)) (D : lvset) : Store (V := V) :=
  store_restrict σ (dom (σ : Store (V := V)) ∖ lvars_fv D).


Fixpoint formula_open (k : nat) (x : atom) (φ : Formula) : Formula :=
  match φ with
  | FTrue => FTrue
  | FFalse => FFalse
  | FAtom q => FAtom (qual_open_atom k x q)
  | FAnd p q => FAnd (formula_open k x p) (formula_open k x q)
  | FOr p q => FOr (formula_open k x p) (formula_open k x q)
  | FImpl p q => FImpl (formula_open k x p) (formula_open k x q)
  | FStar p q => FStar (formula_open k x p) (formula_open k x q)
  | FBWand d p q => FBWand d (formula_open (k + d) x p) (formula_open (k + d) x q)
  | FPlus p q => FPlus (formula_open k x p) (formula_open k x q)
  | FForall p => FForall (formula_open (S k) x p)
  | FOver p => FOver (formula_open k x p)
  | FUnder p => FUnder (formula_open k x p)
  | FPersist p => FPersist (formula_open k x p)
  | FFibVars D p => FFibVars (lvars_open k x D) (formula_open k x p)
  end.

#[global] Instance formula_open_atom_inst : Open atom Formula := formula_open.
Arguments formula_open_atom_inst /.

Fixpoint formula_atom_swap (x y : atom) (φ : Formula) : Formula :=
  match φ with
  | FTrue => FTrue
  | FFalse => FFalse
  | FAtom q => FAtom (qual_atom_swap x y q)
  | FAnd p q => FAnd (formula_atom_swap x y p) (formula_atom_swap x y q)
  | FOr p q => FOr (formula_atom_swap x y p) (formula_atom_swap x y q)
  | FImpl p q => FImpl (formula_atom_swap x y p) (formula_atom_swap x y q)
  | FStar p q => FStar (formula_atom_swap x y p) (formula_atom_swap x y q)
  | FBWand d p q => FBWand d (formula_atom_swap x y p) (formula_atom_swap x y q)
  | FPlus p q => FPlus (formula_atom_swap x y p) (formula_atom_swap x y q)
  | FForall p => FForall (formula_atom_swap x y p)
  | FOver p => FOver (formula_atom_swap x y p)
  | FUnder p => FUnder (formula_atom_swap x y p)
  | FPersist p => FPersist (formula_atom_swap x y p)
  | FFibVars D p => FFibVars (lvars_swap x y D) (formula_atom_swap x y p)
  end.


Definition formula_open_env (η : gmap nat atom) (φ : Formula) : Formula :=
  map_fold (fun k x acc => formula_open k x acc) φ η.


Definition FPure (P : Prop) : Formula :=
  FAtom (tqual ∅ (λ _, P)).


End Formula.
