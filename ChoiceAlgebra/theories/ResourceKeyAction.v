From ChoicePrelude Require Import Prelude Store.
From ChoiceAlgebra Require Import ResourceCore.

(** * Key actions lifted from stores to resources *)

Section ResourceKeyActionA.

Context {K : Type} `{Countable K} `{!SwapKey K}.
Context {V : Type} `{ValueSig V}.

Local Notation StoreAT := (@StoreA V K _ _) (only parsing).
Local Notation WorldAT := (@WorldA K _ _ V) (only parsing).
Local Notation WfWorldAT := (@WfWorldA K _ _ V) (only parsing).

Definition rawA_swap (x y : K) (m : WorldAT) : WorldAT := {|
  worldA_dom    := gset_swap x y (worldA_dom m);
  worldA_stores := λ σ, ∃ σ0 : StoreAT,
    m σ0 ∧ @storeA_swap V K _ _ _ x y σ0 = σ;
|}.

Definition resA_swap (x y : K) (w : WfWorldAT) : WfWorldAT.
Proof.
  refine (exist _ (rawA_swap x y w) _).
  destruct (worldA_wf w) as [Hne Hdom].
  split.
  - destruct Hne as [σ Hσ].
    exists (@storeA_swap V K _ _ _ x y σ). exists σ. split; [exact Hσ | reflexivity].
  - intros σ [σ0 [Hσ0 Hswap]]. subst σ.
    rewrite storeA_swap_dom.
    rewrite (Hdom σ0 Hσ0). reflexivity.
Defined.

Lemma resA_swap_involutive (x y : K) (w : WfWorldAT) :
  resA_swap x y (resA_swap x y w) = w.
Proof.
  apply wfworldA_ext. apply worldA_ext.
  - simpl. apply gset_swap_involutive.
  - intros σ. simpl. split.
    + intros [σ1 [[σ0 [Hσ0 Hswap0]] Hswap1]].
      subst σ1 σ. rewrite storeA_swap_involutive. exact Hσ0.
    + intros Hσ.
      exists (@storeA_swap V K _ _ _ x y σ). split.
      * exists σ. split; [exact Hσ | reflexivity].
      * apply storeA_swap_involutive.
Qed.

Lemma resA_swap_sym (x y : K) (w : WfWorldAT) :
  resA_swap x y w = resA_swap y x w.
Proof.
  apply wfworldA_ext. apply worldA_ext.
  - simpl. apply gset_swap_sym.
  - intros σ. simpl. split.
    + intros [σ0 [Hσ0 Hswap]]. exists σ0. split; [exact Hσ0 |].
      rewrite <- storeA_swap_sym. exact Hswap.
    + intros [σ0 [Hσ0 Hswap]]. exists σ0. split; [exact Hσ0 |].
      rewrite storeA_swap_sym. exact Hswap.
Qed.

Lemma resA_swap_conjugate a b x y (w : WfWorldAT) :
  resA_swap a b (resA_swap x y w) =
  resA_swap (key_swap a b x) (key_swap a b y) (resA_swap a b w).
Proof.
  apply wfworldA_ext. apply worldA_ext.
  - simpl. apply gset_swap_conjugate.
  - intros σ. simpl. split.
    + intros [σ0 [[σ1 [Hσ1 Hswap1]] Hswap0]]. subst σ0 σ.
      exists (@storeA_swap V K _ _ _ a b σ1). split.
      * exists σ1. split; [exact Hσ1 | reflexivity].
      * symmetry. apply storeA_swap_conjugate.
    + intros [σ0 [[σ1 [Hσ1 Hswap1]] Hswap0]]. subst σ0 σ.
      exists (@storeA_swap V K _ _ _ x y σ1). split.
      * exists σ1. split; [exact Hσ1 | reflexivity].
      * apply storeA_swap_conjugate.
Qed.

Lemma resA_swap_conjugate_inv a b x y (w : WfWorldAT) :
  resA_swap x y (resA_swap a b w) =
  resA_swap a b (resA_swap (key_swap a b x) (key_swap a b y) w).
Proof.
  apply wfworldA_ext. apply worldA_ext.
  - simpl. apply gset_swap_conjugate_inv.
  - intros σ. simpl. split.
    + intros [σ0 [[σ1 [Hσ1 Hswap1]] Hswap0]]. subst σ0 σ.
      exists (@storeA_swap V K _ _ _ (key_swap a b x) (key_swap a b y) σ1).
      split.
      * exists σ1. split; [exact Hσ1 | reflexivity].
      * symmetry. apply storeA_swap_conjugate_inv.
    + intros [σ0 [[σ1 [Hσ1 Hswap1]] Hswap0]]. subst σ0 σ.
      exists (@storeA_swap V K _ _ _ a b σ1). split.
      * exists σ1. split; [exact Hσ1 | reflexivity].
      * apply storeA_swap_conjugate_inv.
Qed.

Context `{!ShiftKey K}.

Definition rawA_shift (k : nat) (m : WorldAT) : WorldAT := {|
  worldA_dom    := set_map (key_shift k) (worldA_dom m);
  worldA_stores := λ σ, ∃ σ0 : StoreAT,
    m σ0 ∧ @storeA_shift V K _ _ _ k σ0 = σ;
|}.

Definition resA_shift (k : nat) (w : WfWorldAT) : WfWorldAT.
Proof.
  refine (exist _ (rawA_shift k w) _).
  destruct (worldA_wf w) as [Hne Hdom].
  split.
  - destruct Hne as [σ Hσ].
    exists (@storeA_shift V K _ _ _ k σ). exists σ. split; [exact Hσ | reflexivity].
  - intros σ [σ0 [Hσ0 Hshift]]. subst σ.
    rewrite storeA_shift_dom.
    rewrite (Hdom σ0 Hσ0). reflexivity.
Defined.

End ResourceKeyActionA.

Section ResourceOpenA.

Context {V : Type} `{ValueSig V}.

Definition rawA_open (k : nat) (x : atom)
    (m : @WorldA logic_var _ _ V) : @WorldA logic_var _ _ V :=
  @rawA_swap logic_var _ _ _ V (LVBound k) (LVFree x) m.

Definition resA_open (k : nat) (x : atom)
    (w : @WfWorldA logic_var _ _ V) : @WfWorldA logic_var _ _ V :=
  @resA_swap logic_var _ _ _ V (LVBound k) (LVFree x) w.

End ResourceOpenA.
