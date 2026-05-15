(** * CoreLang.Sugar

    Small derived forms used by examples.  The core syntax remains let-normal,
    with boolean-only matching.  The core language is deterministic; branching
    is ordinary boolean case analysis. *)

From CoreLang Require Export SmallStep OperationalProps LocallyNamelessProps.
From CoreLang Require Import BasicTypingProps.
From ChoicePrelude Require Import StoreBase.

Definition vtrue : value := vconst (cbool true).
Definition vfalse : value := vconst (cbool false).
Definition vnat (n : nat) : value := vconst (cnat n).

Fixpoint tapp_tm (ef : tm) (vx : value) : tm :=
  match ef with
  | tret vf => tapp vf vx
  | tlete e1 e2 => tlete e1 (tapp_tm e2 vx)
  | _ => tlete ef (tapp (vbvar 0) vx)
  end.

Lemma fv_tapp_tm ef vx :
  fv_tm (tapp_tm ef vx) = fv_tm ef ∪ fv_value vx.
Proof.
  induction ef; simpl; set_solver.
Qed.

Lemma tm_swap_atom_tapp_tm x y ef vx :
  tm_swap_atom x y (tapp_tm ef vx) =
  tapp_tm (tm_swap_atom x y ef) (value_swap_atom x y vx).
Proof.
  induction ef; simpl; try reflexivity.
  rewrite IHef2. reflexivity.
Qed.

Lemma tm_swap_atom_tapp_tm_fvar_fresh x y ef :
  x ∉ fv_tm ef →
  y ∉ fv_tm ef →
  tm_swap_atom x y (tapp_tm ef (vfvar x)) = tapp_tm ef (vfvar y).
Proof.
  intros Hx Hy.
  rewrite tm_swap_atom_tapp_tm.
  rewrite tm_swap_atom_fresh by assumption.
  simpl. replace (atom_swap x y x) with y
    by (unfold atom_swap; repeat destruct decide; congruence).
  reflexivity.
Qed.

Lemma open_tapp_tm_lc_arg ef vx k u :
  lc_value vx →
  open_tm k u (tapp_tm ef vx) = tapp_tm (open_tm k u ef) vx.
Proof.
  intros Hvx. revert k.
  induction ef; intros k; simpl;
    try rewrite (open_rec_lc_value vx Hvx k u);
    try rewrite (open_rec_lc_value vx Hvx (S k) u);
    try (destruct (decide (S k = 0)); [lia | reflexivity]);
    try reflexivity.
  rewrite IHef2.
  reflexivity.
Qed.

Lemma body_tapp_tm_body vx :
  lc_value vx →
  body_tm (tapp (vbvar 0) vx).
Proof.
  intros Hvx. exists ∅. intros x _.
  change (lc_tm (tapp (vfvar x) (open_value 0 (vfvar x) vx))).
  rewrite (open_rec_lc_value vx Hvx 0 (vfvar x)).
  repeat constructor. exact Hvx.
Qed.

Lemma lc_tapp_tm ef vx :
  lc_tm ef →
  lc_value vx →
  lc_tm (tapp_tm ef vx).
Proof.
  intros Hef. revert vx.
  induction Hef; intros vx Hvx; simpl.
  - repeat constructor; eauto.
  - eapply LC_lete; [exact Hef |].
    intros x Hx.
    rewrite open_tapp_tm_lc_arg by exact Hvx.
    eauto.
  - eapply LC_lete with (L := ∅); [constructor; exact H |].
    intros x _.
    change (lc_tm (tapp (vfvar x) (open_value 0 (vfvar x) vx))).
    rewrite (open_rec_lc_value vx Hvx 0 (vfvar x)).
    repeat constructor. exact Hvx.
  - eapply LC_lete with (L := ∅); [constructor; assumption |].
    intros x _.
    change (lc_tm (tapp (vfvar x) (open_value 0 (vfvar x) vx))).
    rewrite (open_rec_lc_value vx Hvx 0 (vfvar x)).
    repeat constructor. exact Hvx.
  - eapply LC_lete with (L := ∅); [constructor; assumption |].
    intros x _.
    change (lc_tm (tapp (vfvar x) (open_value 0 (vfvar x) vx))).
    rewrite (open_rec_lc_value vx Hvx 0 (vfvar x)).
    repeat constructor. exact Hvx.
Qed.

Lemma basic_typing_tapp_tm Γ ef vx Tx T :
  Γ ⊢ₑ ef ⋮ (Tx →ₜ T) →
  Γ ⊢ᵥ vx ⋮ Tx →
  Γ ⊢ₑ tapp_tm ef vx ⋮ T.
Proof.
  intros Hef Hvx. remember (Tx →ₜ T) as Tf eqn:HTf.
  revert Tx T vx Hvx HTf.
  induction Hef; intros Tx0 T0 vx Hvx HTf; subst; simpl.
  - eapply TT_App; eauto.
  - eapply TT_Let with (T1 := T1) (L := L ∪ fv_value vx ∪ dom Γ).
    + exact Hef.
    + intros x Hx.
      change (<[x:=T1]> Γ ⊢ₑ open_tm 0 (vfvar x) (tapp_tm e2 vx) ⋮ T0).
      rewrite open_tapp_tm_lc_arg by exact (typing_value_lc _ _ _ Hvx).
      refine (H0 x _ Tx0 T0 vx _ _).
      * set_solver.
      * eapply basic_typing_weaken_insert_value; [set_solver | exact Hvx].
      * reflexivity.
  - discriminate.
  - eapply TT_Let with (L := dom Γ ∪ fv_value vx).
    + eapply TT_App; eauto.
    + intros x Hx.
      cbn.
      rewrite (open_rec_lc_value vx (typing_value_lc _ _ _ Hvx) 0 (vfvar x)).
      eapply TT_App.
      * eapply VT_FVar. rewrite lookup_insert.
        destruct (decide (x = x)); [reflexivity | congruence].
      * eapply basic_typing_weaken_insert_value; [set_solver | exact Hvx].
  - eapply TT_Let with (L := dom Γ ∪ fv_value vx).
    + eapply TT_Match; eauto.
    + intros x Hx.
      cbn.
      rewrite (open_rec_lc_value vx (typing_value_lc _ _ _ Hvx) 0 (vfvar x)).
      eapply TT_App.
      * eapply VT_FVar. rewrite lookup_insert.
        destruct (decide (x = x)); [reflexivity | congruence].
      * eapply basic_typing_weaken_insert_value; [set_solver | exact Hvx].
Qed.

Lemma basic_typing_tret_fvar_insert Γ x T :
  <[x := T]> Γ ⊢ₑ tret (vfvar x) ⋮ T.
Proof.
  apply TT_Ret. apply VT_FVar.
  rewrite lookup_insert. destruct (decide (x = x)); [reflexivity | congruence].
Qed.

Lemma basic_typing_tapp_tm_fvar_insert Γ e x Tx T :
  x ∉ dom Γ →
  Γ ⊢ₑ e ⋮ (Tx →ₜ T) →
  <[x := Tx]> Γ ⊢ₑ tapp_tm e (vfvar x) ⋮ T.
Proof.
  intros Hx Htyped.
  eapply basic_typing_tapp_tm.
  - eapply basic_typing_weaken_insert_tm; [exact Hx | exact Htyped].
  - apply VT_FVar.
    rewrite lookup_insert. destruct (decide (x = x)); [reflexivity | congruence].
Qed.
