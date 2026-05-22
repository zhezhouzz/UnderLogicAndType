(** * CoreLang.Sugar

    Small derived forms used by examples.  The core syntax remains let-normal,
    with boolean-only matching.  The core language is deterministic; branching
    is ordinary boolean case analysis. *)

From CoreLang Require Export SmallStep OperationalProps LocallyNamelessProps.
From CoreLang Require Import BasicTypingProps.
From ChoicePrelude Require Import Prelude.

Definition vtrue : value := vconst (cbool true).
Definition vfalse : value := vconst (cbool false).
Definition vnat (n : nat) : value := vconst (cnat n).

Fixpoint tapp_tm (ef : tm) (vx : value) : tm :=
  match ef with
  | tret vf => tapp vf vx
  | tlete e1 e2 => tlete e1 (tapp_tm e2 (value_shift 0 vx))
  | _ => tlete ef (tapp (vbvar 0) (value_shift 0 vx))
  end.

Lemma fv_tapp_tm ef vx :
  fv_tm (tapp_tm ef vx) = fv_tm ef ∪ fv_value vx.
Proof.
  revert vx.
  induction ef; intros vx; simpl.
  - set_solver.
  - rewrite IHef2, fv_value_shift. set_solver.
  - rewrite fv_value_shift. set_solver.
  - rewrite fv_value_shift. set_solver.
  - rewrite fv_value_shift. set_solver.
Qed.

Local Lemma value_swap_atom_shift x y k v :
  value_swap_atom x y (value_shift k v) =
  value_shift k (value_swap_atom x y v)
with tm_swap_atom_shift x y k e :
  tm_swap_atom x y (tm_shift k e) =
  tm_shift k (tm_swap_atom x y e).
Proof.
  - destruct v; simpl; try reflexivity.
    + destruct decide; reflexivity.
    + rewrite tm_swap_atom_shift. reflexivity.
    + rewrite value_swap_atom_shift. reflexivity.
  - destruct e; simpl; rewrite ?value_swap_atom_shift, ?tm_swap_atom_shift;
      reflexivity.
Qed.

Lemma tm_swap_atom_tapp_tm x y ef vx :
  tm_swap_atom x y (tapp_tm ef vx) =
  tapp_tm (tm_swap_atom x y ef) (value_swap_atom x y vx).
Proof.
  revert vx.
  induction ef; intros vx; simpl; try rewrite value_swap_atom_shift;
    try reflexivity.
  rewrite IHef2, value_swap_atom_shift. reflexivity.
Qed.

Lemma tm_swap_atom_tapp_tm_fvar_fresh x y ef :
  x ∉ fv_tm ef →
  y ∉ fv_tm ef →
  tm_swap_atom x y (tapp_tm ef (vfvar x)) = tapp_tm ef (vfvar y).
Proof.
  intros Hx Hy.
  rewrite tm_swap_atom_tapp_tm.
  rewrite tm_swap_atom_fresh by assumption.
  simpl. replace (atom_swap x y x) with y by (symmetry; apply atom_swap_l).
  reflexivity.
Qed.

Local Lemma open_shift_open_fvar_mutual y :
  (∀ v k cutoff,
    cutoff <= k →
    open_value (S k) (vfvar y) (value_shift cutoff v) =
    value_shift cutoff (open_value k (vfvar y) v)) *
  (∀ e k cutoff,
    cutoff <= k →
    open_tm (S k) (vfvar y) (tm_shift cutoff e) =
    tm_shift cutoff (open_tm k (vfvar y) e)).
Proof.
  apply value_tm_mutind; simpl; intros; try reflexivity; try (f_equal; eauto with lia).
  - destruct (decide (cutoff <= n)) as [Hcn|Hcn];
      destruct (decide (k = n)) as [->|Hkn]; simpl.
    + destruct (decide (S n = S n)) as [_|Hneq]; [|lia].
      cbn [value_shift]. reflexivity.
    + destruct (decide (S k = S n)) as [Heq|_]; [lia |].
      destruct (decide (k = n)) as [Heq|_]; [lia |].
      destruct (decide (cutoff <= n)) as [_|Hbad]; [reflexivity | lia].
    + lia.
    + destruct (decide (S k = n)) as [Heq|_]; [lia |].
      destruct (decide (k = n)) as [Heq|_]; [lia |].
      destruct (decide (cutoff <= n)) as [Hbad|_]; [lia | reflexivity].
Qed.

Local Lemma open_value_shift_open_fvar k cutoff y v :
  cutoff <= k →
  open_value (S k) (vfvar y) (value_shift cutoff v) =
  value_shift cutoff (open_value k (vfvar y) v).
Proof. exact (fst (open_shift_open_fvar_mutual y) v k cutoff). Qed.

Local Lemma open_tm_shift_open_fvar k cutoff y e :
  cutoff <= k →
  open_tm (S k) (vfvar y) (tm_shift cutoff e) =
  tm_shift cutoff (open_tm k (vfvar y) e).
Proof. exact (snd (open_shift_open_fvar_mutual y) e k cutoff). Qed.

Local Lemma open_shift_open_below_mutual y :
  (∀ v j cutoff,
    j < cutoff →
    open_value j (vfvar y) (value_shift cutoff v) =
    value_shift cutoff (open_value j (vfvar y) v)) *
  (∀ e j cutoff,
    j < cutoff →
    open_tm j (vfvar y) (tm_shift cutoff e) =
    tm_shift cutoff (open_tm j (vfvar y) e)).
Proof.
  apply value_tm_mutind; simpl; intros; try reflexivity; try (f_equal; eauto with lia).
  destruct (decide (cutoff <= n)) as [Hcn|Hcn];
    destruct (decide (j = n)) as [Hjn|Hjn]; simpl.
  - subst. lia.
  - destruct (decide (j = S n)) as [Heq|_]; [lia |].
    destruct (decide (cutoff <= n)) as [_|Hbad]; [reflexivity | lia].
  - destruct (decide (j = n)) as [_|Hbad]; [reflexivity | lia].
  - destruct (decide (j = n)) as [Hbad|_]; [lia |].
    destruct (decide (cutoff <= n)) as [Hbad|_]; [lia | reflexivity].
Qed.

Local Lemma open_value_shift_open0 k y v :
  open_value 0 (vfvar y) (value_shift (S k) v) =
  value_shift (S k) (open_value 0 (vfvar y) v).
Proof. exact (fst (open_shift_open_below_mutual y) v 0 (S k) ltac:(lia)). Qed.

Local Lemma open_tm_shift_open0 k y e :
  open_tm 0 (vfvar y) (tm_shift (S k) e) =
  tm_shift (S k) (open_tm 0 (vfvar y) e).
Proof. exact (snd (open_shift_open_below_mutual y) e 0 (S k) ltac:(lia)). Qed.

Lemma open_tapp_tm_arg ef vx k y :
  open_tm k (vfvar y) (tapp_tm ef vx) =
  tapp_tm (open_tm k (vfvar y) ef) (open_value k (vfvar y) vx).
Proof.
  revert vx k.
  induction ef; intros vx k; simpl;
    try rewrite open_value_shift_open_fvar by lia;
    try (destruct (decide (S k = 0)); [lia | reflexivity]);
    try reflexivity.
  rewrite IHef2.
  rewrite open_value_shift_open_fvar by lia.
  reflexivity.
Qed.

Lemma open_tm_tret_bvar0_under k y :
  open_tm (S k) (vfvar y) (tret (vbvar 0)) = tret (vbvar 0).
Proof.
  simpl.
  destruct (decide (S k = 0)); [lia | reflexivity].
Qed.

Lemma open_tapp_tm_shift_bvar0_under ef k y :
  open_tm (S k) (vfvar y) (tapp_tm (tm_shift 0 ef) (vbvar 0)) =
  tapp_tm (tm_shift 0 (open_tm k (vfvar y) ef)) (vbvar 0).
Proof.
  rewrite open_tapp_tm_arg.
  rewrite open_tm_shift_open_fvar by lia.
  simpl.
  destruct (decide (S k = 0)); [lia | reflexivity].
Qed.

Local Lemma shift_lc_id_mutual :
  (∀ v, lc_value v → ∀ k, value_shift k v = v) ∧
  (∀ e, lc_tm e → ∀ k, tm_shift k e = e).
Proof.
  apply lc_mutind; simpl; try reflexivity.
  - intros s e L Hbody IH k. simpl. f_equal.
    pose (x := fresh_for (L ∪ fv_tm e)).
    assert (Hxfresh : x ∉ L ∪ fv_tm e) by (subst x; apply fresh_for_not_in).
    assert (HxL : x ∉ L) by set_solver.
    assert (Hxfv : x ∉ fv_tm e) by set_solver.
    specialize (IH x HxL (S k)) as IHx.
    apply (f_equal (close_tm x 0)) in IHx.
    rewrite <- open_tm_shift_open0 in IHx.
    rewrite close_open_var_tm in IHx by (rewrite fv_tm_shift; exact Hxfv).
    rewrite close_open_var_tm in IHx by exact Hxfv.
    exact IHx.
  - intros Tf vf L Hbody IH k. simpl. f_equal.
    pose (x := fresh_for (L ∪ fv_value vf)).
    assert (Hxfresh : x ∉ L ∪ fv_value vf) by (subst x; apply fresh_for_not_in).
    assert (HxL : x ∉ L) by set_solver.
    assert (Hxfv : x ∉ fv_value vf) by set_solver.
    specialize (IH x HxL (S k)) as IHx.
    apply (f_equal (close_value x 0)) in IHx.
    rewrite <- open_value_shift_open0 in IHx.
    rewrite close_open_var_value in IHx by (rewrite fv_value_shift; exact Hxfv).
    rewrite close_open_var_value in IHx by exact Hxfv.
    exact IHx.
  - intros v Hlv IHv k. simpl. rewrite IHv. reflexivity.
  - intros e1 e2 L He1 IH1 Hbody IH2 k. simpl. f_equal.
    + apply IH1.
    + pose (x := fresh_for (L ∪ fv_tm e2)).
      assert (Hxfresh : x ∉ L ∪ fv_tm e2) by (subst x; apply fresh_for_not_in).
      assert (HxL : x ∉ L) by set_solver.
      assert (Hxfv : x ∉ fv_tm e2) by set_solver.
      specialize (IH2 x HxL (S k)) as IHx.
      apply (f_equal (close_tm x 0)) in IHx.
      rewrite <- open_tm_shift_open0 in IHx.
      rewrite close_open_var_tm in IHx by (rewrite fv_tm_shift; exact Hxfv).
      rewrite close_open_var_tm in IHx by exact Hxfv.
      exact IHx.
  - intros op v Hlv IHv k. simpl. rewrite IHv. reflexivity.
  - intros v1 v2 Hv1 IH1 Hv2 IH2 k. simpl. rewrite IH1, IH2. reflexivity.
  - intros v et ef Hv IHv Het IHet Hef IHef k.
    simpl. rewrite IHv, IHet, IHef. reflexivity.
Qed.

Lemma value_shift_lc_id k v :
  lc_value v →
  value_shift k v = v.
Proof.
  intros Hlc.
  exact (proj1 shift_lc_id_mutual v Hlc k).
Qed.

Lemma tm_shift_lc_id k e :
  lc_tm e →
  tm_shift k e = e.
Proof.
  intros Hlc.
  exact (proj2 shift_lc_id_mutual e Hlc k).
Qed.

Local Lemma value_shift_lc k v :
  lc_value v →
  lc_value (value_shift k v).
Proof.
  intros Hlc.
  rewrite (value_shift_lc_id k v Hlc).
  exact Hlc.
Qed.

Lemma open_tapp_tm_lc_arg ef vx k u :
  lc_value vx →
  open_tm k u (tapp_tm ef vx) = tapp_tm (open_tm k u ef) vx.
Proof.
  intros Hvx. revert vx k Hvx.
  induction ef; intros vx k Hvx; simpl;
    try rewrite (open_rec_lc_value vx Hvx k u);
    try rewrite (open_rec_lc_value (value_shift 0 vx) (value_shift_lc 0 vx Hvx) (S k) u);
    try (destruct (decide (S k = 0)); [lia | reflexivity]).
  - rewrite IHef2 by (apply value_shift_lc; exact Hvx).
    reflexivity.
Qed.

Lemma tapp_tm_tlete e1 e2 v :
  tapp_tm (tlete e1 e2) v = tlete e1 (tapp_tm e2 (value_shift 0 v)).
Proof. reflexivity. Qed.

Lemma tapp_tm_tlete_fvar e1 e2 x :
  tapp_tm (tlete e1 e2) (vfvar x) = tlete e1 (tapp_tm e2 (vfvar x)).
Proof. reflexivity. Qed.

Lemma open_tapp_tm_fvar e x y :
  (tapp_tm e (vfvar y)) ^^ x = tapp_tm (e ^^ x) (vfvar y).
Proof.
  unfold open_one.
  apply open_tapp_tm_lc_arg. constructor.
Qed.

Ltac core_sugar_norm :=
  rewrite ?tapp_tm_tlete_fvar;
  rewrite ?open_tapp_tm_fvar.

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
    rewrite open_tapp_tm_lc_arg by (apply value_shift_lc; exact Hvx).
    eauto using value_shift_lc.
  - eapply LC_lete with (L := ∅); [constructor; exact H |].
    intros x _.
    change (lc_tm (tapp (vfvar x)
      (open_value 0 (vfvar x) (value_shift 0 vx)))).
    rewrite (open_rec_lc_value _ (value_shift_lc 0 vx Hvx) 0 (vfvar x)).
    repeat constructor. apply value_shift_lc. exact Hvx.
  - eapply LC_lete with (L := ∅); [constructor; assumption |].
    intros x _.
    change (lc_tm (tapp (vfvar x)
      (open_value 0 (vfvar x) (value_shift 0 vx)))).
    rewrite (open_rec_lc_value _ (value_shift_lc 0 vx Hvx) 0 (vfvar x)).
    repeat constructor. apply value_shift_lc. exact Hvx.
  - eapply LC_lete with (L := ∅); [constructor; assumption |].
    intros x _.
    change (lc_tm (tapp (vfvar x)
      (open_value 0 (vfvar x) (value_shift 0 vx)))).
    rewrite (open_rec_lc_value _ (value_shift_lc 0 vx Hvx) 0 (vfvar x)).
    repeat constructor. apply value_shift_lc. exact Hvx.
Qed.

Local Lemma basic_typing_value_shift Γ v T k :
  Γ ⊢ᵥ v ⋮ T →
  Γ ⊢ᵥ value_shift k v ⋮ T.
Proof.
  intros Hty.
  rewrite (value_shift_lc_id k v (typing_value_lc _ _ _ Hty)).
  exact Hty.
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
      change (<[x:=T1]> Γ ⊢ₑ
        open_tm 0 (vfvar x) (tapp_tm e2 (value_shift 0 vx)) ⋮ T0).
      rewrite open_tapp_tm_lc_arg
        by (apply value_shift_lc; exact (typing_value_lc _ _ _ Hvx)).
      refine (H0 x _ Tx0 T0 (value_shift 0 vx) _ _).
      * set_solver.
      * apply basic_typing_value_shift.
        eapply basic_typing_weaken_insert_value; [set_solver | exact Hvx].
      * reflexivity.
  - discriminate.
  - eapply TT_Let with (L := dom Γ ∪ fv_value vx).
    + eapply TT_App; eauto.
    + intros x Hx.
      cbn.
      rewrite (open_rec_lc_value _ (value_shift_lc 0 vx
        (typing_value_lc _ _ _ Hvx)) 0 (vfvar x)).
      eapply TT_App.
      * eapply VT_FVar. apply lookup_insert_eq.
      * apply basic_typing_value_shift.
        eapply basic_typing_weaken_insert_value; [set_solver | exact Hvx].
  - eapply TT_Let with (L := dom Γ ∪ fv_value vx).
    + eapply TT_Match; eauto.
    + intros x Hx.
      cbn.
      rewrite (open_rec_lc_value _ (value_shift_lc 0 vx
        (typing_value_lc _ _ _ Hvx)) 0 (vfvar x)).
      eapply TT_App.
      * eapply VT_FVar. rewrite lookup_insert.
        destruct (decide (x = x)); [reflexivity | congruence].
      * apply basic_typing_value_shift.
        eapply basic_typing_weaken_insert_value; [set_solver | exact Hvx].
Qed.

Lemma basic_typing_tret_fvar_insert Γ x T :
  <[x := T]> Γ ⊢ₑ tret (vfvar x) ⋮ T.
Proof.
  apply TT_Ret. apply VT_FVar.
  apply lookup_insert_eq.
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
    apply lookup_insert_eq.
Qed.
