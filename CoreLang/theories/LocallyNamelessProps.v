From LocallyNameless Require Import Tactics.
From Stdlib Require Import Lia.

(** * Locally-nameless facts for CoreLang

    The statements here are adapted from HATs' [CoreLangProp.v] and
    UnderType's [LocallyNameless/LangLc.v], specialized to the simplified
    CoreLang syntax used in this repository. *)

Lemma lc_bvar_absurd n : ¬ lc_value (vbvar n).
Proof. inversion 1. Qed.

Lemma lc_lam_iff_body s e :
  lc_value (vlam s e) ↔ body_tm e.
Proof.
  split.
  - intros H. inversion H; subst. hauto.
  - hauto.
Qed.

Lemma lc_fix_iff_body Tf vf :
  lc_value (vfix Tf vf) ↔ body_val vf.
Proof.
  split.
  - intros H. inversion H; subst. hauto.
  - hauto.
Qed.

Lemma lc_ret_iff_value v :
  lc_tm (tret v) ↔ lc_value v.
Proof.
  split; inversion 1; subst; eauto.
Qed.

Lemma body_ret_iff_value v :
  body_tm (tret v) ↔ body_val v.
Proof.
  split; intros [L Hbody]; exists L; intros x Hx; specialize (Hbody x Hx); simpl in *.
  - by apply lc_ret_iff_value in Hbody.
  - by apply lc_ret_iff_value.
Qed.

Lemma lc_lete_iff_body e1 e2 :
  lc_tm (tlete e1 e2) ↔ lc_tm e1 ∧ body_tm e2.
Proof.
  split.
  - intros H. inversion H; subst. split; eauto. eexists; eauto.
  - intros [Hlc1 [L Hbody]]. econstructor; eauto.
Qed.

Lemma lc_prim_iff_value op v :
  lc_tm (tprim op v) ↔ lc_value v.
Proof.
  split; inversion 1; subst; eauto.
Qed.

Lemma lc_app_iff_values v1 v2 :
  lc_tm (tapp v1 v2) ↔ lc_value v1 ∧ lc_value v2.
Proof.
  split; inversion 1; subst; eauto.
Qed.

Lemma lc_match_iff_parts v et ef :
  lc_tm (tmatch v et ef) ↔ lc_value v ∧ lc_tm et ∧ lc_tm ef.
Proof.
  split.
  - inversion 1; subst; hauto.
  - hauto.
Qed.

Lemma close_open_var_value (v : value) (x : atom) k :
  x ∉ fv_value v →
  close_value x k (open_value k (vfvar x) v) = v.
Proof.
  revert x k. induction v using value_mut with
      (P0 := fun e => ∀ x k, x ∉ fv_tm e →
        close_tm x k (open_tm k (vfvar x) e) = e);
      simpl; intros y j Hy;
      try solve [reflexivity | f_equal; eauto; my_set_solver].
  - rewrite decide_False by my_set_solver. reflexivity.
  - destruct (decide (j = n)); subst; simpl.
    + rewrite decide_True by reflexivity. reflexivity.
    + reflexivity.
Qed.

Lemma close_open_var_tm (e : tm) (x : atom) k :
  x ∉ fv_tm e →
  close_tm x k (open_tm k (vfvar x) e) = e.
Proof.
  revert x k. induction e using tm_mut with
      (P := fun v => ∀ x k, x ∉ fv_value v →
        close_value x k (open_value k (vfvar x) v) = v);
      simpl; intros y j Hy;
      try solve [reflexivity | f_equal; eauto; my_set_solver].
  - rewrite decide_False by my_set_solver. reflexivity.
  - destruct (decide (j = n)); subst; simpl.
    + rewrite decide_True by reflexivity. reflexivity.
    + reflexivity.
Qed.

Lemma open_fv_value (v u : value) k :
  fv_value (open_value k u v) ⊆ fv_value u ∪ fv_value v.
Proof.
  revert u k. induction v using value_mut with
      (P0 := fun e => ∀ u k,
        fv_tm (open_tm k u e) ⊆ fv_value u ∪ fv_tm e);
      simpl; intros u j; try my_set_solver.
  destruct (decide (j = n)); my_set_solver.
Qed.

Lemma open_fv_tm (e : tm) (u : value) k :
  fv_tm (open_tm k u e) ⊆ fv_value u ∪ fv_tm e.
Proof.
  revert u k. induction e using tm_mut with
      (P := fun v => ∀ u k,
        fv_value (open_value k u v) ⊆ fv_value u ∪ fv_value v);
      simpl; intros u j; try my_set_solver.
  destruct (decide (j = n)); my_set_solver.
Qed.

Lemma open_fv_value' (v u : value) k :
  fv_value v ⊆ fv_value (open_value k u v).
Proof.
  revert u k. induction v using value_mut with
      (P0 := fun e => ∀ u k,
        fv_tm e ⊆ fv_tm (open_tm k u e));
      simpl; intros u j; try set_solver.
Qed.

Lemma open_fv_tm' (e : tm) (u : value) k :
  fv_tm e ⊆ fv_tm (open_tm k u e).
Proof.
  revert u k. induction e using tm_mut with
      (P := fun v => ∀ u k,
        fv_value v ⊆ fv_value (open_value k u v));
      simpl; intros u j; try set_solver.
Qed.

Lemma subst_fresh_value_proven x u (v : value) :
  x ∉ fv_value v → value_subst x u v = v.
Proof.
  revert x u. induction v using value_mut with
      (P0 := fun e => ∀ x u, x ∉ fv_tm e → tm_subst x u e = e);
      simpl; intros y u Hy; try reflexivity; try f_equal; eauto; try set_solver.
  rewrite decide_False by set_solver. reflexivity.
Qed.

Lemma subst_fresh_tm_proven x u (e : tm) :
  x ∉ fv_tm e → tm_subst x u e = e.
Proof.
  revert x u. induction e using tm_mut with
      (P := fun v => ∀ x u, x ∉ fv_value v → value_subst x u v = v);
      simpl; intros y u Hy; try reflexivity; try f_equal; eauto; try set_solver.
  rewrite decide_False by set_solver. reflexivity.
Qed.

Ltac crush_nat_decides :=
  repeat match goal with
  | H : context[decide (?i = ?i)] |- _ =>
      rewrite decide_True in H by reflexivity
  | |- context[decide (?i = ?i)] =>
      rewrite decide_True by reflexivity
  | H : context[decide (?i = ?j)] |- _ =>
      rewrite decide_False in H by lia
  | |- context[decide (?i = ?j)] =>
      rewrite decide_False by lia
  end.

Lemma open_rec_open_eq_value u w (v : value) i j :
  i ≠ j →
  open_value i u (open_value j w v) = open_value j w v →
  open_value i u v = v.
Proof.
  revert i j. induction v using value_mut with
      (P0 := fun e => ∀ i j,
        i ≠ j →
        open_tm i u (open_tm j w e) = open_tm j w e →
        open_tm i u e = e);
      simpl; intros i j Hneq Heq; try reflexivity.
  - destruct (decide (j = n)); destruct (decide (i = n)); subst; simpl in *;
      crush_nat_decides; try contradiction; auto.
  - inversion Heq; subst. f_equal; eauto; lia.
  - inversion Heq; subst. f_equal; eauto; lia.
  - inversion Heq. f_equal; eauto.
  - inversion Heq. f_equal; eauto.
  - inversion Heq. f_equal; eauto.
  - inversion Heq. f_equal; eauto.
  - inversion Heq. f_equal; eauto.
Qed.

Lemma open_rec_open_eq_tm u w (e : tm) i j :
  i ≠ j →
  open_tm i u (open_tm j w e) = open_tm j w e →
  open_tm i u e = e.
Proof.
  revert i j. induction e using tm_mut with
      (P := fun v => ∀ i j,
        i ≠ j →
        open_value i u (open_value j w v) = open_value j w v →
        open_value i u v = v);
      simpl; intros i j Hneq Heq; try reflexivity.
  - destruct (decide (j = n)); destruct (decide (i = n)); subst; simpl in *;
      crush_nat_decides; try contradiction; auto.
  - inversion Heq; subst. f_equal; eauto; lia.
  - inversion Heq; subst. f_equal; eauto; lia.
  - inversion Heq. f_equal; eauto.
  - inversion Heq. f_equal; eauto.
  - inversion Heq. f_equal; eauto.
  - inversion Heq. f_equal; eauto.
  - inversion Heq. f_equal; eauto.
Qed.

Lemma open_rec_lc_mutual :
  (∀ v, lc_value v → ∀ k u, open_value k u v = v) ∧
  (∀ e, lc_tm e → ∀ k u, open_tm k u e = e).
Proof.
  apply lc_mutind; simpl; intros; try reflexivity; try (f_equal; eauto).
  - f_equal.
    pose (x := fresh_for L).
    assert (Hx : x ∉ L) by (subst x; apply fresh_for_not_in).
    eapply open_rec_open_eq_tm with (j := 0) (w := vfvar x); [lia |].
    exact (H x Hx (S k) u).
  - f_equal.
    pose (x := fresh_for L).
    assert (Hx : x ∉ L) by (subst x; apply fresh_for_not_in).
    eapply open_rec_open_eq_value with (j := 0) (w := vfvar x); [lia |].
    exact (H x Hx (S k) u).
  - pose (x := fresh_for L).
    assert (Hx : x ∉ L) by (subst x; apply fresh_for_not_in).
    eapply open_rec_open_eq_tm with (j := 0) (w := vfvar x); [lia |].
    exact (H0 x Hx (S k) u).
Qed.

Lemma open_rec_lc_value v :
  lc_value v → ∀ k u, open_value k u v = v.
Proof. exact (proj1 open_rec_lc_mutual v). Qed.

Lemma open_rec_lc_tm e :
  lc_tm e → ∀ k u, open_tm k u e = e.
Proof. exact (proj2 open_rec_lc_mutual e). Qed.

Lemma subst_open_value x u w k v :
  lc_value w →
  value_subst x w (open_value k u v) =
  open_value k (value_subst x w u) (value_subst x w v).
Proof.
  revert x u w k. induction v using value_mut with
      (P0 := fun e => ∀ x u w k,
        lc_value w →
        tm_subst x w (open_tm k u e) =
        open_tm k (value_subst x w u) (tm_subst x w e));
      simpl; intros y u w k Hlc; try reflexivity; try (f_equal; eauto).
  - destruct (decide (y = x)); subst; simpl.
    + symmetry. by apply open_rec_lc_value.
    + reflexivity.
  - destruct (decide (k = n)); subst; simpl.
    + reflexivity.
    + reflexivity.
Qed.

Lemma subst_open_tm x u w k e :
  lc_value w →
  tm_subst x w (open_tm k u e) =
  open_tm k (value_subst x w u) (tm_subst x w e).
Proof.
  revert x u w k. induction e using tm_mut with
      (P := fun v => ∀ x u w k,
        lc_value w →
        value_subst x w (open_value k u v) =
        open_value k (value_subst x w u) (value_subst x w v));
      simpl; intros y u w k Hlc; try reflexivity; try (f_equal; eauto).
  - destruct (decide (y = x)); subst; simpl.
    + symmetry. by apply open_rec_lc_value.
    + reflexivity.
  - destruct (decide (k = n)); subst; simpl.
    + reflexivity.
    + reflexivity.
Qed.

Lemma subst_lc_mutual :
  (∀ v, lc_value v → ∀ x u, lc_value u → lc_value (value_subst x u v)) ∧
  (∀ e, lc_tm e → ∀ x u, lc_value u → lc_tm (tm_subst x u e)).
Proof.
  apply lc_mutind; simpl; intros; eauto.
  - destruct (decide (x = x0)).
    + hauto.
    + hauto.
  - eapply LC_lam with (L := L ∪ {[x]}); intros y Hy.
    replace (vfvar y) with (value_subst x u (vfvar y))
      by (simpl; rewrite decide_False by set_solver; reflexivity).
    rewrite <- subst_open_tm by eauto.
    apply H; set_solver.
  - eapply LC_fix with (L := L ∪ {[x]}); intros y Hy.
    replace (vfvar y) with (value_subst x u (vfvar y))
      by (simpl; rewrite decide_False by set_solver; reflexivity).
    rewrite <- subst_open_value by eauto.
    apply H; set_solver.
  - eapply LC_lete with (L := L ∪ {[x]}); eauto.
    intros y Hy.
    replace (vfvar y) with (value_subst x u (vfvar y))
      by (simpl; rewrite decide_False by set_solver; reflexivity).
    rewrite <- subst_open_tm by eauto.
    apply H0; set_solver.
Qed.

Lemma subst_lc_value x u v :
  lc_value v → lc_value u → lc_value (value_subst x u v).
Proof. intros Hlc Hu. exact (proj1 subst_lc_mutual v Hlc x u Hu). Qed.

Lemma subst_lc_tm x u e :
  lc_tm e → lc_value u → lc_tm (tm_subst x u e).
Proof. intros Hlc Hu. exact (proj2 subst_lc_mutual e Hlc x u Hu). Qed.

Lemma subst_intro_value x w k v :
  x ∉ fv_value v →
  lc_value w →
  value_subst x w (open_value k (vfvar x) v) = open_value k w v.
Proof.
  intros Hfresh Hlc.
  rewrite subst_open_value by exact Hlc.
  simpl. rewrite decide_True by reflexivity.
  by rewrite subst_fresh_value_proven.
Qed.

Lemma subst_intro_tm x w k e :
  x ∉ fv_tm e →
  lc_value w →
  tm_subst x w (open_tm k (vfvar x) e) = open_tm k w e.
Proof.
  intros Hfresh Hlc.
  rewrite subst_open_tm by exact Hlc.
  simpl. rewrite decide_True by reflexivity.
  by rewrite subst_fresh_tm_proven.
Qed.

Lemma body_open_value v u :
  body_val v → lc_value u → lc_value (open_value 0 u v).
Proof.
  intros [L Hbody] Hlc.
  pose (x := fresh_for (L ∪ fv_value v)).
  assert (Hxfresh : x ∉ L ∪ fv_value v) by (subst x; apply fresh_for_not_in).
  assert (HxL : x ∉ L) by set_solver.
  assert (Hxfv : x ∉ fv_value v) by set_solver.
  specialize (Hbody x HxL).
  rewrite <- (subst_intro_value x u 0 v Hxfv Hlc).
  by apply subst_lc_value.
Qed.

Lemma body_open_tm e u :
  body_tm e → lc_value u → lc_tm (open_tm 0 u e).
Proof.
  intros [L Hbody] Hlc.
  pose (x := fresh_for (L ∪ fv_tm e)).
  assert (Hxfresh : x ∉ L ∪ fv_tm e) by (subst x; apply fresh_for_not_in).
  assert (HxL : x ∉ L) by set_solver.
  assert (Hxfv : x ∉ fv_tm e) by set_solver.
  specialize (Hbody x HxL).
  rewrite <- (subst_intro_tm x u 0 e Hxfv Hlc).
  by apply subst_lc_tm.
Qed.
