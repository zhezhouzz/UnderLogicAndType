From LocallyNameless Require Import Tactics.
From CoreLang Require Import Syntax LocallyNamelessProps.

(** * Additional locally-nameless algebra for CoreLang

    This file contains helper lemmas that are useful for typing and
    denotation proofs, but are not needed by the core locally-nameless
    regularity development in [LocallyNamelessProps]. *)

Lemma subst_open_var_value x y u k v :
  x <> y ->
  lc_value u ->
  value_subst x u (open_value k (vfvar y) v) =
  open_value k (vfvar y) (value_subst x u v).
Proof.
  intros Hxy Hlc.
  rewrite subst_open_value by exact Hlc.
  simpl. by rewrite decide_False.
Qed.

Lemma subst_open_var_tm x y u k e :
  x <> y ->
  lc_value u ->
  tm_subst x u (open_tm k (vfvar y) e) =
  open_tm k (vfvar y) (tm_subst x u e).
Proof.
  intros Hxy Hlc.
  rewrite subst_open_tm by exact Hlc.
  simpl. by rewrite decide_False.
Qed.

Lemma open_subst_same_value x y k v :
  x ∉ fv_value v ->
  value_subst x (vfvar y) (open_value k (vfvar x) v) =
  open_value k (vfvar y) v.
Proof.
  intros Hfresh. by apply subst_intro_value.
Qed.

Lemma open_subst_same_tm x y k e :
  x ∉ fv_tm e ->
  tm_subst x (vfvar y) (open_tm k (vfvar x) e) =
  open_tm k (vfvar y) e.
Proof.
  intros Hfresh. by apply subst_intro_tm.
Qed.

Lemma subst_body_value x u v :
  body_val v -> lc_value u -> body_val (value_subst x u v).
Proof.
  intros [L Hbody] Hlc.
  exists (L ∪ {[x]}). intros y Hy.
  rewrite <- subst_open_var_value by my_set_solver.
  apply subst_lc_value; auto. apply Hbody. my_set_solver.
Qed.

Lemma subst_body_tm x u e :
  body_tm e -> lc_value u -> body_tm (tm_subst x u e).
Proof.
  intros [L Hbody] Hlc.
  exists (L ∪ {[x]}). intros y Hy.
  rewrite <- subst_open_var_tm by my_set_solver.
  apply subst_lc_tm; auto. apply Hbody. my_set_solver.
Qed.

Lemma lc_implies_body_value v :
  lc_value v -> body_val v.
Proof.
  intros Hlc. exists ∅. intros x _. by rewrite open_rec_lc_value.
Qed.

Lemma lc_implies_body_tm e :
  lc_tm e -> body_tm e.
Proof.
  intros Hlc. exists ∅. intros x _. by rewrite open_rec_lc_tm.
Qed.

Lemma fv_of_subst_value x u v :
  fv_value (value_subst x u v) ⊆ (fv_value v ∖ {[x]}) ∪ fv_value u.
Proof.
  revert x u. induction v using value_mut with
      (P0 := fun e => ∀ x u,
        fv_tm (tm_subst x u e) ⊆ (fv_tm e ∖ {[x]}) ∪ fv_value u);
      simpl; intros y u; try my_set_solver.
  - destruct (decide (y = x)); my_set_solver.
Qed.

Lemma fv_of_subst_tm x u e :
  fv_tm (tm_subst x u e) ⊆ (fv_tm e ∖ {[x]}) ∪ fv_value u.
Proof.
  revert x u. induction e using tm_mut with
      (P := fun v => ∀ x u,
        fv_value (value_subst x u v) ⊆ (fv_value v ∖ {[x]}) ∪ fv_value u);
      simpl; intros y u; try my_set_solver.
  - destruct (decide (y = x)); my_set_solver.
Qed.

Lemma close_rm_fv_value x k v :
  x ∉ fv_value (close_value x k v).
Proof.
  revert k. induction v using value_mut with
      (P0 := fun e => ∀ k, x ∉ fv_tm (close_tm x k e));
      simpl; intros k; try my_set_solver.
  destruct (decide (x = x0)); my_set_solver.
Qed.

Lemma close_rm_fv_tm x k e :
  x ∉ fv_tm (close_tm x k e).
Proof.
  revert k. induction e using tm_mut with
      (P := fun v => ∀ k, x ∉ fv_value (close_value x k v));
      simpl; intros k; try my_set_solver.
  destruct (decide (x = x0)); my_set_solver.
Qed.

Lemma open_with_fresh_include_fv_value x v k :
  x ∉ fv_value v ->
  {[x]} ∪ fv_value v ⊆ {[x]} ∪ fv_value (open_value k (vfvar x) v).
Proof.
  intros Hfresh.
  pose proof (open_fv_value' v (vfvar x) k). my_set_solver.
Qed.

Lemma open_with_fresh_include_fv_tm x e k :
  x ∉ fv_tm e ->
  {[x]} ∪ fv_tm e ⊆ {[x]} ∪ fv_tm (open_tm k (vfvar x) e).
Proof.
  intros Hfresh.
  pose proof (open_fv_tm' e (vfvar x) k). my_set_solver.
Qed.

Lemma subst_commute_value x ux y uy v :
  x <> y ->
  x ∉ fv_value uy ->
  y ∉ fv_value ux ->
  value_subst x ux (value_subst y uy v) =
  value_subst y uy (value_subst x ux v).
Proof.
  intros Hxy Hxuy Hyux.
  induction v using value_mut with
      (P0 := fun e =>
        tm_subst x ux (tm_subst y uy e) =
        tm_subst y uy (tm_subst x ux e));
      simpl; try reflexivity.
  - destruct (decide (y = x0)); subst; simpl.
    + rewrite decide_False by done.
      simpl. rewrite decide_True by reflexivity.
      by rewrite subst_fresh_value_proven.
    + destruct (decide (x = x0)); subst; simpl.
      * symmetry. by rewrite subst_fresh_value_proven.
      * by rewrite decide_False by done.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma subst_commute_tm x ux y uy e :
  x <> y ->
  x ∉ fv_value uy ->
  y ∉ fv_value ux ->
  tm_subst x ux (tm_subst y uy e) =
  tm_subst y uy (tm_subst x ux e).
Proof.
  intros Hxy Hxuy Hyux.
  induction e using tm_mut with
      (P := fun v =>
        value_subst x ux (value_subst y uy v) =
        value_subst y uy (value_subst x ux v));
      simpl; try reflexivity.
  - destruct (decide (y = x0)); subst; simpl.
    + rewrite decide_False by done.
      simpl. rewrite decide_True by reflexivity.
      by rewrite subst_fresh_value_proven.
    + destruct (decide (x = x0)); subst; simpl.
      * symmetry. by rewrite subst_fresh_value_proven.
      * by rewrite decide_False by done.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma subst_subst_value x ux y uy v :
  x <> y ->
  y ∉ fv_value ux ->
  value_subst x ux (value_subst y uy v) =
  value_subst y (value_subst x ux uy) (value_subst x ux v).
Proof. Admitted.

Lemma subst_subst_tm x ux y uy e :
  x <> y ->
  y ∉ fv_value ux ->
  tm_subst x ux (tm_subst y uy e) =
  tm_subst y (value_subst x ux uy) (tm_subst x ux e).
Proof. Admitted.

Lemma close_fresh_rec_value x k v :
  x ∉ fv_value v ->
  close_value x k v = v.
Proof.
  revert k. induction v using value_mut with
      (P0 := fun e => ∀ k, x ∉ fv_tm e -> close_tm x k e = e);
      simpl; intros k Hfresh; try reflexivity; try (f_equal; eauto; my_set_solver).
  by rewrite decide_False by my_set_solver.
Qed.

Lemma close_fresh_rec_tm x k e :
  x ∉ fv_tm e ->
  close_tm x k e = e.
Proof.
  revert k. induction e using tm_mut with
      (P := fun v => ∀ k, x ∉ fv_value v -> close_value x k v = v);
      simpl; intros k Hfresh; try reflexivity; try (f_equal; eauto; my_set_solver).
  by rewrite decide_False by my_set_solver.
Qed.

Lemma close_var_rename_value x y k v :
  y ∉ fv_value v ->
  close_value x k v =
  close_value y k (value_subst x (vfvar y) v).
Proof. Admitted.

Lemma close_var_rename_tm x y k e :
  y ∉ fv_tm e ->
  close_tm x k e =
  close_tm y k (tm_subst x (vfvar y) e).
Proof. Admitted.

Lemma open_close_var_value x v :
  lc_value v ->
  open_value 0 (vfvar x) (close_value x 0 v) = v.
Proof. Admitted.

Lemma open_close_var_tm x e :
  lc_tm e ->
  open_tm 0 (vfvar x) (close_tm x 0 e) = e.
Proof. Admitted.

Lemma fv_of_subst_value_closed x u v :
  fv_value u = ∅ ->
  fv_value (value_subst x u v) = fv_value v ∖ {[x]}.
Proof.
  intros Hu.
  apply leibniz_equiv.
  split.
  - pose proof (fv_of_subst_value x u v) as Hsub.
    rewrite Hu in Hsub. my_set_solver.
  - assert (Hrev : ∀ x u,
        fv_value u = ∅ →
        fv_value v ∖ {[x]} ⊆ fv_value (value_subst x u v)).
    { clear x u Hu. induction v using value_mut with
        (P0 := fun e => ∀ x u,
          fv_value u = ∅ ->
          fv_tm e ∖ {[x]} ⊆ fv_tm (tm_subst x u e));
        simpl; intros y u Hu; try my_set_solver.
      destruct (decide (y = x)); subst; simpl; my_set_solver. }
    by apply Hrev.
Qed.

Lemma fv_of_subst_tm_closed x u e :
  fv_value u = ∅ ->
  fv_tm (tm_subst x u e) = fv_tm e ∖ {[x]}.
Proof.
  intros Hu.
  apply leibniz_equiv.
  split.
  - pose proof (fv_of_subst_tm x u e) as Hsub.
    rewrite Hu in Hsub. my_set_solver.
  - assert (Hrev : ∀ x u,
        fv_value u = ∅ →
        fv_tm e ∖ {[x]} ⊆ fv_tm (tm_subst x u e)).
    { clear x u Hu. induction e using tm_mut with
        (P := fun v => ∀ x u,
          fv_value u = ∅ ->
          fv_value v ∖ {[x]} ⊆ fv_value (value_subst x u v));
        simpl; intros y u Hu; try my_set_solver.
      destruct (decide (y = x)); subst; simpl; my_set_solver. }
    by apply Hrev.
Qed.

Lemma subst_shadow_value x z u v :
  x ∉ fv_value v ->
  value_subst x u (value_subst z (vfvar x) v) =
  value_subst z u v.
Proof. Admitted.

Lemma subst_shadow_tm x z u e :
  x ∉ fv_tm e ->
  tm_subst x u (tm_subst z (vfvar x) e) =
  tm_subst z u e.
Proof. Admitted.

Lemma subst_close_value x y u k v :
  x ∉ fv_value u ->
  x <> y ->
  close_value x k (value_subst y u v) =
  value_subst y u (close_value x k v).
Proof. Admitted.

Lemma subst_close_tm x y u k e :
  x ∉ fv_value u ->
  x <> y ->
  close_tm x k (tm_subst y u e) =
  tm_subst y u (close_tm x k e).
Proof. Admitted.

Lemma open_lc_respect_value k u w v :
  lc_value u ->
  lc_value w ->
  lc_value (open_value k u v) ->
  lc_value (open_value k w v).
Proof. Admitted.

Lemma open_lc_respect_tm k u w e :
  lc_value u ->
  lc_value w ->
  lc_tm (open_tm k u e) ->
  lc_tm (open_tm k w e).
Proof. Admitted.

Lemma open_idemp_value k u v :
  lc_value u ->
  open_value k u (open_value k u v) = open_value k u v.
Proof. Admitted.

Lemma open_idemp_tm k u e :
  lc_value u ->
  open_tm k u (open_tm k u e) = open_tm k u e.
Proof. Admitted.
