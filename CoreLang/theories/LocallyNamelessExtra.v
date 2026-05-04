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
  rewrite <- subst_open_var_value by set_solver.
  apply subst_lc_value; auto. apply Hbody. set_solver.
Qed.

Lemma subst_body_tm x u e :
  body_tm e -> lc_value u -> body_tm (tm_subst x u e).
Proof.
  intros [L Hbody] Hlc.
  exists (L ∪ {[x]}). intros y Hy.
  rewrite <- subst_open_var_tm by set_solver.
  apply subst_lc_tm; auto. apply Hbody. set_solver.
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
      simpl; intros y u; try set_solver.
  - destruct (decide (y = x)); set_solver.
Qed.

Lemma fv_of_subst_tm x u e :
  fv_tm (tm_subst x u e) ⊆ (fv_tm e ∖ {[x]}) ∪ fv_value u.
Proof.
  revert x u. induction e using tm_mut with
      (P := fun v => ∀ x u,
        fv_value (value_subst x u v) ⊆ (fv_value v ∖ {[x]}) ∪ fv_value u);
      simpl; intros y u; try set_solver.
  - destruct (decide (y = x)); set_solver.
Qed.

Lemma close_rm_fv_value x k v :
  x ∉ fv_value (close_value x k v).
Proof.
  revert k. induction v using value_mut with
      (P0 := fun e => ∀ k, x ∉ fv_tm (close_tm x k e));
      simpl; intros k; try set_solver.
  destruct (decide (x = x0)); set_solver.
Qed.

Lemma close_rm_fv_tm x k e :
  x ∉ fv_tm (close_tm x k e).
Proof.
  revert k. induction e using tm_mut with
      (P := fun v => ∀ k, x ∉ fv_value (close_value x k v));
      simpl; intros k; try set_solver.
  destruct (decide (x = x0)); set_solver.
Qed.

Lemma open_with_fresh_include_fv_value x v k :
  x ∉ fv_value v ->
  {[x]} ∪ fv_value v ⊆ {[x]} ∪ fv_value (open_value k (vfvar x) v).
Proof.
  intros Hfresh.
  pose proof (open_fv_value' v (vfvar x) k). set_solver.
Qed.

Lemma open_with_fresh_include_fv_tm x e k :
  x ∉ fv_tm e ->
  {[x]} ∪ fv_tm e ⊆ {[x]} ∪ fv_tm (open_tm k (vfvar x) e).
Proof.
  intros Hfresh.
  pose proof (open_fv_tm' e (vfvar x) k). set_solver.
Qed.

Lemma subst_commute_value x ux y uy v :
  x <> y ->
  x ∉ fv_value uy ->
  y ∉ fv_value ux ->
  value_subst x ux (value_subst y uy v) =
  value_subst y uy (value_subst x ux v).
Proof. Admitted.

Lemma subst_commute_tm x ux y uy e :
  x <> y ->
  x ∉ fv_value uy ->
  y ∉ fv_value ux ->
  tm_subst x ux (tm_subst y uy e) =
  tm_subst y uy (tm_subst x ux e).
Proof. Admitted.

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
