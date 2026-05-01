From LocallyNameless Require Import Tactics.

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
  - intros H. inversion H; subst. eexists. eauto.
  - intros [L H]. econstructor. exact H.
Qed.

Lemma lc_fix_iff_body Tf vf :
  lc_value (vfix Tf vf) ↔ body_val vf.
Proof.
  split.
  - intros H. inversion H; subst. eexists. eauto.
  - intros [L H]. econstructor. exact H.
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
  - inversion 1; subst; eauto.
  - intros [Hlc_v [Hlc_t Hlc_f]]. constructor; auto.
Qed.

Lemma close_open_var_value (v : value) (x : atom) k :
  x ∉ fv_value v →
  close_value x k (open_value k (vfvar x) v) = v
with close_open_var_tm (e : tm) (x : atom) k :
  x ∉ fv_tm e →
  close_tm x k (open_tm k (vfvar x) e) = e.
Proof. Admitted.

Lemma open_fv_value (v u : value) k :
  fv_value (open_value k u v) ⊆ fv_value u ∪ fv_value v
with open_fv_tm (e : tm) (u : value) k :
  fv_tm (open_tm k u e) ⊆ fv_value u ∪ fv_tm e.
Proof. Admitted.

Lemma open_fv_value' (v u : value) k :
  fv_value v ⊆ fv_value (open_value k u v)
with open_fv_tm' (e : tm) (u : value) k :
  fv_tm e ⊆ fv_tm (open_tm k u e).
Proof. Admitted.

Lemma subst_fresh_value_proven x u (v : value) :
  x ∉ fv_value v → value_subst x u v = v
with subst_fresh_tm_proven x u (e : tm) :
  x ∉ fv_tm e → tm_subst x u e = e.
Proof. Admitted.

Lemma open_rec_lc_value v :
  lc_value v → ∀ k u, open_value k u v = v
with open_rec_lc_tm e :
  lc_tm e → ∀ k u, open_tm k u e = e.
Proof. Admitted.

Lemma subst_lc_value x u v :
  lc_value v → lc_value u → lc_value (value_subst x u v)
with subst_lc_tm x u e :
  lc_tm e → lc_value u → lc_tm (tm_subst x u e).
Proof. Admitted.

Lemma subst_open_value x u w k v :
  lc_value w →
  value_subst x w (open_value k u v) =
  open_value k (value_subst x w u) (value_subst x w v)
with subst_open_tm x u w k e :
  lc_value w →
  tm_subst x w (open_tm k u e) =
  open_tm k (value_subst x w u) (tm_subst x w e).
Proof. Admitted.

Lemma subst_intro_value x w k v :
  x ∉ fv_value v →
  lc_value w →
  value_subst x w (open_value k (vfvar x) v) = open_value k w v.
Proof. Admitted.

Lemma subst_intro_tm x w k e :
  x ∉ fv_tm e →
  lc_value w →
  tm_subst x w (open_tm k (vfvar x) e) = open_tm k w e.
Proof. Admitted.
