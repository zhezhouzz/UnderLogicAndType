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
