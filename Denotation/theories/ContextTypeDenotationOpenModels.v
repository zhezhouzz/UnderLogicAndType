(** * Denotation.ContextTypeDenotationOpenModels

    Split out from [ContextTypeDenotation.v] to keep individual proof files small. *)

From Denotation Require Import Notation.
From Denotation Require Export ContextTypeDenotationOpen.

Section ContextTypeDenotation.

Lemma res_models_open_denot_ty_bind0_iff
    y gas Σ T τ e (m : WfWorldT) :
  LVFree y ∉ dom Σ ->
  lty_env_closed Σ ->
  y ∉ fv_tm e ->
  y ∉ fv_cty τ ->
  m ⊨ formula_open 0 y
      (denot_ty_lvar_gas gas (typed_lty_env_bind Σ T) τ e) <->
    m ⊨ denot_ty_lvar_gas gas
      (<[LVFree y := T]> Σ)
      (cty_open 0 y τ)
      (open_tm 0 (vfvar y) e).
Proof.
  intros Hfresh Hclosed Hy Hτ.
  replace (<[LVFree y := T]> Σ) with
    (lty_env_open_one 0 y (typed_lty_env_bind Σ T))
    by exact (typed_lty_env_bind_open_current y Σ T Hfresh Hclosed).
  apply res_models_open_denot_ty_lvar_gas_iff.
  - rewrite typed_lty_env_bind_lvars_fv_dom.
    intros Hbad. apply Hfresh. apply lvars_fv_elem. exact Hbad.
  - exact Hy.
  - exact Hτ.
Qed.

Lemma res_models_open_denot_ty_lvar_gas_to_open_at
    k y gas Σ τ e (m : WfWorldT) :
  y ∉ lvars_fv (dom Σ) ->
  y ∉ fv_tm e ->
  y ∉ fv_cty τ ->
  m ⊨ formula_open k y (denot_ty_lvar_gas gas Σ τ e) ->
  m ⊨ denot_ty_lvar_gas gas
    (lty_env_open_one k y Σ)
    (cty_open k y τ)
    (open_tm k (vfvar y) e).
Proof.
  intros HΣ He Hτ.
  apply (proj1 (res_models_open_denot_ty_lvar_gas_iff
    k y gas Σ τ e m HΣ He Hτ)).
Qed.

Lemma res_models_open_denot_ty_lvar_gas_from_open_at
    k y gas Σ τ e (m : WfWorldT) :
  y ∉ lvars_fv (dom Σ) ->
  y ∉ fv_tm e ->
  y ∉ fv_cty τ ->
  m ⊨ denot_ty_lvar_gas gas
    (lty_env_open_one k y Σ)
    (cty_open k y τ)
    (open_tm k (vfvar y) e) ->
  m ⊨ formula_open k y (denot_ty_lvar_gas gas Σ τ e).
Proof.
  intros HΣ He Hτ.
  apply (proj2 (res_models_open_denot_ty_lvar_gas_iff
    k y gas Σ τ e m HΣ He Hτ)).
Qed.

Lemma res_models_open_denot_ty_lvar_gas_to_open
    y gas Σ T τ e (m : WfWorldT) :
  LVFree y ∉ dom Σ ->
  lty_env_closed Σ ->
  y ∉ fv_tm e ->
  y ∉ fv_cty τ ->
  m ⊨ formula_open 0 y
    (denot_ty_lvar_gas gas (typed_lty_env_bind Σ T) τ e) ->
  m ⊨ denot_ty_lvar_gas gas
    (<[LVFree y := T]> Σ)
    (cty_open 0 y τ)
    (open_tm 0 (vfvar y) e).
Proof.
  intros Hfresh Hclosed Hy Hτ.
  replace (<[LVFree y := T]> Σ) with
    (lty_env_open_one 0 y (typed_lty_env_bind Σ T))
    by exact (typed_lty_env_bind_open_current y Σ T Hfresh Hclosed).
  apply (proj1 (res_models_open_denot_ty_lvar_gas_iff
    0 y gas (typed_lty_env_bind Σ T) τ e m
    ltac:(rewrite typed_lty_env_bind_lvars_fv_dom;
      intros Hbad; apply Hfresh; apply lvars_fv_elem; exact Hbad)
    Hy Hτ)).
Qed.

Lemma res_models_open_denot_ty_lvar_gas_from_open
    y gas Σ T τ e (m : WfWorldT) :
  LVFree y ∉ dom Σ ->
  lty_env_closed Σ ->
  y ∉ fv_tm e ->
  y ∉ fv_cty τ ->
  m ⊨ denot_ty_lvar_gas gas
    (<[LVFree y := T]> Σ)
    (cty_open 0 y τ)
    (open_tm 0 (vfvar y) e) ->
  m ⊨ formula_open 0 y
    (denot_ty_lvar_gas gas (typed_lty_env_bind Σ T) τ e).
Proof.
  intros Hfresh Hclosed Hy Hτ.
  replace (<[LVFree y := T]> Σ) with
    (lty_env_open_one 0 y (typed_lty_env_bind Σ T))
    by exact (typed_lty_env_bind_open_current y Σ T Hfresh Hclosed).
  apply (proj2 (res_models_open_denot_ty_lvar_gas_iff
    0 y gas (typed_lty_env_bind Σ T) τ e m
    ltac:(rewrite typed_lty_env_bind_lvars_fv_dom;
      intros Hbad; apply Hfresh; apply lvars_fv_elem; exact Hbad)
    Hy Hτ)).
Qed.

Lemma denot_ty_lvar_gas_insert_commute_tapp_open
    gas (Σ : lty_env) x y T1 Ty τ e2 (m : WfWorldT) :
  x <> y ->
  m ⊨ denot_ty_lvar_gas gas
      (<[LVFree y := Ty]> (<[LVFree x := T1]> Σ))
      τ (tapp_tm (e2 ^^ x) (vfvar y)) ->
  m ⊨ denot_ty_lvar_gas gas
      (<[LVFree x := T1]> (<[LVFree y := Ty]> Σ))
      τ ((tapp_tm e2 (vfvar y)) ^^ x).
Proof.
  intros Hxy Hm.
  rewrite lty_env_insert_free_commute by exact Hxy.
  change (((tapp_tm e2 (vfvar y)) ^^ x)) with
    (open_tm 0 (vfvar x) (tapp_tm e2 (vfvar y))).
  rewrite open_tapp_tm_fvar_lc_arg.
  exact Hm.
Qed.

End ContextTypeDenotation.
