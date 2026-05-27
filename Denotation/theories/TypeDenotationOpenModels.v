(** * Denotation.TypeDenotationOpenModels

    Split out from [TypeDenotation.v] to keep individual proof files small. *)

From Denotation Require Import Notation.
From Denotation Require Export TypeDenotationOpen.

Section TypeDenotation.

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
  rewrite <- (typed_lty_env_bind_open_current y Σ T Hfresh Hclosed).
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
  rewrite <- (typed_lty_env_bind_open_current y Σ T Hfresh Hclosed).
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
  rewrite <- (typed_lty_env_bind_open_current y Σ T Hfresh Hclosed).
  apply (proj2 (res_models_open_denot_ty_lvar_gas_iff
    0 y gas (typed_lty_env_bind Σ T) τ e m
    ltac:(rewrite typed_lty_env_bind_lvars_fv_dom;
      intros Hbad; apply Hfresh; apply lvars_fv_elem; exact Hbad)
    Hy Hτ)).
Qed.

End TypeDenotation.
