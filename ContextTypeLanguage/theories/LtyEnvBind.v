(** * ContextTypeLanguage.LtyEnvBind

    Type-language compatibility names for generic lvar-store binder laws. *)

From LocallyNameless Require Import Classes.
From ContextTypeLanguage Require Export LtyEnvProjection.

Lemma typed_lty_env_bind_dom (Σ : lty_env) T :
  dom (typed_lty_env_bind Σ T) =
  lvars_shift_from 0 (dom Σ) ∪ {[LVBound 0]}.
Proof. apply lvar_store_bind_dom. Qed.

Lemma typed_lty_env_bind_atom_env_insert_dom
    (Δ : gmap atom ty) x Tx Ty :
  x ∉ dom Δ ->
  dom (typed_lty_env_bind (atom_env_to_lty_env (<[x := Tx]> Δ)) Ty) =
  dom (typed_lty_env_bind (atom_env_to_lty_env Δ) Ty) ∪
  {[LVFree x]}.
Proof. apply lvar_store_bind_atom_store_insert_dom. Qed.

Lemma typed_lty_env_bind_lvars_fv_dom (Σ : lty_env) T :
  lvars_fv (dom (typed_lty_env_bind Σ T)) = lvars_fv (dom Σ).
Proof. apply lvar_store_bind_lvars_fv_dom. Qed.

Lemma lvars_at_depth_typed_lty_env_bind d (Σ : lty_env) T :
  lvars_at_depth (S d) (dom (typed_lty_env_bind Σ T)) =
  lvars_at_depth d (dom Σ).
Proof.
  rewrite typed_lty_env_bind_dom, lvars_at_depth_union.
  rewrite lvars_at_depth_shift_under by lia.
  rewrite lvars_at_depth_singleton_bound0_succ.
  set_solver.
Qed.

Lemma typed_lty_env_bind_atom_dom (Σ : lty_env) T :
  lty_env_atom_dom (typed_lty_env_bind Σ T) = lty_env_atom_dom Σ.
Proof. apply lvar_store_bind_atom_dom. Qed.

Lemma lty_env_insert_free_commute
    (Σ : lty_env) x y Tx Ty :
  x <> y ->
  <[LVFree x := Tx]> (<[LVFree y := Ty]> Σ) =
  <[LVFree y := Ty]> (<[LVFree x := Tx]> Σ).
Proof. apply lvar_store_insert_free_commute. Qed.

Lemma typed_lty_env_bind_insert_free
    (Σ : lty_env) x Tx T :
  typed_lty_env_bind (<[LVFree x := Tx]> Σ) T =
  <[LVFree x := Tx]> (typed_lty_env_bind Σ T).
Proof. apply lvar_store_bind_insert_free. Qed.

Lemma lty_env_union_insert_free_singleton
    (Σ : lty_env) x y Tx Ty :
  x <> y ->
  LVFree x ∉ dom Σ ->
  ((@union (gmap logic_var ty) _
      (<[LVFree y := Ty]> (Σ : gmap logic_var ty))
      (<[LVFree x := Tx]> (∅ : gmap logic_var ty))) : lty_env) =
  <[LVFree y := Ty]> (<[LVFree x := Tx]> Σ).
Proof. apply lvar_store_union_insert_free_singleton. Qed.

Lemma lty_env_closed_insert_free (Σ : lty_env) x T :
  lty_env_closed Σ ->
  lty_env_closed (<[LVFree x := T]> Σ).
Proof. apply lvar_store_closed_insert_free. Qed.

Lemma lty_env_closed_lookup_bound_none (Σ : lty_env) k :
  lty_env_closed Σ ->
  Σ !! LVBound k = None.
Proof. apply lvar_store_closed_lookup_bound_none. Qed.

Lemma lty_env_shift_closed (Σ : lty_env) :
  lty_env_closed Σ ->
  lty_env_shift Σ = Σ.
Proof. apply lvar_store_shift_closed. Qed.

Lemma typed_lty_env_bind_free_notin x (Σ : lty_env) T :
  LVFree x ∉ dom Σ ->
  LVFree x ∉ dom (typed_lty_env_bind Σ T).
Proof. apply lvar_store_bind_free_notin. Qed.

Lemma lty_env_shift_lookup_bound0_none (Σ : lty_env) :
  (lty_env_shift Σ : gmap logic_var ty) !! LVBound 0 = None.
Proof. apply lvar_store_shift_lookup_bound0_none. Qed.

Lemma logic_var_open_env_shift0_typed_bind_inj_on η (Σ : lty_env) T :
  open_env_fresh_for_lvars η (dom Σ) ->
  logic_var_open_env_inj_on (open_env_shift_from 0 η)
    (dom (<[LVBound 0 := T]> (lty_env_shift Σ))).
Proof. apply logic_var_open_env_shift0_lvar_store_bind_inj_on. Qed.

Lemma typed_lty_env_bind_open_under k x (Σ : lty_env) T :
  LVFree x ∉ dom Σ ->
  lty_env_open_one (S k) x (typed_lty_env_bind Σ T) =
  typed_lty_env_bind (lty_env_open_one k x Σ) T.
Proof. apply lvar_store_bind_open_under. Qed.

Lemma typed_lty_env_bind_open_current y (Σ : lty_env) T :
  LVFree y ∉ dom Σ ->
  lty_env_closed Σ ->
  lty_env_open_one 0 y (typed_lty_env_bind Σ T) =
  <[LVFree y := T]> Σ.
Proof. apply lvar_store_bind_open_current. Qed.

Lemma typed_lty_env_bind_open_current_base y (Σ : lty_env) b :
  LVFree y ∉ dom Σ ->
  lty_env_closed Σ ->
  lty_env_open_one 0 y (typed_lty_env_bind Σ (TBase b)) =
  <[LVFree y := TBase b]> Σ.
Proof. apply typed_lty_env_bind_open_current. Qed.

Lemma lty_env_open_typed_bind_atom_env (Δ : gmap atom ty) T x :
  x ∉ dom Δ ->
  lty_env_open_one 0 x
    (typed_lty_env_bind (atom_env_to_lty_env Δ) T) =
  atom_env_to_lty_env (<[x := T]> Δ).
Proof. apply lvar_store_open_bind_atom_store. Qed.

Lemma typed_lty_env_bind_open_env_shift0 η (Σ : lty_env) T :
  open_env_fresh_for_lvars η (dom Σ) ->
  lty_env_open_lvars (open_env_shift_from 0 η) (typed_lty_env_bind Σ T) =
  typed_lty_env_bind (lty_env_open_lvars η Σ) T.
Proof. apply lvar_store_bind_open_env_shift0. Qed.

Lemma typed_lty_env_bind_open_env_lift η (Σ : lty_env) T :
  open_env_fresh_for_lvars η (dom Σ) ->
  lty_env_open_lvars ((kmap S η)) (typed_lty_env_bind Σ T) =
  typed_lty_env_bind (lty_env_open_lvars η Σ) T.
Proof. apply lvar_store_bind_open_env_lift. Qed.
