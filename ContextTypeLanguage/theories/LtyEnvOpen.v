(** * ContextTypeLanguage.LtyEnvOpen

    Type-language compatibility names for generic lvar-store opening laws. *)

From LocallyNameless Require Import Classes.
From ContextTypeLanguage Require Export LtyEnvCore.

Lemma lty_env_open_one_dom k x (Σ : lty_env) :
  dom (lty_env_open_one k x Σ) = lvars_open k x (dom Σ).
Proof. apply lvar_store_open_one_dom. Qed.

Lemma lty_env_open_lvars_empty (Σ : lty_env) :
  lty_env_open_lvars ∅ Σ = Σ.
Proof. apply lvar_store_open_lvars_empty. Qed.

Lemma lty_env_open_lvars_singleton k x (Σ : lty_env) :
  LVFree x ∉ dom Σ ->
  lty_env_open_lvars (<[k := x]> ∅) Σ =
  lty_env_open_one k x Σ.
Proof. apply lvar_store_open_lvars_singleton. Qed.

Lemma lty_env_open_lvars_open_one_empty k x (Σ : lty_env) :
  LVFree x ∉ dom Σ ->
  lty_env_open_lvars ∅ (lty_env_open_one k x Σ) =
  lty_env_open_lvars (<[k := x]> ∅) Σ.
Proof. apply lvar_store_open_lvars_open_one_empty. Qed.

Lemma lty_env_open_lvars_dom η (Σ : lty_env) :
  open_env_fresh_for_lvars η (dom Σ) ->
  dom (lty_env_open_lvars η Σ) =
  lvars_open_env_simul η (dom Σ).
Proof. apply lvar_store_open_lvars_dom. Qed.

Lemma lty_env_open_lvars_lookup_fresh η v T (Σ : lty_env) :
  Σ !! v = None ->
  open_env_fresh_for_lvars η (dom (<[v := T]> Σ)) ->
  lty_env_open_lvars η Σ !! logic_var_open_env η v = None.
Proof. apply lvar_store_open_lvars_lookup_fresh. Qed.

Lemma lty_env_open_lvars_insert_entry η v T (Σ : lty_env) :
  Σ !! v = None ->
  logic_var_open_env_inj_on η (dom (<[v := T]> Σ)) ->
  lty_env_open_lvars η (<[v := T]> Σ) =
  <[logic_var_open_env η v := T]> (lty_env_open_lvars η Σ).
Proof. apply lvar_store_open_lvars_insert_entry. Qed.

Lemma lty_env_open_lvars_insert_fresh η k x (Σ : lty_env) :
  η !! k = None ->
  open_env_avoids_atom x η ->
  open_env_fresh_for_lvars (<[k := x]> η) (dom Σ) ->
  lty_env_open_lvars (<[k := x]> η) Σ =
  lty_env_open_one k x (lty_env_open_lvars η Σ).
Proof. apply lvar_store_open_lvars_insert_fresh. Qed.

Lemma lty_env_open_lvars_open_one η k x (Σ : lty_env) :
  x ∉ lvars_fv (dom Σ) ->
  open_env_fresh_for_lvars η (dom (lty_env_open_one k x Σ)) ->
  lty_env_open_lvars η (lty_env_open_one k x Σ) =
  lty_env_open_lvars (<[k := x]> η) Σ.
Proof. apply lvar_store_open_lvars_open_one. Qed.

Lemma lty_env_open_one_fresh_noop k x (Σ : lty_env) :
  LVBound k ∉ dom Σ ->
  LVFree x ∉ dom Σ ->
  lty_env_open_one k x Σ = Σ.
Proof. apply lvar_store_open_one_fresh_noop. Qed.

Lemma lty_env_open_one_involutive k x (Σ : lty_env) :
  lty_env_open_one k x (lty_env_open_one k x Σ) = Σ.
Proof. apply lvar_store_open_one_involutive. Qed.

Lemma lty_env_open_one_insert k x v T (Σ : lty_env) :
  lty_env_open_one k x (<[v := T]> Σ) =
  <[logic_var_open k x v := T]> (lty_env_open_one k x Σ).
Proof. apply lvar_store_open_one_insert. Qed.

Lemma lty_env_open_one_insert_fresh k x v T (Σ : lty_env) :
  logic_var_open k x v ∉ dom (lty_env_open_one k x Σ) ->
  lty_env_open_one k x (<[v := T]> Σ) =
  <[logic_var_open k x v := T]> (lty_env_open_one k x Σ).
Proof. apply lvar_store_open_one_insert_fresh. Qed.

Lemma lty_env_open_one_shift_under_gen j k x (Σ : lty_env) :
  j <= k ->
  lty_env_open_one (S k) x (lty_env_shift_from j Σ) =
  lty_env_shift_from j (lty_env_open_one k x Σ).
Proof. apply lvar_store_open_one_shift_under_gen. Qed.

Lemma lty_env_open_one_shift_under j k x (Σ : lty_env) :
  j <= k ->
  lty_env_open_one (S (S k)) x (lty_env_shift_from (S j) Σ) =
  lty_env_shift_from (S j) (lty_env_open_one (S k) x Σ).
Proof. apply lvar_store_open_one_shift_under. Qed.

Lemma lvars_open_shift_dom_gen j k x (Σ : lty_env) :
  j <= k ->
  lvars_open (S k) x (lvars_shift_from j (dom Σ)) =
  lvars_shift_from j (lvars_open k x (dom Σ)).
Proof. apply lvar_store_lvars_open_shift_dom_gen. Qed.

Lemma lvars_open_shift_dom j k x (Σ : lty_env) :
  j <= k ->
  lvars_open (S (S k)) x (lvars_shift_from (S j) (dom Σ)) =
  lvars_shift_from (S j) (lvars_open (S k) x (dom Σ)).
Proof. apply lvar_store_lvars_open_shift_dom. Qed.

Lemma lty_env_open_one_shift_insert_bound k x T (Σ : lty_env) :
  lty_env_open_one (S k) x (lty_env_shift (<[LVBound k := T]> Σ)) =
  lty_env_shift (lty_env_open_one k x (<[LVBound k := T]> Σ)).
Proof. apply lvar_store_open_one_shift_insert_bound. Qed.

Lemma lty_env_bvar_scope_shift_open_noop k x (Σ : lty_env) :
  LVBound k ∉ lty_env_bvar_scope (lty_env_shift Σ) ->
  lvars_open k x (lty_env_bvar_scope (lty_env_shift Σ)) =
  lty_env_bvar_scope (lty_env_shift Σ).
Proof. apply lvar_store_bvar_scope_shift_open_noop. Qed.

Lemma lty_env_bvar_scope_shift_open_one_noop k x (Σ : lty_env) :
  LVBound k ∉ lty_env_bvar_scope (lty_env_shift Σ) ->
  LVFree x ∉ dom (lty_env_shift Σ) ->
  lty_env_bvar_scope (lty_env_open_one k x (lty_env_shift Σ)) =
  lty_env_bvar_scope (lty_env_shift Σ).
Proof. apply lvar_store_bvar_scope_shift_open_one_noop. Qed.

Lemma lty_env_bvar_scope_open_one_shift_under_result k x (Σ : lty_env) :
  LVBound (S k) ∉ lty_env_bvar_scope (lty_env_shift Σ) ->
  LVFree x ∉ dom (lty_env_shift Σ) ->
  lty_env_bvar_scope (lty_env_open_one (S k) x (lty_env_shift Σ)) =
  lty_env_bvar_scope (lty_env_shift Σ).
Proof. apply lvar_store_bvar_scope_open_one_shift_under_result. Qed.

Lemma lvars_open_shift_dom_union_bound0 k x (Σ : lty_env) :
  lvars_open (S k) x (lvars_shift_from 0 (dom Σ) ∪ {[LVBound 0]}) =
  lvars_shift_from 0 (lvars_open k x (dom Σ)) ∪ {[LVBound 0]}.
Proof. apply lvar_store_lvars_open_shift_dom_union_bound0. Qed.

Lemma lty_env_atom_dom_open_one k x (Σ : lty_env) :
  lty_env_atom_dom (lty_env_open_one k x Σ) ⊆ lty_env_atom_dom Σ ∪ {[x]}.
Proof. apply lvar_store_atom_dom_open_one. Qed.
