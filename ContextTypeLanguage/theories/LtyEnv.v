(** * ContextTypeLanguage.LtyEnv

    Type-language names and laws for ty-valued lvar stores. *)

From LocallyNameless Require Import Classes.
From ContextStore Require Export Store.
From ContextTypeLanguage Require Export TypeOpen.

(** * ContextTypeLanguage.LtyEnv

    Thin TypeLanguage names for [ty]-valued lvar stores.  The operations and
    laws live in [ContextStore]; this file only fixes the value type and
    provides the TypeLanguage instances used by opening notation. *)


Notation lty_env := (gmap logic_var ty) (only parsing).
Local Notation StoreT := (Store (V := value)) (only parsing).

Bind Scope lvar_scope with lty_env.

Notation lty_env_shift_from :=
  (@lvar_store_shift_from ty) (only parsing).
Notation lty_env_shift :=
  (@lvar_store_shift ty) (only parsing).
Notation lty_env_open_one :=
  (@lvar_store_open_one ty) (only parsing).
Notation lty_env_closed :=
  (@lvar_store_closed ty) (only parsing).
Notation atom_env_to_lty_env :=
  (@atom_store_to_lvar_store ty) (only parsing).
Notation lty_env_open :=
  (@lvar_store_open ty) (only parsing).
Notation lty_env_to_atom_env :=
  (@lvar_store_to_atom_store ty) (only parsing).
Notation lty_env_open_lvars :=
  (@lvar_store_open_lvars ty) (only parsing).
Notation lty_env_atom_dom :=
  (@lvar_store_atom_dom ty) (only parsing).
Notation lty_env_bvar_scope :=
  (@lvar_store_bvar_scope ty) (only parsing).
Notation lty_env_swap :=
  (@lvar_store_swap ty) (only parsing).

Notation typed_lty_env_bind :=
  (@lvar_store_bind ty) (only parsing).

Notation "'↑ₗ' Σ" := (atom_env_to_lty_env Σ)
  (at level 20, format "↑ₗ Σ").

Notation "'↑ₗ' Σ" := (atom_env_to_lty_env Σ)
  (at level 20, only parsing) : ctx_scope.

Definition lty_env_msubst_store (σ : StoreT) (Σ : lty_env) : lty_env :=
  storeA_restrict Σ (dom Σ ∖ lvars_of_atoms (dom (σ : gmap atom value))).

#[global] Instance stale_lty_env : Stale lty_env := lvar_store_atom_dom.
Arguments stale_lty_env /.

#[global] Instance open_lty_env_atom_inst : Open atom lty_env :=
  lvar_store_open_one.

#[global] Instance mopen_lty_env_inst :
  MOpen (gmap nat atom) lty_env (gmap atom ty) := lvar_store_open.

#[global] Instance into_lvars_atom_ty_env : IntoLVars (gmap atom ty) :=
  fun Σ => lvars_of_atoms (dom Σ).

#[global] Instance into_lvars_logic_ty_env : IntoLVars (gmap logic_var ty) :=
  fun Σ => dom Σ.

(** * ContextTypeLanguage.LtyEnv

    Type-language compatibility names for generic lvar-store opening laws. *)


Lemma lty_env_msubst_store_lookup_some σ (Σ : lty_env) v T :
  lty_env_msubst_store σ Σ !! v = Some T ->
  Σ !! v = Some T /\ v ∉ lvars_of_atoms (dom (σ : gmap atom value)).
Proof.
  intros Hlook.
  unfold lty_env_msubst_store in Hlook.
  pose proof (storeA_restrict_lookup_some
    Σ (dom Σ ∖ lvars_of_atoms (dom (σ : gmap atom value))) v T Hlook)
    as [Hin HΣ].
  apply elem_of_difference in Hin as [_ Hfresh].
  split; assumption.
Qed.

Ltac type_env_norm :=
  type_open_env_syntax_norm;
  rewrite ?lvar_store_atom_dom_shift in *.

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

Lemma lty_env_open_lvars_dom η (Σ : lty_env) :
  open_env_fresh_for_lvars η (dom Σ) ->
  dom (lty_env_open_lvars η Σ) =
  lvars_open_env η (dom Σ).
Proof. apply lvar_store_open_lvars_dom. Qed.

Lemma lty_env_open_lvars_insert_fresh η k x (Σ : lty_env) :
  η !! k = None ->
  open_env_avoids_atom x η ->
  open_env_fresh_for_lvars (<[k := x]> η) (dom Σ) ->
  lty_env_open_lvars (<[k := x]> η) Σ =
  lty_env_open_one k x (lty_env_open_lvars η Σ).
Proof. apply lvar_store_open_lvars_insert_fresh. Qed.

Lemma lty_env_open_lvars_lift_bound0_singleton η T :
  open_env_values_inj η ->
  lty_env_open_lvars ((kmap S η))
    ((<[LVBound 0 := T]> (∅ : gmap logic_var ty)) : lty_env) =
  ((<[LVBound 0 := T]> (∅ : gmap logic_var ty)) : lty_env).
Proof.
  induction η as [|k x η Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - intros _. rewrite kmap_empty, lty_env_open_lvars_empty. reflexivity.
  - intros Hinj.
    pose proof (open_env_values_inj_insert_inv η k x Hfresh Hinj)
      as [Hinjη Havoid].
    rewrite open_env_lift_insert.
    rewrite lty_env_open_lvars_insert_fresh.
    + rewrite IH by exact Hinjη.
      rewrite lvar_store_open_one_insert.
      replace (logic_var_open (S k) x (LVBound 0)) with (LVBound 0).
      * replace (lty_env_open_one (S k) x (∅ : lty_env)) with
          ((∅ : gmap logic_var ty) : lty_env); [reflexivity|].
        unfold lty_env_open_one.
        apply (storeA_rekey_empty (V := ty) (K := logic_var)
          (logic_var_open (S k) x)).
      * unfold swap. repeat destruct decide; try lia; try congruence.
    + better_base_solver.
    + better_base_solver.
    + intros i z Hiz Hbad.
      replace (dom (<[LVBound 0 := T]> (∅ : gmap logic_var ty)) : lvset)
        with ({[LVBound 0]} : lvset) in Hbad
        by (rewrite dom_insert_L, dom_empty_L; set_solver).
      apply lvars_fv_elem in Hbad.
      unfold lvars_open_env in Hbad.
      apply elem_of_map in Hbad as [v [Hv HvIn]].
      assert (Hv0 : v = LVBound 0) by set_solver.
      subst v.
      cbn [logic_var_open_env] in Hv.
      assert (Hnone :
        delete i (<[S k:=x]> (kmap S η : gmap nat atom)) !! 0 = None).
      {
        destruct (decide (i = 0)) as [->|Hi0].
        - rewrite lookup_delete_eq. reflexivity.
        - rewrite lookup_delete_ne by congruence.
          change ((<[S k:=x]> ((kmap S η)) : gmap nat atom) !! 0 = None).
          destruct (decide (0 = S k)) as [Hbad0|Hneq0]; [lia|].
          rewrite lookup_insert_ne by (intros H; apply Hneq0; symmetry; exact H).
          apply open_env_lift_lookup_zero_none.
      }
      rewrite Hnone in Hv. discriminate.
Qed.

(** * ContextTypeLanguage.LtyEnv

    Type-language compatibility names for generic lvar-store binder laws. *)


Lemma typed_lty_env_bind_dom (Σ : lty_env) T :
  dom (typed_lty_env_bind Σ T) =
  lvars_shift_from 0 (dom Σ) ∪ {[LVBound 0]}.
Proof. apply lvar_store_bind_dom. Qed.

Lemma typed_lty_env_bind_lookup_free (Σ : lty_env) T x :
  typed_lty_env_bind Σ T !! LVFree x = Σ !! LVFree x.
Proof.
  unfold typed_lty_env_bind, lvar_store_bind.
  rewrite lookup_insert_ne by discriminate.
  unfold lvar_store_shift, lvar_store_shift_from.
  change ((storeA_rekey (logic_var_shift_from 0) Σ
    : gmap logic_var ty) !! logic_var_shift_from 0 (LVFree x) =
    Σ !! LVFree x).
  apply storeA_rekey_lookup.
  apply logic_var_shift_from_inj.
Qed.


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

Lemma lty_env_closed_insert_free (Σ : lty_env) x T :
  lty_env_closed Σ ->
  lty_env_closed (<[LVFree x := T]> Σ).
Proof. apply lvar_store_closed_insert_free. Qed.

Lemma lty_env_insert_free_fresh
    (Σ : lty_env) x z T :
  z <> x ->
  LVFree z ∉ dom Σ ->
  LVFree z ∉ dom (<[LVFree x := T]> Σ).
Proof.
  intros Hzx HzΣ.
  rewrite dom_insert_L.
  intros Hin.
  apply elem_of_union in Hin as [Hin|Hin].
  - apply elem_of_singleton in Hin. inversion Hin. subst.
    contradiction.
  - exact (HzΣ Hin).
Qed.

Lemma lty_env_insert_free_commute
    (Σ : lty_env) x y Tx Ty :
  x <> y ->
  <[LVFree x := Tx]> (<[LVFree y := Ty]> Σ) =
  <[LVFree y := Ty]> (<[LVFree x := Tx]> Σ).
Proof.
  intros Hxy.
  apply map_eq. intros u.
  destruct (decide (u = LVFree x)) as [->|Hux].
  - rewrite lookup_insert_eq.
    rewrite lookup_insert_ne by congruence.
    rewrite lookup_insert_eq. reflexivity.
  - destruct (decide (u = LVFree y)) as [->|Huy].
    + rewrite lookup_insert_ne by congruence.
      rewrite !lookup_insert_eq. reflexivity.
    + rewrite !lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma lty_env_closed_lookup_bound_none (Σ : lty_env) k :
  lty_env_closed Σ ->
  Σ !! LVBound k = None.
Proof. apply lvar_store_closed_lookup_bound_none. Qed.

Lemma typed_lty_env_bind_open_current y (Σ : lty_env) T :
  LVFree y ∉ dom Σ ->
  lty_env_closed Σ ->
  lty_env_open_one 0 y (typed_lty_env_bind Σ T) =
  <[LVFree y := T]> Σ.
Proof. apply lvar_store_bind_open_current. Qed.

Lemma lty_env_open_one_under_three_binds k y (Σ : lty_env) T0 T1 T2 :
  LVFree y ∉ dom Σ ->
  lty_env_open_one (k + 3) y
    (typed_lty_env_bind
      (typed_lty_env_bind
        (typed_lty_env_bind Σ T0) T1) T2) =
  typed_lty_env_bind
    (typed_lty_env_bind
      (typed_lty_env_bind (lty_env_open_one k y Σ) T0) T1) T2.
Proof. apply lvar_store_open_one_under_three_binds. Qed.

Lemma typed_lty_env_bind_open_env_lift η (Σ : lty_env) T :
  open_env_fresh_for_lvars η (dom Σ) ->
  lty_env_open_lvars ((kmap S η)) (typed_lty_env_bind Σ T) =
  typed_lty_env_bind (lty_env_open_lvars η Σ) T.
Proof. apply lvar_store_bind_open_env_lift. Qed.
