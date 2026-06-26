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
  better_set_solver.
Qed.

Lemma lty_env_closed_insert_free (Σ : lty_env) x T :
  lty_env_closed Σ ->
  lty_env_closed (<[LVFree x := T]> Σ).
Proof. apply lvar_store_closed_insert_free. Qed.

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

Definition tree_node_branch_bound_env (Σ : lty_env) : lty_env :=
  typed_lty_env_bind
    (typed_lty_env_bind
      (typed_lty_env_bind Σ (TBase TTree))
      (TBase TTree))
    (TBase TNat).

Definition tree_node_branch_open_env
    (Σ : lty_env) (root left right : atom) : lty_env :=
  lty_env_open_one 2 right
    (lty_env_open_one 1 left
      (lty_env_open_one 0 root
        (tree_node_branch_bound_env Σ))).

Lemma lty_env_open_one_commute_fresh_eq i j x y (Σ : lty_env) :
  i <> j ->
  x <> y ->
  lty_env_open_one i x (lty_env_open_one j y Σ) =
  lty_env_open_one j y (lty_env_open_one i x Σ).
Proof.
  intros Hij Hxy.
  unfold lty_env_open_one, lvar_store_open_one.
  rewrite (storeA_rekey_compose (logic_var_open i x) (logic_var_open j y)).
  2:{ apply swap_inj. }
  2:{ intros a b Hab. eapply swap_inj. exact Hab. }
  rewrite (storeA_rekey_compose (logic_var_open j y) (logic_var_open i x)).
  2:{ apply swap_inj. }
  2:{ intros a b Hab. eapply swap_inj. exact Hab. }
  apply storeA_rekey_ext_on_dom. intros v _.
  apply logic_var_open_commute_fresh; assumption.
Qed.

Lemma lty_env_open_one_lookup k y (Σ : lty_env) v :
  lty_env_open_one k y Σ !! v = Σ !! logic_var_open k y v.
Proof.
  unfold lty_env_open_one, lvar_store_open_one.
  change ((storeA_rekey (logic_var_open k y) Σ : gmap logic_var ty) !! v =
    Σ !! logic_var_open k y v).
  rewrite <- (logic_var_open_involutive k y v) at 1.
  change ((storeA_rekey (logic_var_open k y) Σ : gmap logic_var ty) !!
    logic_var_open k y (logic_var_open k y v) =
    Σ !! logic_var_open k y v).
  apply storeA_rekey_lookup.
  apply swap_inj.
Qed.

Lemma lty_env_open_one_tree_node_branch_bound_env k y (Σ : lty_env) :
  LVFree y ∉ dom Σ ->
  lty_env_open_one (k + 3) y (tree_node_branch_bound_env Σ) =
  tree_node_branch_bound_env (lty_env_open_one k y Σ).
Proof.
  intros Hy.
  unfold tree_node_branch_bound_env.
  apply lty_env_open_one_under_three_binds. exact Hy.
Qed.

Lemma lty_env_open_one_tree_node_branch_open_env
    k y (Σ : lty_env) root left right :
  y <> root ->
  y <> left ->
  y <> right ->
  LVFree y ∉ dom Σ ->
  lty_env_open_one (k + 3) y
    (tree_node_branch_open_env Σ root left right) =
  tree_node_branch_open_env (lty_env_open_one k y Σ) root left right.
Proof.
  intros Hyroot Hyleft Hyright HyΣ.
  unfold tree_node_branch_open_env.
  rewrite (lty_env_open_one_commute_fresh_eq (k + 3) 2 y right)
    by (lia || congruence).
  rewrite (lty_env_open_one_commute_fresh_eq (k + 3) 1 y left)
    by (lia || congruence).
  rewrite (lty_env_open_one_commute_fresh_eq (k + 3) 0 y root)
    by (lia || congruence).
  rewrite lty_env_open_one_tree_node_branch_bound_env by exact HyΣ.
  reflexivity.
Qed.

Lemma tree_node_branch_open_env_lvars_fv_dom_subset
    (Σ : lty_env) root left right :
  lvars_fv (dom (tree_node_branch_open_env Σ root left right)) ⊆
  lvars_fv (dom Σ) ∪ {[root]} ∪ {[left]} ∪ {[right]}.
Proof.
  intros x Hx.
  unfold tree_node_branch_open_env in Hx.
  rewrite !lty_env_open_one_dom in Hx.
  apply lvars_fv_open_subset in Hx.
  apply elem_of_union in Hx as [Hx|Hx]; [|set_solver].
  apply lvars_fv_open_subset in Hx.
  apply elem_of_union in Hx as [Hx|Hx]; [|set_solver].
  apply lvars_fv_open_subset in Hx.
  apply elem_of_union in Hx as [Hx|Hx]; [|set_solver].
  unfold tree_node_branch_bound_env in Hx.
  rewrite !typed_lty_env_bind_lvars_fv_dom in Hx.
  set_solver.
Qed.

Lemma tree_node_branch_bound_env_lookup_free (Σ : lty_env) x :
  tree_node_branch_bound_env Σ !! LVFree x = Σ !! LVFree x.
Proof.
  unfold tree_node_branch_bound_env.
  rewrite !typed_lty_env_bind_lookup_free. reflexivity.
Qed.

Lemma tree_node_branch_bound_env_lookup_bound0 (Σ : lty_env) :
  tree_node_branch_bound_env Σ !! LVBound 0 = Some (TBase TNat).
Proof.
  unfold tree_node_branch_bound_env, typed_lty_env_bind, lvar_store_bind.
  rewrite lookup_insert_eq. reflexivity.
Qed.

Lemma lty_env_shift_lookup_bound_succ (Σ : lty_env) k :
  lty_env_shift Σ !! LVBound (S k) = Σ !! LVBound k.
Proof.
  unfold lty_env_shift, lvar_store_shift, lvar_store_shift_from.
  change ((storeA_rekey (logic_var_shift_from 0) Σ
    : gmap logic_var ty) !! logic_var_shift_from 0 (LVBound k) =
    Σ !! LVBound k).
  apply storeA_rekey_lookup.
  apply logic_var_shift_from_inj.
Qed.

Lemma tree_node_branch_bound_env_lookup_bound1 (Σ : lty_env) :
  tree_node_branch_bound_env Σ !! LVBound 1 = Some (TBase TTree).
Proof.
  unfold tree_node_branch_bound_env, typed_lty_env_bind, lvar_store_bind.
  rewrite lookup_insert_ne by discriminate.
  rewrite lty_env_shift_lookup_bound_succ.
  rewrite lookup_insert_eq. reflexivity.
Qed.

Lemma tree_node_branch_bound_env_lookup_bound2 (Σ : lty_env) :
  tree_node_branch_bound_env Σ !! LVBound 2 = Some (TBase TTree).
Proof.
  unfold tree_node_branch_bound_env, typed_lty_env_bind, lvar_store_bind.
  rewrite lookup_insert_ne by discriminate.
  rewrite lty_env_shift_lookup_bound_succ.
  rewrite lookup_insert_ne by discriminate.
  rewrite lty_env_shift_lookup_bound_succ.
  rewrite lookup_insert_eq. reflexivity.
Qed.

Lemma tree_node_branch_bound_env_lookup_bound_ge3 (Σ : lty_env) k :
  tree_node_branch_bound_env Σ !! LVBound (S (S (S k))) =
  Σ !! LVBound k.
Proof.
  unfold tree_node_branch_bound_env, typed_lty_env_bind, lvar_store_bind.
  rewrite lookup_insert_ne by discriminate.
  rewrite lty_env_shift_lookup_bound_succ.
  rewrite lookup_insert_ne by discriminate.
  rewrite lty_env_shift_lookup_bound_succ.
  rewrite lookup_insert_ne by discriminate.
  rewrite lty_env_shift_lookup_bound_succ.
  reflexivity.
Qed.

Lemma tree_node_branch_open_env_lookup_bound_none
    (Σ : lty_env) root left right k :
  lty_env_closed Σ ->
  LVFree root ∉ dom Σ ->
  LVFree left ∉ dom Σ ->
  LVFree right ∉ dom Σ ->
  root <> left ->
  root <> right ->
  left <> right ->
  tree_node_branch_open_env Σ root left right !! LVBound k = None.
Proof.
  intros Hclosed Hroot Hleft Hright Hroot_left Hroot_right Hleft_right.
  unfold tree_node_branch_open_env.
  destruct k as [|[|[|k]]];
    rewrite !lty_env_open_one_lookup.
  - replace (logic_var_open 2 right (LVBound 0)) with (LVBound 0)
      by better_base_solver.
    replace (logic_var_open 1 left (LVBound 0)) with (LVBound 0)
      by better_base_solver.
    replace (logic_var_open 0 root (LVBound 0)) with (LVFree root)
      by better_base_solver.
    rewrite tree_node_branch_bound_env_lookup_free.
    apply not_elem_of_dom. exact Hroot.
  - replace (logic_var_open 2 right (LVBound 1)) with (LVBound 1)
      by better_base_solver.
    replace (logic_var_open 1 left (LVBound 1)) with (LVFree left)
      by better_base_solver.
    replace (logic_var_open 0 root (LVFree left)) with (LVFree left)
      by better_base_solver.
    rewrite tree_node_branch_bound_env_lookup_free.
    apply not_elem_of_dom. exact Hleft.
  - replace (logic_var_open 2 right (LVBound 2)) with (LVFree right)
      by better_base_solver.
    replace (logic_var_open 1 left (LVFree right)) with (LVFree right)
      by better_base_solver.
    replace (logic_var_open 0 root (LVFree right)) with (LVFree right)
      by better_base_solver.
    rewrite tree_node_branch_bound_env_lookup_free.
    apply not_elem_of_dom. exact Hright.
  - replace (logic_var_open 2 right (LVBound (S (S (S k)))))
      with (LVBound (S (S (S k)))) by better_base_solver.
    replace (logic_var_open 1 left (LVBound (S (S (S k)))))
      with (LVBound (S (S (S k)))) by better_base_solver.
    replace (logic_var_open 0 root (LVBound (S (S (S k)))))
      with (LVBound (S (S (S k)))) by better_base_solver.
    rewrite tree_node_branch_bound_env_lookup_bound_ge3.
    apply lty_env_closed_lookup_bound_none. exact Hclosed.
Qed.

Lemma tree_node_branch_open_env_lookup_free
    (Σ : lty_env) root left right z :
  root <> left ->
  root <> right ->
  left <> right ->
  tree_node_branch_open_env Σ root left right !! LVFree z =
  (<[LVFree right := TBase TTree]>
    (<[LVFree left := TBase TTree]>
      (<[LVFree root := TBase TNat]> Σ))) !! LVFree z.
Proof.
  intros Hroot_left Hroot_right Hleft_right.
  unfold tree_node_branch_open_env.
  rewrite !lty_env_open_one_lookup.
  destruct (decide (z = right)) as [->|Hzr].
  - replace (logic_var_open 2 right (LVFree right)) with (LVBound 2)
      by better_base_solver.
    replace (logic_var_open 1 left (LVBound 2)) with (LVBound 2)
      by better_base_solver.
    replace (logic_var_open 0 root (LVBound 2)) with (LVBound 2)
      by better_base_solver.
    rewrite tree_node_branch_bound_env_lookup_bound2.
    rewrite lookup_insert_eq. reflexivity.
  - rewrite lookup_insert_ne by (intros Heq; inversion Heq; congruence).
    destruct (decide (z = left)) as [->|Hzl].
    + replace (logic_var_open 2 right (LVFree left)) with (LVFree left)
        by better_base_solver.
      replace (logic_var_open 1 left (LVFree left)) with (LVBound 1)
        by better_base_solver.
      replace (logic_var_open 0 root (LVBound 1)) with (LVBound 1)
        by better_base_solver.
      rewrite tree_node_branch_bound_env_lookup_bound1.
      rewrite lookup_insert_eq. reflexivity.
    + rewrite lookup_insert_ne by (intros Heq; inversion Heq; congruence).
      destruct (decide (z = root)) as [->|Hzroot].
      * replace (logic_var_open 2 right (LVFree root)) with (LVFree root)
          by better_base_solver.
        replace (logic_var_open 1 left (LVFree root)) with (LVFree root)
          by better_base_solver.
        replace (logic_var_open 0 root (LVFree root)) with (LVBound 0)
          by better_base_solver.
        rewrite tree_node_branch_bound_env_lookup_bound0.
        rewrite lookup_insert_eq. reflexivity.
      * rewrite lookup_insert_ne by (intros Heq; inversion Heq; congruence).
        replace (logic_var_open 2 right (LVFree z)) with (LVFree z)
          by better_base_solver.
        replace (logic_var_open 1 left (LVFree z)) with (LVFree z)
          by better_base_solver.
        replace (logic_var_open 0 root (LVFree z)) with (LVFree z)
          by better_base_solver.
        rewrite tree_node_branch_bound_env_lookup_free.
        reflexivity.
Qed.

Lemma tree_node_branch_open_env_lc_dom
    (Σ : lty_env) root left right :
  lc_lvars (dom Σ) ->
  root ∉ lvars_fv (dom Σ) ->
  left ∉ lvars_fv (dom Σ) ->
  right ∉ lvars_fv (dom Σ) ->
  root <> left ->
  root <> right ->
  left <> right ->
  lc_lvars (dom (tree_node_branch_open_env Σ root left right)).
Proof.
  intros Hlc Hroot Hleft Hright Hroot_left Hroot_right Hleft_right
    [k|x] Hin; [|exact I].
  exfalso.
  apply elem_of_dom in Hin as [T Hlook].
  rewrite (tree_node_branch_open_env_lookup_bound_none
    Σ root left right k) in Hlook; [discriminate|..].
  - exact Hlc.
  - intros Hdom. apply Hroot. apply lvars_fv_elem. exact Hdom.
  - intros Hdom. apply Hleft. apply lvars_fv_elem. exact Hdom.
  - intros Hdom. apply Hright. apply lvars_fv_elem. exact Hdom.
  - exact Hroot_left.
  - exact Hroot_right.
  - exact Hleft_right.
Qed.

Lemma tree_node_branch_open_env_norm
    (Σ : lty_env) root left right :
  lty_env_closed Σ ->
  LVFree root ∉ dom Σ ->
  LVFree left ∉ dom Σ ->
  LVFree right ∉ dom Σ ->
  root <> left ->
  root <> right ->
  left <> right ->
  tree_node_branch_open_env Σ root left right =
  <[LVFree right := TBase TTree]>
    (<[LVFree left := TBase TTree]>
      (<[LVFree root := TBase TNat]> Σ)).
Proof.
  intros Hclosed Hroot Hleft Hright Hroot_left Hroot_right Hleft_right.
  apply map_eq. intros [k|z].
  - rewrite (tree_node_branch_open_env_lookup_bound_none
      Σ root left right k); [|eassumption..].
    rewrite !lookup_insert_ne by discriminate.
    symmetry. apply lty_env_closed_lookup_bound_none. exact Hclosed.
  - unfold tree_node_branch_open_env.
    rewrite !lty_env_open_one_lookup.
    destruct (decide (z = right)) as [->|Hzright].
    + replace (logic_var_open 2 right (LVFree right)) with (LVBound 2)
        by better_base_solver.
      replace (logic_var_open 1 left (LVBound 2)) with (LVBound 2)
        by better_base_solver.
      replace (logic_var_open 0 root (LVBound 2)) with (LVBound 2)
        by better_base_solver.
      rewrite tree_node_branch_bound_env_lookup_bound2.
      rewrite lookup_insert_eq. reflexivity.
    + replace (logic_var_open 2 right (LVFree z)) with (LVFree z)
        by better_base_solver.
      destruct (decide (z = left)) as [->|Hzleft].
      * replace (logic_var_open 1 left (LVFree left)) with (LVBound 1)
          by better_base_solver.
        replace (logic_var_open 0 root (LVBound 1)) with (LVBound 1)
          by better_base_solver.
        rewrite tree_node_branch_bound_env_lookup_bound1.
        rewrite lookup_insert_ne by (intros Heq; inversion Heq; congruence).
        rewrite lookup_insert_eq. reflexivity.
      * replace (logic_var_open 1 left (LVFree z)) with (LVFree z)
          by better_base_solver.
        destruct (decide (z = root)) as [->|Hzroot].
        -- replace (logic_var_open 0 root (LVFree root)) with (LVBound 0)
             by better_base_solver.
           rewrite tree_node_branch_bound_env_lookup_bound0.
           rewrite lookup_insert_ne by (intros Heq; inversion Heq; congruence).
           rewrite lookup_insert_ne by (intros Heq; inversion Heq; congruence).
           rewrite lookup_insert_eq. reflexivity.
        -- replace (logic_var_open 0 root (LVFree z)) with (LVFree z)
             by better_base_solver.
           rewrite tree_node_branch_bound_env_lookup_free.
           rewrite lookup_insert_ne by (intros Heq; inversion Heq; congruence).
           rewrite lookup_insert_ne by (intros Heq; inversion Heq; congruence).
           rewrite lookup_insert_ne by (intros Heq; inversion Heq; congruence).
           reflexivity.
Qed.

Lemma typed_lty_env_bind_open_env_lift η (Σ : lty_env) T :
  open_env_fresh_for_lvars η (dom Σ) ->
  lty_env_open_lvars ((kmap S η)) (typed_lty_env_bind Σ T) =
  typed_lty_env_bind (lty_env_open_lvars η Σ) T.
Proof. apply lvar_store_bind_open_env_lift. Qed.
