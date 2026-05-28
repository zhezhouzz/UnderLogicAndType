(** * ContextTypeLanguage.LtyEnvOpen

    Same-key opening and bound-variable scope laws for lvar-keyed type
    environments. *)

From LocallyNameless Require Import Classes.
From ContextTypeLanguage Require Export LtyEnvCore.

Lemma lty_env_open_one_dom k x Σ :
  dom (lty_env_open_one k x Σ) = lvars_open k x (dom Σ).
Proof.
  unfold lty_env_open_one.
  change (dom (storeA_rekey (logic_var_open k x) Σ : gmap logic_var ty) =
    lvars_open k x (dom (Σ : gmap logic_var ty))).
  rewrite storeA_rekey_dom by (intros a b H; eapply logic_var_open_inj_fresh; exact H).
  rewrite lvars_open_unfold.
  unfold set_swap.
  apply set_eq. intros v.
  rewrite !elem_of_map.
  split.
  - intros [u [Hu HuD]]. exists u. split; [|exact HuD].
    rewrite <- logic_var_open_unfold. exact Hu.
  - intros [u [Hu HuD]]. exists u. split; [|exact HuD].
    rewrite logic_var_open_unfold. exact Hu.
Qed.

Lemma lty_env_open_lvars_empty Σ :
  lty_env_open_lvars ∅ Σ = Σ.
Proof.
  unfold lty_env_open_lvars.
  apply storeA_map_eq. intros v.
  unfold storeA_rekey, storeA_map_key.
  change ((kmap (M2:=gmap logic_var) (logic_var_open_env ∅) Σ) !! v =
    (Σ : gmap logic_var ty) !! v).
  rewrite <- (logic_var_open_env_empty v) at 1.
  rewrite (lookup_kmap (M1:=gmap logic_var) (M2:=gmap logic_var)
    (Inj0:=fun a b H => ltac:(rewrite !logic_var_open_env_empty in H; exact H))
    (logic_var_open_env ∅) Σ v).
  reflexivity.
Qed.

Lemma lty_env_open_lvars_singleton k x Σ :
  LVFree x ∉ dom Σ ->
  lty_env_open_lvars (<[k := x]> ∅) Σ =
  lty_env_open_one k x Σ.
Proof.
  intros Hfresh.
  unfold lty_env_open_lvars, lty_env_open_one.
  apply storeA_rekey_ext_on_dom. intros v Hv.
  apply logic_var_open_env_singleton_fresh.
  intros ->. apply Hfresh. exact Hv.
Qed.

Lemma lty_env_open_lvars_open_one_empty k x Σ :
  LVFree x ∉ dom Σ ->
  lty_env_open_lvars ∅ (lty_env_open_one k x Σ) =
  lty_env_open_lvars (<[k := x]> ∅) Σ.
Proof.
  intros Hfresh.
  rewrite lty_env_open_lvars_empty.
  symmetry. apply lty_env_open_lvars_singleton. exact Hfresh.
Qed.

Lemma lty_env_open_lvars_dom η Σ :
  open_env_fresh_for_lvars η (dom Σ) ->
  dom (lty_env_open_lvars η Σ) =
  lvars_open_env_simul η (dom Σ).
Proof.
  intros Hfresh.
  unfold lty_env_open_lvars, lvars_open_env_simul, lvars_open_env.
  change (dom (storeA_rekey (logic_var_open_env η) Σ : gmap logic_var ty) =
    set_map (logic_var_open_env η) (dom (Σ : gmap logic_var ty))).
  apply storeA_rekey_dom_inj_on.
  apply open_env_fresh_for_lvars_inj_on. exact Hfresh.
Qed.

Lemma lty_env_open_lvars_lookup_fresh η v T Σ :
  Σ !! v = None ->
  open_env_fresh_for_lvars η (dom (<[v := T]> Σ)) ->
  lty_env_open_lvars η Σ !! logic_var_open_env η v = None.
Proof.
  intros Hnone Hfresh.
  unfold lty_env_open_lvars.
  change ((storeA_rekey (logic_var_open_env η) Σ : gmap logic_var ty) !!
    logic_var_open_env η v = None).
  apply storeA_rekey_lookup_none_inj_on.
  - exact Hnone.
  - intros y Hy Heq.
    assert (Hinj := open_env_fresh_for_lvars_inj_on η
      (dom (<[v := T]> Σ)) Hfresh).
    assert (HyD : y ∈ dom (<[v := T]> (Σ : gmap logic_var ty))).
    { rewrite dom_insert_L. apply elem_of_union_r. exact Hy. }
    assert (HvD : v ∈ dom (<[v := T]> (Σ : gmap logic_var ty))).
    { rewrite dom_insert_L. apply elem_of_union_l. apply elem_of_singleton. reflexivity. }
    pose proof (Hinj y v HyD HvD Heq) as ->.
    apply elem_of_dom in Hy as [U Hy].
    change ((Σ : gmap logic_var ty) !! v = None) in Hnone.
    rewrite Hnone in Hy. discriminate.
Qed.

Lemma lty_env_open_lvars_insert_entry η v T Σ :
  Σ !! v = None ->
  logic_var_open_env_inj_on η (dom (<[v := T]> Σ)) ->
  lty_env_open_lvars η (<[v := T]> Σ) =
  <[logic_var_open_env η v := T]> (lty_env_open_lvars η Σ).
Proof.
  intros Hnone Hinj.
  unfold lty_env_open_lvars.
  apply storeA_rekey_insert_inj_on; exact Hnone || exact Hinj.
Qed.

Lemma lty_env_open_lvars_insert_fresh η k x Σ :
  η !! k = None ->
  open_env_avoids_atom x η ->
  open_env_fresh_for_lvars (<[k := x]> η) (dom Σ) ->
  lty_env_open_lvars (<[k := x]> η) Σ =
  lty_env_open_one k x (lty_env_open_lvars η Σ).
Proof.
  intros Hη Havoid Hfresh.
  unfold lty_env_open_lvars, lty_env_open_one.
  assert (Hfreshη : open_env_fresh_for_lvars η (dom Σ)).
  { eapply open_env_fresh_for_lvars_insert_tail; eassumption. }
  assert (Hhead : x ∉ lvars_fv (lvars_open_env η (dom Σ))).
  { eapply open_env_fresh_for_lvars_insert_head; eassumption. }
  rewrite storeA_rekey_compose_inj_on.
  2:{ apply open_env_fresh_for_lvars_inj_on. exact Hfreshη. }
  2:{ intros a b _ _ Hab. eapply logic_var_open_inj_fresh. exact Hab. }
  apply storeA_rekey_ext_on_dom. intros v Hv.
  rewrite <- logic_var_open_env_open_fresh by eassumption.
  symmetry. apply logic_var_open_env_open_one_fresh.
  intros ->. apply Hhead. apply lvars_fv_open_env_free. exact Hv.
Qed.

Lemma lty_env_open_lvars_open_one η k x Σ :
  x ∉ lvars_fv (dom Σ) ->
  open_env_fresh_for_lvars η (dom (lty_env_open_one k x Σ)) ->
  lty_env_open_lvars η (lty_env_open_one k x Σ) =
  lty_env_open_lvars (<[k := x]> η) Σ.
Proof.
  intros Hx Hfresh.
  unfold lty_env_open_lvars, lty_env_open_one.
  rewrite storeA_rekey_compose_inj_on.
  2:{ intros a b _ _ Hab. eapply logic_var_open_inj_fresh. exact Hab. }
  2:{
    apply open_env_fresh_for_lvars_inj_on. exact Hfresh.
  }
  apply storeA_rekey_ext_on_dom. intros v Hv.
  apply logic_var_open_env_open_one_fresh.
  intros ->. apply Hx. apply lvars_fv_elem. exact Hv.
Qed.

Lemma logic_var_bv_elem_singleton v k :
  k ∈ lvars_bv ({[v]} : lvset) <-> v = LVBound k.
Proof.
  rewrite lvars_bv_elem, elem_of_singleton.
  split; intros H; [symmetry|symmetry]; exact H.
Qed.

Lemma logic_var_open_fresh_noop k x v :
  LVBound k <> v ->
  LVFree x <> v ->
  logic_var_open k x v = v.
Proof.
  intros Hk Hx.
  rewrite logic_var_open_unfold.
  apply swap_fresh; congruence.
Qed.

Lemma lty_env_open_one_fresh_noop k x Σ :
  LVBound k ∉ dom Σ ->
  LVFree x ∉ dom Σ ->
  lty_env_open_one k x Σ = Σ.
Proof.
  intros Hk Hx.
  unfold lty_env_open_one.
  change (storeA_swap (LVBound k) (LVFree x) Σ = Σ).
  apply storeA_swap_fresh; assumption.
Qed.

Lemma lty_env_open_one_involutive k x Σ :
  lty_env_open_one k x (lty_env_open_one k x Σ) = Σ.
Proof.
  unfold lty_env_open_one.
  change (storeA_swap (LVBound k) (LVFree x)
    (storeA_swap (LVBound k) (LVFree x) Σ) = Σ).
  apply storeA_swap_involutive.
Qed.

Lemma lty_env_open_one_insert k x v T Σ :
  lty_env_open_one k x (<[v := T]> Σ) =
  <[logic_var_open k x v := T]> (lty_env_open_one k x Σ).
Proof.
  unfold lty_env_open_one.
  apply storeA_rekey_insert.
  intros a b H. eapply logic_var_open_inj_fresh. exact H.
Qed.

Lemma lty_env_open_one_insert_fresh k x v T Σ :
  logic_var_open k x v ∉ dom (lty_env_open_one k x Σ) ->
  lty_env_open_one k x (<[v := T]> Σ) =
  <[logic_var_open k x v := T]> (lty_env_open_one k x Σ).
Proof.
  intros _. apply lty_env_open_one_insert.
Qed.

Lemma lty_env_open_one_shift_under_gen j k x Σ :
  j <= k ->
  lty_env_open_one (S k) x (lty_env_shift_from j Σ) =
  lty_env_shift_from j (lty_env_open_one k x Σ).
Proof.
  intros Hjk.
  apply storeA_map_eq. intros v.
  unfold lty_env_open_one, lty_env_shift_from.
  change ((storeA_rekey (logic_var_open (S k) x)
      (storeA_rekey (logic_var_shift_from j) Σ) : gmap logic_var ty) !! v =
    (storeA_rekey (logic_var_shift_from j)
      (storeA_rekey (logic_var_open k x) Σ) : gmap logic_var ty) !! v).
  destruct (decide (v ∈ dom (storeA_rekey (logic_var_open (S k) x)
      (storeA_rekey (logic_var_shift_from j) Σ) : gmap logic_var ty))) as [Hv|Hv].
  - rewrite storeA_rekey_dom in Hv by
      (intros a b H; eapply logic_var_open_inj_fresh; exact H).
    apply elem_of_map in Hv as [u [-> Hu]].
    rewrite storeA_rekey_dom in Hu by apply logic_var_shift_from_inj.
    apply elem_of_map in Hu as [w [-> Hw]].
    unfold storeA_rekey, storeA_map_key.
    change ((kmap (M2:=gmap logic_var) (logic_var_open (S k) x)
        (kmap (M2:=gmap logic_var) (logic_var_shift_from j) Σ) !!
        logic_var_open (S k) x (logic_var_shift_from j w)) =
      (kmap (M2:=gmap logic_var) (logic_var_shift_from j)
        (kmap (M2:=gmap logic_var) (logic_var_open k x) Σ) !!
        logic_var_open (S k) x (logic_var_shift_from j w))).
    rewrite (lookup_kmap (M1:=gmap logic_var) (M2:=gmap logic_var)
      (Inj0:=fun a b H => ltac:(eapply logic_var_open_inj_fresh; exact H))
      (logic_var_open (S k) x)
      (kmap (M2:=gmap logic_var) (logic_var_shift_from j) Σ)
      (logic_var_shift_from j w)).
    rewrite (lookup_kmap (M1:=gmap logic_var) (M2:=gmap logic_var)
      (Inj0:=logic_var_shift_from_inj j)
      (logic_var_shift_from j) Σ w).
    rewrite logic_var_open_shift_from_under_gen by exact Hjk.
    rewrite (lookup_kmap (M1:=gmap logic_var) (M2:=gmap logic_var)
      (Inj0:=logic_var_shift_from_inj j)
      (logic_var_shift_from j)
      (kmap (M2:=gmap logic_var) (logic_var_open k x) Σ)
      (logic_var_open k x w)).
    rewrite (lookup_kmap (M1:=gmap logic_var) (M2:=gmap logic_var)
      (Inj0:=fun a b H => ltac:(eapply logic_var_open_inj_fresh; exact H))
      (logic_var_open k x) Σ w).
    reflexivity.
  - transitivity (@None ty).
    + apply not_elem_of_dom. exact Hv.
    + symmetry. apply not_elem_of_dom. intros Hr.
      apply Hv.
      rewrite storeA_rekey_dom by
        (intros a b H; eapply logic_var_open_inj_fresh; exact H).
      rewrite storeA_rekey_dom in Hr by apply logic_var_shift_from_inj.
      apply elem_of_map in Hr as [u [-> Hu]].
      rewrite storeA_rekey_dom in Hu by
        (intros a b H; eapply logic_var_open_inj_fresh; exact H).
      apply elem_of_map in Hu as [w [-> Hw]].
      apply elem_of_map. exists (logic_var_shift_from j w).
      split.
      * symmetry. apply logic_var_open_shift_from_under_gen. exact Hjk.
      * rewrite storeA_rekey_dom by apply logic_var_shift_from_inj.
        apply elem_of_map. exists w. split; [reflexivity|exact Hw].
Qed.

Lemma lty_env_open_one_shift_under j k x Σ :
  j <= k ->
  lty_env_open_one (S (S k)) x (lty_env_shift_from (S j) Σ) =
  lty_env_shift_from (S j) (lty_env_open_one (S k) x Σ).
Proof.
  intros Hjk. apply lty_env_open_one_shift_under_gen. lia.
Qed.

Lemma lvars_open_shift_dom_gen j k x (Σ : lty_env) :
  j <= k ->
  lvars_open (S k) x (lvars_shift_from j (dom Σ)) =
  lvars_shift_from j (lvars_open k x (dom Σ)).
Proof.
  apply lvars_open_shift_from_under_gen.
Qed.

Lemma lvars_open_shift_dom j k x (Σ : lty_env) :
  j <= k ->
  lvars_open (S (S k)) x (lvars_shift_from (S j) (dom Σ)) =
  lvars_shift_from (S j) (lvars_open (S k) x (dom Σ)).
Proof.
  intros Hjk. apply lvars_open_shift_dom_gen. lia.
Qed.

Lemma lty_env_open_one_shift_insert_bound k x T Σ :
  lty_env_open_one (S k) x (lty_env_shift (<[LVBound k := T]> Σ)) =
  lty_env_shift (lty_env_open_one k x (<[LVBound k := T]> Σ)).
Proof.
  rewrite lty_env_shift_insert.
  rewrite lty_env_open_one_insert.
  replace (logic_var_open (S k) x (logic_var_shift_from 0 (LVBound k)))
    with (LVFree x).
  2:{
    cbn [logic_var_shift_from].
    destruct (decide (0 <= k)) as [_|Hbad]; [|lia].
    rewrite logic_var_open_unfold.
    unfold swap. repeat destruct decide; try lia; try congruence.
  }
  rewrite lty_env_open_one_insert.
  replace (logic_var_open k x (LVBound k)) with (LVFree x).
  2:{
    rewrite logic_var_open_unfold.
    unfold swap. repeat destruct decide; try lia; try congruence.
  }
  rewrite lty_env_shift_insert_free.
  unfold lty_env_shift.
  rewrite lty_env_open_one_shift_under_gen by lia.
  reflexivity.
Qed.

Lemma lvars_bv_of_bvars (B : gset nat) :
  lvars_bv (lvars_of_bvars B) = B.
Proof.
  apply set_eq. intros k.
  rewrite lvars_bv_elem.
  unfold lvars_of_bvars.
  rewrite elem_of_map.
  split.
  - intros [n [Heq Hn]]. inversion Heq. subst. exact Hn.
  - intros Hk. exists k. split; [reflexivity|exact Hk].
Qed.

Lemma lvars_bv_shift_from D k :
  lvars_bv (lvars_shift_from k D) =
  set_map (fun n => if decide (k <= n) then S n else n) (lvars_bv D).
Proof.
  apply lvars_shift_from_bv.
Qed.

Lemma lty_env_bvar_scope_shift_open_noop k x Σ :
  LVBound k ∉ lty_env_bvar_scope (lty_env_shift Σ) ->
  lvars_open k x (lty_env_bvar_scope (lty_env_shift Σ)) =
  lty_env_bvar_scope (lty_env_shift Σ).
Proof.
  intros Hfresh.
  rewrite lvars_open_unfold.
  apply set_swap_fresh.
  - exact Hfresh.
  - unfold lty_env_bvar_scope, lvars_of_bvars.
    intros Hin. apply elem_of_map in Hin as [n [Hbad _]].
    discriminate.
Qed.

Lemma lty_env_bvar_scope_shift_open_one_noop k x Σ :
  LVBound k ∉ lty_env_bvar_scope (lty_env_shift Σ) ->
  LVFree x ∉ dom (lty_env_shift Σ) ->
  lty_env_bvar_scope (lty_env_open_one k x (lty_env_shift Σ)) =
  lty_env_bvar_scope (lty_env_shift Σ).
Proof.
  intros Hbound Hfree.
  unfold lty_env_bvar_scope.
  f_equal.
  rewrite lty_env_open_one_dom.
  apply set_eq. intros n.
  rewrite !lvars_bv_elem.
  rewrite lvars_open_unfold, set_swap_elem.
  unfold swap.
  destruct (decide (LVBound n = LVBound k)) as [Hnk|Hnk].
  - inversion Hnk. subst n.
    repeat destruct decide; try congruence.
    split; intros Hin; [exfalso; exact (Hfree Hin)|].
    exfalso. apply Hbound.
    unfold lty_env_bvar_scope, lvars_of_bvars.
    apply elem_of_map. exists k. split; [reflexivity|].
    rewrite lvars_bv_elem. exact Hin.
  - repeat destruct decide; try congruence.
    reflexivity.
Qed.

Lemma lty_env_bvar_scope_open_one_shift_under_result k x Σ :
  LVBound (S k) ∉ lty_env_bvar_scope (lty_env_shift Σ) ->
  LVFree x ∉ dom (lty_env_shift Σ) ->
  lty_env_bvar_scope (lty_env_open_one (S k) x (lty_env_shift Σ)) =
  lty_env_bvar_scope (lty_env_shift Σ).
Proof.
  apply lty_env_bvar_scope_shift_open_one_noop.
Qed.

Lemma lvars_open_shift_union_bound0 k x D :
  lvars_open (S k) x (lvars_shift_from 0 D ∪ {[LVBound 0]}) =
  lvars_shift_from 0 (lvars_open k x D) ∪ {[LVBound 0]}.
Proof.
  rewrite lvars_open_unfold, set_swap_union, <- lvars_open_unfold.
  rewrite lvars_open_shift_from_under_gen by lia.
  rewrite set_swap_singleton.
  rewrite swap_fresh by discriminate.
  reflexivity.
Qed.

Lemma lvars_open_shift_dom_union_bound0 k x (Σ : lty_env) :
  lvars_open (S k) x (lvars_shift_from 0 (dom Σ) ∪ {[LVBound 0]}) =
  lvars_shift_from 0 (lvars_open k x (dom Σ)) ∪ {[LVBound 0]}.
Proof.
  apply lvars_open_shift_union_bound0.
Qed.

Lemma lty_env_atom_dom_open_one k x Σ :
  lty_env_atom_dom (lty_env_open_one k x Σ) ⊆ lty_env_atom_dom Σ ∪ {[x]}.
Proof.
  unfold lty_env_atom_dom.
  rewrite lty_env_open_one_dom.
  apply lvars_fv_open_subset.
Qed.
