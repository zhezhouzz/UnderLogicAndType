(** * BasicDenotation.BasicTypingFormula

    Encoding CoreLang basic type well-formedness side conditions as
    ContextLogic formulas.  We keep only the component formulas; obligation
    wrapper sugar is intentionally avoided on the new route. *)

From CoreLang Require Import LocallyNamelessExtra.
From ContextBasicDenotation Require Import Notation StoreTyping TermTLet.
From ContextBase Require Import BaseTactics.

Section BasicTypingFormula.

Lemma basic_typing_open_env_swap_back
    (η : gmap nat atom) k y z Σ e T :
  η !! k = Some z ->
  y ∉ lvars_fv (dom Σ) ∪ fv_tm e ->
  z ∉ lvars_fv (dom Σ) ->
  open_env_avoids_atom y (delete k η) ->
  open_env_fresh_for_lvars η ({[LVBound k]} ∪ dom Σ) ->
  open_env_fresh_for_lvars η (tm_lvars e) ->
  open_env_fresh_for_lvars (<[k := y]> (delete k η)) (tm_lvars e) ->
  lty_env_to_atom_env
    (lty_env_open_lvars (<[k := y]> (delete k η)) Σ) ⊢ₑ
    open_tm_env (<[k := y]> (delete k η)) e ⋮ T ->
  lty_env_to_atom_env (lty_env_open_lvars η Σ) ⊢ₑ
    open_tm_env η e ⋮ T.
Proof.
  intros Hηk Hy Hz Havoid HfreshΣ Hfreshη Hfreshy Hty.
  pose proof (basic_typing_swap_tm _ _ _ y z Hty) as Hswap.
  rewrite open_tm_env_insert_open_swap_back in Hswap by
    (try exact Hηk; try exact Hfreshη; try exact Hfreshy; set_solver).
  rewrite lvar_store_to_atom_store_open_lvars_insert_delete_swap_back in Hswap
    by (try exact Hηk; try exact Havoid; try exact HfreshΣ; set_solver).
  exact Hswap.
Qed.

Definition basic_tm_has_ltype_by_open_env
    (Σ : lty_env) (e : tm) (T : ty) : Prop :=
  tm_lvars e ⊆ dom Σ /\
  forall η,
    open_env_fresh_for_lvars η (dom Σ) ->
    lvars_bv (dom Σ) ⊆ dom η ->
    lty_env_to_atom_env (lty_env_open_lvars η Σ) ⊢ₑ
      open_tm_env η e ⋮ T.

Inductive basic_value_has_ltype : lty_env -> value -> ty -> Prop :=
  | BVT_Const Σ c :
      basic_value_has_ltype Σ (vconst c) (TBase (base_ty_of_const c))
  | BVT_FVar Σ x T :
      Σ !! LVFree x = Some T ->
      basic_value_has_ltype Σ (vfvar x) T
  | BVT_BVar Σ k T :
      Σ !! LVBound k = Some T ->
      basic_value_has_ltype Σ (vbvar k) T
  | BVT_Lam Σ s T e (L : aset) :
      (forall x, x ∉ L ->
        basic_tm_has_ltype (<[LVFree x := s]> Σ) (e ^^ x) T) ->
      basic_value_has_ltype Σ (vlam s e) (s →ₜ T)
  | BVT_Fix Σ sx T vf (L : aset) :
      (forall x, x ∉ L ->
        basic_value_has_ltype (<[LVFree x := sx]> Σ) (vf ^^ x)
          ((sx →ₜ T) →ₜ T)) ->
      basic_value_has_ltype Σ (vfix (sx →ₜ T) vf) (sx →ₜ T)

with basic_tm_has_ltype : lty_env -> tm -> ty -> Prop :=
  | BTT_Ret Σ v T :
      basic_value_has_ltype Σ v T ->
      basic_tm_has_ltype Σ (tret v) T
  | BTT_Let Σ T1 T2 e1 e2 (L : aset) :
      basic_tm_has_ltype Σ e1 T1 ->
      (forall x, x ∉ L ->
        basic_tm_has_ltype (<[LVFree x := T1]> Σ) (e2 ^^ x) T2) ->
      basic_tm_has_ltype Σ (tlete e1 e2) T2
  | BTT_Op Σ op v arg_b ret_b :
      prim_op_type op = (arg_b, ret_b) ->
      basic_value_has_ltype Σ v (TBase arg_b) ->
      basic_tm_has_ltype Σ (tprim op v) (TBase ret_b)
  | BTT_App Σ s1 s2 v1 v2 :
      basic_value_has_ltype Σ v1 (s1 →ₜ s2) ->
      basic_value_has_ltype Σ v2 s1 ->
      basic_tm_has_ltype Σ (tapp v1 v2) s2
  | BTT_Match Σ v T et ef :
      basic_value_has_ltype Σ v (TBase TBool) ->
      basic_tm_has_ltype Σ et T ->
      basic_tm_has_ltype Σ ef T ->
      basic_tm_has_ltype Σ (tmatch v et ef) T.

Scheme basic_value_has_ltype_ind' := Induction for basic_value_has_ltype Sort Prop
  with basic_tm_has_ltype_ind' := Induction for basic_tm_has_ltype Sort Prop.
Combined Scheme basic_has_ltype_mutind
  from basic_value_has_ltype_ind', basic_tm_has_ltype_ind'.

Hint Constructors basic_value_has_ltype basic_tm_has_ltype : core.

Lemma basic_value_has_ltype_lvars Σ v T :
  basic_value_has_ltype Σ v T ->
  lvars_of_atoms (fv_value v) ⊆ dom Σ.
Proof.
  induction 1 using basic_value_has_ltype_ind'
    with (P0 := fun Σ e T _ => lvars_of_atoms (fv_tm e) ⊆ dom Σ);
    cbn [fv_value fv_tm]; try set_solver.
  - match goal with
    | Hlook : _ !! _ = Some _ |- _ =>
        apply elem_of_dom_2 in Hlook; set_solver
    end.
  - set (y := fresh_for (L ∪ fv_tm e ∪ lvars_fv (dom Σ))).
    assert (Hy : y ∉ L ∪ fv_tm e ∪ lvars_fv (dom Σ)).
    { subst y. apply fresh_for_not_in. }
    match goal with
    | Hopen_typed : forall z, z ∉ _ ->
        lvars_of_atoms (fv_tm _) ⊆ _ |- _ =>
        pose proof (Hopen_typed y ltac:(set_solver)) as Hopened;
        rewrite dom_insert in Hopened
    end.
    pose proof (open_fv_tm' e (vfvar y) 0) as Hopen.
    cbn [fv_value] in Hopen.
    set_solver.
  - set (y := fresh_for (L ∪ fv_value vf ∪ lvars_fv (dom Σ))).
    assert (Hy : y ∉ L ∪ fv_value vf ∪ lvars_fv (dom Σ)).
    { subst y. apply fresh_for_not_in. }
    match goal with
    | Hopen_typed : forall z, z ∉ _ ->
        lvars_of_atoms (fv_value _) ⊆ _ |- _ =>
        pose proof (Hopen_typed y ltac:(set_solver)) as Hopened;
        rewrite dom_insert in Hopened
    end.
    pose proof (open_fv_value' vf (vfvar y) 0) as Hopen.
    cbn [fv_value] in Hopen.
    set_solver.
  - set (y := fresh_for (L ∪ fv_tm e2 ∪ lvars_fv (dom Σ))).
    assert (Hy : y ∉ L ∪ fv_tm e2 ∪ lvars_fv (dom Σ)).
    { subst y. apply fresh_for_not_in. }
    match goal with
    | Hopen_typed : forall z, z ∉ _ ->
        lvars_of_atoms (fv_tm _) ⊆ _ |- _ =>
        pose proof (Hopen_typed y ltac:(set_solver)) as Hopened;
        rewrite dom_insert in Hopened
    end.
    pose proof (open_fv_tm' e2 (vfvar y) 0) as Hopen.
    cbn [fv_value] in Hopen.
    set_solver.
Qed.

Lemma basic_tm_has_ltype_lvars Σ e T :
  basic_tm_has_ltype Σ e T ->
  lvars_of_atoms (fv_tm e) ⊆ dom Σ.
Proof.
  induction 1 using basic_tm_has_ltype_ind'
    with (P := fun Σ v T _ => lvars_of_atoms (fv_value v) ⊆ dom Σ);
    cbn [fv_value fv_tm]; try set_solver.
  - match goal with
    | Hlook : _ !! _ = Some _ |- _ =>
        apply elem_of_dom_2 in Hlook; set_solver
    end.
  - set (y := fresh_for (L ∪ fv_tm e ∪ lvars_fv (dom Σ))).
    assert (Hy : y ∉ L ∪ fv_tm e ∪ lvars_fv (dom Σ)).
    { subst y. apply fresh_for_not_in. }
    match goal with
    | Hopen_typed : forall z, z ∉ _ ->
        lvars_of_atoms (fv_tm _) ⊆ _ |- _ =>
        pose proof (Hopen_typed y ltac:(set_solver)) as Hopened;
        rewrite dom_insert in Hopened
    end.
    pose proof (open_fv_tm' e (vfvar y) 0) as Hopen.
    cbn [fv_value] in Hopen.
    set_solver.
  - set (y := fresh_for (L ∪ fv_value vf ∪ lvars_fv (dom Σ))).
    assert (Hy : y ∉ L ∪ fv_value vf ∪ lvars_fv (dom Σ)).
    { subst y. apply fresh_for_not_in. }
    match goal with
    | Hopen_typed : forall z, z ∉ _ ->
        lvars_of_atoms (fv_value _) ⊆ _ |- _ =>
        pose proof (Hopen_typed y ltac:(set_solver)) as Hopened;
        rewrite dom_insert in Hopened
    end.
    pose proof (open_fv_value' vf (vfvar y) 0) as Hopen.
    cbn [fv_value] in Hopen.
    set_solver.
  - set (y := fresh_for (L ∪ fv_tm e2 ∪ lvars_fv (dom Σ))).
    assert (Hy : y ∉ L ∪ fv_tm e2 ∪ lvars_fv (dom Σ)).
    { subst y. apply fresh_for_not_in. }
    match goal with
    | Hopen_typed : forall z, z ∉ _ ->
        lvars_of_atoms (fv_tm _) ⊆ _ |- _ =>
        pose proof (Hopen_typed y ltac:(set_solver)) as Hopened;
        rewrite dom_insert in Hopened
    end.
    pose proof (open_fv_tm' e2 (vfvar y) 0) as Hopen.
    cbn [fv_value] in Hopen.
    set_solver.
Qed.

Lemma basic_has_ltype_weaken_mutual :
  (forall Σ v T,
    basic_value_has_ltype Σ v T ->
    forall Σ',
      Σ ⊆ Σ' ->
      basic_value_has_ltype Σ' v T) /\
  (forall Σ e T,
    basic_tm_has_ltype Σ e T ->
    forall Σ',
      Σ ⊆ Σ' ->
      basic_tm_has_ltype Σ' e T).
Proof.
  apply basic_has_ltype_mutind; intros; eauto.
  - econstructor. eapply lookup_weaken; eassumption.
  - econstructor. eapply lookup_weaken; eassumption.
  - eapply BVT_Lam with (L := L). intros x Hx.
    eapply H; [exact Hx|].
    apply insert_mono. exact H0.
  - eapply BVT_Fix with (L := L). intros x Hx.
    eapply H; [exact Hx|].
    apply insert_mono. exact H0.
  - eapply BTT_Let with (L := L).
    + eapply H; exact H1.
    + intros x Hx. eapply H0; [exact Hx|].
      apply insert_mono. exact H1.
Qed.

Lemma basic_value_has_ltype_weaken Σ Σ' v T :
  basic_value_has_ltype Σ v T ->
  Σ ⊆ Σ' ->
  basic_value_has_ltype Σ' v T.
Proof.
  intros Hty Hsub.
  exact (proj1 basic_has_ltype_weaken_mutual Σ v T Hty Σ' Hsub).
Qed.

Lemma basic_tm_has_ltype_weaken Σ Σ' e T :
  basic_tm_has_ltype Σ e T ->
  Σ ⊆ Σ' ->
  basic_tm_has_ltype Σ' e T.
Proof.
  intros Hty Hsub.
  exact (proj2 basic_has_ltype_weaken_mutual Σ e T Hty Σ' Hsub).
Qed.

Lemma basic_tm_has_ltype_to_open_env Σ e T :
  basic_tm_has_ltype Σ e T ->
  basic_tm_has_ltype_by_open_env Σ e T.
Admitted.

Lemma basic_has_ltype_of_atom_typing_mutual :
  (forall Δ v T,
    Δ ⊢ᵥ v ⋮ T ->
    basic_value_has_ltype (atom_env_to_lty_env Δ) v T) /\
  (forall Δ e T,
    Δ ⊢ₑ e ⋮ T ->
    basic_tm_has_ltype (atom_env_to_lty_env Δ) e T).
Proof.
  apply has_type_mutind; intros; eauto.
  - econstructor. rewrite atom_store_to_lvar_store_lookup_free. exact e.
  - eapply BVT_Lam with (L := L). intros x Hx.
    pose proof (H x Hx) as Hbody.
    rewrite atom_store_to_lvar_store_insert in Hbody.
    exact Hbody.
  - eapply BVT_Fix with (L := L). intros x Hx.
    pose proof (H x Hx) as Hbody.
    rewrite atom_store_to_lvar_store_insert in Hbody.
    exact Hbody.
  - eapply BTT_Let with (L := L); eauto.
    intros x Hx.
    pose proof (H0 x Hx) as Hbody.
    rewrite atom_store_to_lvar_store_insert in Hbody.
    exact Hbody.
Qed.

Lemma basic_value_has_ltype_of_atom_env_typing Δ v T :
  Δ ⊢ᵥ v ⋮ T ->
  basic_value_has_ltype (atom_env_to_lty_env Δ) v T.
Proof. exact (proj1 basic_has_ltype_of_atom_typing_mutual Δ v T). Qed.

Lemma basic_tm_has_ltype_of_atom_env_typing Δ e T :
  Δ ⊢ₑ e ⋮ T ->
  basic_tm_has_ltype (atom_env_to_lty_env Δ) e T.
Proof. exact (proj2 basic_has_ltype_of_atom_typing_mutual Δ e T). Qed.

Lemma basic_value_has_ltype_of_empty_atom_typing Σ v T :
  ∅ ⊢ᵥ v ⋮ T ->
  basic_value_has_ltype Σ v T.
Proof.
  intros Hty.
  eapply basic_value_has_ltype_weaken.
  - exact (basic_value_has_ltype_of_atom_env_typing ∅ v T Hty).
  - apply map_empty_subseteq.
Qed.

Lemma atom_store_has_ltype_insert_fresh Σ σ x T :
  x ∉ dom (σ : gmap atom value) ->
  atom_store_has_ltype Σ σ ->
  atom_store_has_ltype (<[LVFree x := T]> Σ) σ.
Proof.
  intros Hx Htyped y v Hy.
  destruct (Htyped y v Hy) as [U [HΣ Hv]].
  exists U. split; [|exact Hv].
  rewrite lookup_insert_ne; [exact HΣ|].
  intros Heq. inversion Heq. subst y.
  apply Hx. change (x ∈ dom (σ : gmap atom value)).
  rewrite elem_of_dom. eauto.
Qed.

Lemma lty_env_msubst_store_insert_fresh σ Σ x T :
  x ∉ dom (σ : gmap atom value) ->
  lty_env_msubst_store σ (<[LVFree x := T]> Σ) =
  <[LVFree x := T]> (lty_env_msubst_store σ Σ).
Proof.
  intros Hx.
  unfold lty_env_msubst_store.
  rewrite dom_insert_L.
  rewrite storeA_restrict_insert_in.
  - f_equal.
    apply storeA_map_eq. intros v.
    rewrite !storeA_restrict_lookup.
    destruct (decide (v ∈ dom Σ ∖ lvars_of_atoms (dom (σ : gmap atom value))))
      as [Hv|Hv].
    + destruct (decide (v ∈ ({[LVFree x]} ∪ dom Σ)
          ∖ lvars_of_atoms (dom (σ : gmap atom value)))) as [_|Hbad].
      * reflexivity.
      * set_solver.
    + destruct (decide (v ∈ ({[LVFree x]} ∪ dom Σ)
          ∖ lvars_of_atoms (dom (σ : gmap atom value)))) as [Hvbig|_].
      * apply elem_of_difference in Hvbig as [Hvbig Hvfresh].
        apply elem_of_union in Hvbig as [Hvx|HvΣ].
        -- apply elem_of_singleton in Hvx. subst v.
           destruct ((Σ : gmap logic_var ty) !! LVFree x) eqn:HΣx; [|reflexivity].
           exfalso. apply Hv.
           apply elem_of_difference. split; [rewrite elem_of_dom; eauto|exact Hvfresh].
        -- exfalso. apply Hv. apply elem_of_difference. split; assumption.
      * reflexivity.
  - apply elem_of_difference. split.
    + apply elem_of_union_l. set_solver.
    + intros Hbad. unfold lvars_of_atoms in Hbad.
      apply elem_of_map in Hbad as [y [Heq Hy]].
      inversion Heq. subst y.
      apply Hx. exact Hy.
Qed.

Lemma basic_has_ltype_msubst_store_at_mutual :
  (forall Σ v T,
    basic_value_has_ltype Σ v T ->
    forall d σ,
      atom_store_has_ltype Σ σ ->
      basic_value_has_ltype (lty_env_msubst_store σ Σ)
        (lstore_instantiate_value_at d (lstore_lift_free σ) v) T) /\
  (forall Σ e T,
    basic_tm_has_ltype Σ e T ->
    forall d σ,
      atom_store_has_ltype Σ σ ->
      basic_tm_has_ltype (lty_env_msubst_store σ Σ)
        (lstore_instantiate_tm_at d (lstore_lift_free σ) e) T).
Proof.
  apply basic_has_ltype_mutind;
    intros; cbn [lstore_instantiate_value_at lstore_instantiate_tm_at
      lstore_instantiate_value_split_at lstore_instantiate_tm_split_at].
  - constructor.
  - rewrite lstore_free_part_lift_free.
    cbn [lstore_instantiate_value_split_at].
    destruct ((σ : gmap atom value) !! x) as [vx|] eqn:Hσx.
    + match goal with
      | Htyped : atom_store_has_ltype _ σ,
        Hlook : Σ !! LVFree x = Some T |- _ =>
          destruct (Htyped x vx Hσx) as [U [HΣU Hvx]];
          rewrite Hlook in HΣU; inversion HΣU; subst U
      end.
      replace (match (σ : gmap atom value) !! x with
               | Some u => u
               | None => vfvar x
               end) with vx by (rewrite Hσx; reflexivity).
      apply basic_value_has_ltype_of_empty_atom_typing. exact Hvx.
    + replace (match (σ : gmap atom value) !! x with
               | Some u => u
               | None => vfvar x
               end) with (vfvar x) by (rewrite Hσx; reflexivity).
      constructor. apply lty_env_msubst_store_lookup_some_2.
      * match goal with
        | Hlook : Σ !! LVFree x = Some T |- _ => exact Hlook
        end.
      * intros Hin. unfold lvars_of_atoms in Hin.
      apply elem_of_map in Hin as [y [Hy HyD]].
      inversion Hy. subst y.
      apply not_elem_of_dom in Hσx. exact (Hσx HyD).
  - rewrite lstore_bound_part_empty_of_lc by apply lc_lstore_lift_free.
    destruct (decide (d <= k)); rewrite ?lookup_empty.
    + constructor. apply lty_env_msubst_store_lookup_some_2.
      * match goal with
        | Hlook : Σ !! LVBound k = Some T |- _ => exact Hlook
        end.
      * intros Hin. unfold lvars_of_atoms in Hin.
      apply elem_of_map in Hin as [y [Hy _]]. discriminate.
    + constructor. apply lty_env_msubst_store_lookup_some_2.
      * match goal with
        | Hlook : Σ !! LVBound k = Some T |- _ => exact Hlook
        end.
      * intros Hin. unfold lvars_of_atoms in Hin.
      apply elem_of_map in Hin as [y [Hy _]]. discriminate.
  - eapply BVT_Lam with (L := L ∪ dom (σ : gmap atom value) ∪ fv_tm e).
    intros y Hy.
    match goal with
    | Htyped : atom_store_has_ltype Σ σ,
      IH : forall z, z ∉ L -> forall d0 σ0,
        atom_store_has_ltype (<[LVFree z := s]> Σ) σ0 -> _ |- _ =>
        pose proof (atom_store_has_ltype_insert_fresh Σ σ y s
          ltac:(set_solver) Htyped) as Hσy;
        pose proof (IH y ltac:(set_solver) (S d) σ Hσy) as Hbody
    end.
    rewrite lty_env_msubst_store_insert_fresh in Hbody by set_solver.
    change (e ^^ y) with (open_tm 0 (vfvar y) e) in Hbody.
    rewrite lstore_instantiate_tm_at_open0_fresh_lift_free in Hbody.
    + exact Hbody.
    + match goal with
      | Htyped : atom_store_has_ltype Σ σ |- _ =>
          apply atom_store_has_ltype_closed with (Σ := Σ); exact Htyped
      end.
    + set_solver.
  - eapply BVT_Fix with (L := L ∪ dom (σ : gmap atom value) ∪ fv_value vf).
    intros y Hy.
    match goal with
    | Htyped : atom_store_has_ltype Σ σ,
      IH : forall z, z ∉ L -> forall d0 σ0,
        atom_store_has_ltype (<[LVFree z := sx]> Σ) σ0 -> _ |- _ =>
        pose proof (atom_store_has_ltype_insert_fresh Σ σ y sx
          ltac:(set_solver) Htyped) as Hσy;
        pose proof (IH y ltac:(set_solver) (S d) σ Hσy) as Hbody
    end.
    rewrite lty_env_msubst_store_insert_fresh in Hbody by set_solver.
    change (vf ^^ y) with (open_value 0 (vfvar y) vf) in Hbody.
    rewrite lstore_instantiate_value_at_open0_fresh_lift_free in Hbody.
    + exact Hbody.
    + match goal with
      | Htyped : atom_store_has_ltype Σ σ |- _ =>
          apply atom_store_has_ltype_closed with (Σ := Σ); exact Htyped
      end.
    + set_solver.
  - constructor.
    match goal with
    | IH : forall d0 σ0, atom_store_has_ltype Σ σ0 -> _,
      Htyped : atom_store_has_ltype Σ σ |- _ =>
        apply IH; exact Htyped
    end.
  - eapply BTT_Let with (L := L ∪ dom (σ : gmap atom value) ∪ fv_tm e2).
    + match goal with
      | IH : forall d0 σ0, atom_store_has_ltype Σ σ0 -> _,
        Htyped : atom_store_has_ltype Σ σ |- _ =>
          apply IH; exact Htyped
      end.
    + intros y Hy.
      match goal with
      | Htyped : atom_store_has_ltype Σ σ,
        IH : forall z, z ∉ L -> forall d0 σ0,
          atom_store_has_ltype (<[LVFree z := T1]> Σ) σ0 -> _ |- _ =>
          pose proof (atom_store_has_ltype_insert_fresh Σ σ y T1
            ltac:(set_solver) Htyped) as Hσy;
          pose proof (IH y ltac:(set_solver) (S d) σ Hσy) as Hbody
      end.
      rewrite lty_env_msubst_store_insert_fresh in Hbody by set_solver.
      change (e2 ^^ y) with (open_tm 0 (vfvar y) e2) in Hbody.
      rewrite lstore_instantiate_tm_at_open0_fresh_lift_free in Hbody.
      * exact Hbody.
      * match goal with
        | Htyped : atom_store_has_ltype Σ σ |- _ =>
            apply atom_store_has_ltype_closed with (Σ := Σ); exact Htyped
        end.
      * set_solver.
  - eapply BTT_Op.
    + match goal with
      | Hop : prim_op_type op = (arg_b, ret_b) |- _ => exact Hop
      end.
    +
    match goal with
    | IH : forall d0 σ0, atom_store_has_ltype Σ σ0 -> _,
      Htyped : atom_store_has_ltype Σ σ |- _ =>
        apply IH; exact Htyped
    end.
  - eapply BTT_App;
      match goal with
      | IH : forall d0 σ0, atom_store_has_ltype Σ σ0 -> _,
        Htyped : atom_store_has_ltype Σ σ |- _ =>
          apply IH; exact Htyped
      end.
  - eapply BTT_Match;
      match goal with
      | IH : forall d0 σ0, atom_store_has_ltype Σ σ0 -> _,
        Htyped : atom_store_has_ltype Σ σ |- _ =>
          apply IH; exact Htyped
      end.
Qed.

Lemma basic_value_has_ltype_msubst_store_at
    d σ Σ v T :
  atom_store_has_ltype Σ σ ->
  basic_value_has_ltype Σ v T ->
  basic_value_has_ltype (lty_env_msubst_store σ Σ)
    (lstore_instantiate_value_at d (lstore_lift_free σ) v) T.
Proof.
  intros Hσ Hty.
  exact (proj1 basic_has_ltype_msubst_store_at_mutual Σ v T Hty d σ Hσ).
Qed.

Lemma basic_tm_has_ltype_msubst_store_at
    d σ Σ e T :
  atom_store_has_ltype Σ σ ->
  basic_tm_has_ltype Σ e T ->
  basic_tm_has_ltype (lty_env_msubst_store σ Σ)
    (lstore_instantiate_tm_at d (lstore_lift_free σ) e) T.
Proof.
  intros Hσ Hty.
  exact (proj2 basic_has_ltype_msubst_store_at_mutual Σ e T Hty d σ Hσ).
Qed.

Lemma basic_tm_has_ltype_msubst_store
    σ Σ e T :
  atom_store_has_ltype Σ σ ->
  basic_tm_has_ltype Σ e T ->
  basic_tm_has_ltype (lty_env_msubst_store σ Σ)
    (lstore_instantiate_tm (lstore_lift_free σ) e) T.
Proof.
  intros Hσ Hty.
  exact (basic_tm_has_ltype_msubst_store_at 0 σ Σ e T Hσ Hty).
Qed.

Lemma basic_tm_has_ltype_tapp_tm_tlete_assoc
    (Σ : lty_env) e1 e2 y T :
  lc_tm (tlete e1 e2) ->
  basic_tm_has_ltype Σ (tlete e1 (tapp_tm e2 (vfvar y))) T ->
  basic_tm_has_ltype Σ (tapp_tm (tlete e1 e2) (vfvar y)) T.
Admitted.

Lemma basic_tm_has_ltype_tapp_tm_tlete_assoc_rev
    (Σ : lty_env) e1 e2 y T :
  lc_tm (tlete e1 e2) ->
  basic_tm_has_ltype Σ (tapp_tm (tlete e1 e2) (vfvar y)) T ->
  basic_tm_has_ltype Σ (tlete e1 (tapp_tm e2 (vfvar y))) T.
Admitted.

Lemma basic_typing_tapp_tlete_assoc_spine Γ e1 e2 y ys T :
  Γ ⊢ₑ tapp_tm_fvar_spine
    (tlete e1 (tapp_tm e2 (vfvar y))) ys ⋮ T ->
  Γ ⊢ₑ tapp_tm_fvar_spine
    (tapp_tm (tlete e1 e2) (vfvar y)) ys ⋮ T.
Proof.
  induction ys as [|z ys IH] in T |- *; cbn [tapp_tm_fvar_spine].
  - apply basic_typing_tapp_tm_tlete_assoc.
  - intros Hty.
    apply basic_typing_tapp_tm_fvar_inv in Hty as [Tx [Hfun Hz]].
    eapply basic_typing_tapp_tm.
    + apply IH. exact Hfun.
    + exact Hz.
Qed.

Lemma basic_tm_has_ltype_tapp_tlete_assoc_spine
    (Σ : lty_env) e1 e2 y ys T :
  lc_tm (tlete e1 e2) ->
  basic_tm_has_ltype Σ
    (tapp_tm_fvar_spine (tlete e1 (tapp_tm e2 (vfvar y))) ys) T ->
  basic_tm_has_ltype Σ
    (tapp_tm_fvar_spine (tapp_tm (tlete e1 e2) (vfvar y)) ys) T.
Admitted.

Lemma basic_tm_has_ltype_insert_fresh_lvar
    (Σ : lty_env) e U x T :
  LVFree x ∉ dom Σ ->
  basic_tm_has_ltype Σ e U ->
  basic_tm_has_ltype (<[LVFree x := T]> Σ) e U.
Proof.
  intros Hfresh Hty.
  eapply basic_tm_has_ltype_weaken; [exact Hty|].
  apply insert_subseteq. apply not_elem_of_dom. exact Hfresh.
Qed.

Lemma basic_tm_has_ltype_swap_atom x y Σ e T :
  basic_tm_has_ltype Σ e T ->
  basic_tm_has_ltype (lty_env_swap x y Σ) (tm_swap_atom x y e) T.
Admitted.

(** The syntactic well-formedness of [τ] is not a runtime property of the
    world, but we still package it as a world-independent logic qualifier.
    Unlike [basic_context_ty], this version is scoped by the lvar-domain of [Σ]
    directly, so bound lvars in a type body are preserved until the surrounding
    formula open swaps them to atoms. *)
Definition context_ty_wf_lqual
    (Σ : lty_env) (τ : context_ty) : LogicQualifierT :=
  lqual (dom Σ)
    (fun _ => basic_context_ty_lvars (dom Σ) τ).
Definition context_ty_wf_formula
    (Σ : lty_env) (τ : context_ty) : Formula :=
  FAtom (context_ty_wf_lqual Σ τ).
Lemma formula_fv_context_ty_wf_formula Σ τ :
  formula_fv (context_ty_wf_formula Σ τ) = lvars_fv (dom Σ).
Proof. reflexivity. Qed.
Definition expr_basic_typing_lqual
    (Σ : lty_env) (e : tm) (T : ty) : LogicQualifierT :=
  lqual (dom Σ)
    (fun _ => basic_tm_has_ltype Σ e T).
Definition expr_basic_typing_formula
    (Σ : lty_env) (e : tm) (T : ty) : Formula :=
  FAtom (expr_basic_typing_lqual Σ e T).
Lemma formula_fv_expr_basic_typing_formula Σ e T :
  formula_fv (expr_basic_typing_formula Σ e T) = lvars_fv (dom Σ).
Proof. reflexivity. Qed.
Lemma formula_open_context_ty_wf_formula k y Σ τ :
  formula_open k y (context_ty_wf_formula Σ τ) =
  context_ty_wf_formula (lty_env_open_one k y Σ) (cty_open k y τ).
Proof.
  unfold context_ty_wf_formula, context_ty_wf_lqual.
  cbn [formula_open lqual_open].
  f_equal.
  apply logic_qualifier_ext.
  - rewrite lty_env_open_one_dom. reflexivity.
  - intros w1 w2 _. cbn [lqual_prop].
    rewrite lty_env_open_one_dom.
    rewrite basic_context_ty_lvars_open.
    reflexivity.
Qed.

Lemma formula_open_env_context_ty_wf_formula η Σ τ :
  open_env_fresh_for_lvars η (dom Σ ∪ context_ty_lvars τ) ->
  open_env_values_inj η ->
  formula_open_env η (context_ty_wf_formula Σ τ) =
  context_ty_wf_formula (lty_env_open_lvars η Σ) (open_cty_env η τ).
Proof.
  revert Σ τ.
  induction η as [|k x η Hnone Hfold IH] using fin_maps.map_fold_ind.
  - intros Σ τ _ _.
    rewrite formula_open_env_empty, lty_env_open_lvars_empty,
      open_cty_env_empty. reflexivity.
  - intros Σ τ Hfresh Hinj.
    pose proof (open_env_values_inj_insert_inv η k x Hnone Hinj)
      as [Hinjη Havoid].
    pose proof (open_env_fresh_for_lvars_insert_tail η k x
      (dom Σ ∪ context_ty_lvars τ) Hnone Hfresh) as Hfreshη.
    rewrite formula_open_env_insert_fresh by assumption.
    rewrite IH by (exact Hfreshη || exact Hinjη).
    rewrite formula_open_context_ty_wf_formula.
    rewrite lty_env_open_lvars_insert_fresh.
    2: exact Hnone.
    2: exact Havoid.
    2:{ eapply open_env_fresh_for_lvars_mono;
          [intros v Hv; apply elem_of_union_l; exact Hv | exact Hfresh]. }
    rewrite open_cty_env_insert_fresh by assumption.
    reflexivity.
Qed.

Lemma basic_tm_has_ltype_open_one_fresh k y Σ e T :
  y ∉ lvars_fv (dom Σ) ∪ fv_tm e ->
  basic_tm_has_ltype Σ e T ->
  basic_tm_has_ltype (lty_env_open_one k y Σ)
    (open_tm k (vfvar y) e) T.
Admitted.

Lemma basic_tm_has_ltype_open_one_cofinite k Σ e T :
  basic_tm_has_ltype Σ e T ->
  exists L : aset,
    forall y,
      y ∉ L ->
      basic_tm_has_ltype (lty_env_open_one k y Σ)
        (open_tm k (vfvar y) e) T.
Proof.
  intros Hty.
  exists (lvars_fv (dom Σ) ∪ fv_tm e).
  intros y Hy.
  apply basic_tm_has_ltype_open_one_fresh; [exact Hy|exact Hty].
Qed.

Lemma basic_tm_has_ltype_close_one_cofinite k Σ e T :
  (exists L : aset,
    forall y,
      y ∉ L ->
      basic_tm_has_ltype (lty_env_open_one k y Σ)
        (open_tm k (vfvar y) e) T) ->
  basic_tm_has_ltype Σ e T.
Admitted.

Lemma atom_env_lty_env_roundtrip_closed (Σ : lty_env) :
  lty_env_closed Σ ->
  atom_env_to_lty_env (lty_env_to_atom_env Σ) = Σ.
Proof.
  intros Hclosed.
  apply map_eq. intros [k|x].
  - rewrite atom_store_to_lvar_store_lookup_bound_none.
    symmetry. apply lty_env_closed_lookup_bound_none. exact Hclosed.
  - rewrite atom_store_to_lvar_store_lookup_free.
    apply lvar_store_to_atom_store_lookup.
Qed.

Lemma basic_tm_has_ltype_of_atom_typing Σ e T :
  lty_env_closed Σ ->
  lty_env_to_atom_env Σ ⊢ₑ e ⋮ T ->
  basic_tm_has_ltype Σ e T.
Proof.
  intros Hclosed Hty.
  pose proof (basic_tm_has_ltype_of_atom_env_typing
    (lty_env_to_atom_env Σ) e T Hty) as Hbasic.
  rewrite atom_env_lty_env_roundtrip_closed in Hbasic by exact Hclosed.
  exact Hbasic.
Qed.

Lemma basic_tm_has_ltype_open_one_cofinite_iff k Σ e T :
  basic_tm_has_ltype Σ e T <->
  exists L : aset,
    forall y,
      y ∉ L ->
      basic_tm_has_ltype (lty_env_open_one k y Σ)
        (open_tm k (vfvar y) e) T.
Proof.
  split.
  - apply basic_tm_has_ltype_open_one_cofinite.
  - apply basic_tm_has_ltype_close_one_cofinite.
Qed.

Lemma basic_tm_has_ltype_open_one_rename_fresh k y z Σ e T :
  y ∉ lvars_fv (dom Σ) ∪ fv_tm e ->
  z ∉ lvars_fv (dom Σ) ∪ fv_tm e ->
  basic_tm_has_ltype (lty_env_open_one k y Σ)
    (open_tm k (vfvar y) e) T ->
  basic_tm_has_ltype (lty_env_open_one k z Σ)
    (open_tm k (vfvar z) e) T.
Admitted.

Lemma basic_tm_has_ltype_close_one_fresh k y Σ e T :
  y ∉ lvars_fv (dom Σ) ∪ fv_tm e ->
  basic_tm_has_ltype (lty_env_open_one k y Σ)
    (open_tm k (vfvar y) e) T ->
  basic_tm_has_ltype Σ e T.
Admitted.

Lemma basic_tm_has_ltype_open_one_fresh_iff k y Σ e T :
  y ∉ lvars_fv (dom Σ) ∪ fv_tm e ->
  basic_tm_has_ltype Σ e T <->
  basic_tm_has_ltype (lty_env_open_one k y Σ)
    (open_tm k (vfvar y) e) T.
Proof.
  intros Hy. split.
  - apply basic_tm_has_ltype_open_one_fresh. exact Hy.
  - apply basic_tm_has_ltype_close_one_fresh. exact Hy.
Qed.

Lemma formula_open_expr_basic_typing_formula k y Σ e T :
  y ∉ lvars_fv (dom Σ) ∪ fv_tm e ->
  formula_open k y (expr_basic_typing_formula Σ e T) =
  expr_basic_typing_formula
    (lty_env_open_one k y Σ) (open_tm k (vfvar y) e) T.
Proof.
  intros Hy.
  unfold expr_basic_typing_formula, expr_basic_typing_lqual.
  cbn [formula_open lqual_open].
  f_equal.
  apply logic_qualifier_ext.
  - rewrite lty_env_open_one_dom. reflexivity.
  - intros w1 w2 Hlw. cbn [lqual_prop].
    apply basic_tm_has_ltype_open_one_fresh_iff. exact Hy.
Qed.

Lemma formula_open_env_expr_basic_typing_formula η Σ e T :
  open_env_fresh_for_lvars η (dom Σ ∪ tm_lvars e) ->
  open_env_values_inj η ->
  formula_open_env η (expr_basic_typing_formula Σ e T) =
  expr_basic_typing_formula
    (lty_env_open_lvars η Σ) (open_tm_env η e) T.
Proof.
  revert Σ e.
  induction η as [|k x η Hnone Hfold IH] using fin_maps.map_fold_ind.
  - intros Σ e _ _.
    rewrite formula_open_env_empty, lty_env_open_lvars_empty.
    rewrite map_fold_empty. reflexivity.
  - intros Σ e Hfresh Hinj.
    pose proof (open_env_values_inj_insert_inv η k x Hnone Hinj)
      as [Hinjη Havoid].
    pose proof (open_env_fresh_for_lvars_insert_tail η k x
      (dom Σ ∪ tm_lvars e) Hnone Hfresh) as Hfreshη.
    rewrite formula_open_env_insert_fresh by assumption.
    rewrite IH by (exact Hfreshη || exact Hinjη).
    rewrite formula_open_expr_basic_typing_formula.
    2:{
      pose proof (open_env_fresh_for_lvars_insert_head η k x
        (dom Σ ∪ tm_lvars e) Hnone Hfresh) as Hhead.
      rewrite <- tm_lvars_fv.
      rewrite tm_lvars_open_tm_env.
      2:{ eapply open_env_fresh_for_lvars_mono.
          - intros v Hv. apply elem_of_union_r. exact Hv.
          - exact Hfreshη. }
      assert (HΣfv : lvars_fv (dom (lty_env_open_lvars η Σ)) ⊆
                     lvars_fv (lvars_open_env η (dom Σ))).
      {
        rewrite lty_env_open_lvars_dom.
        - unfold lvars_open_env. set_solver.
        - eapply open_env_fresh_for_lvars_mono;
            [intros v Hv; apply elem_of_union_l; exact Hv|exact Hfreshη].
      }
      intros Hbad. apply Hhead.
      rewrite lvars_open_env_union, lvars_fv_union.
      apply elem_of_union.
      apply elem_of_union in Hbad as [Hbad|Hbad].
      - left. apply HΣfv. exact Hbad.
      - right. exact Hbad.
    }
    rewrite lty_env_open_lvars_insert_fresh.
    2: exact Hnone.
    2: exact Havoid.
    2:{ eapply open_env_fresh_for_lvars_mono;
          [intros v Hv; apply elem_of_union_l; exact Hv|exact Hfresh]. }
    rewrite open_tm_env_insert_fresh_plain by exact Hnone.
    reflexivity.
Qed.

Lemma basic_typing_lty_env_insert_free_away Σ x T e U :
  x ∉ fv_tm e ->
  lty_env_to_atom_env Σ ⊢ₑ e ⋮ U ->
  lty_env_to_atom_env (<[LVFree x := T]> Σ) ⊢ₑ e ⋮ U.
Proof.
  intros Hfresh Hty.
  eapply basic_typing_env_agree_tm; [exact Hty|].
  intros a Ha.
  apply lvar_store_to_atom_store_insert_free_lookup_ne.
  intros ->. exact (Hfresh Ha).
Qed.

Lemma basic_typing_lty_env_to_atom_env_fv_subset Σ e T :
  lty_env_to_atom_env Σ ⊢ₑ e ⋮ T ->
  fv_tm e ⊆ lvars_fv (dom Σ).
Proof.
  intros Hty.
  pose proof (basic_typing_contains_fv_tm _ _ _ Hty) as Hfv.
  pose proof (lvar_store_to_atom_store_dom_subset Σ) as Hdom.
  unfold lty_env_atom_dom, lvar_store_atom_dom in Hdom.
  set_solver.
Qed.

Lemma context_ty_wf_lqual_denote_iff Σ τ (m : WfWorldT) :
  logic_qualifier_denote (context_ty_wf_lqual Σ τ) m <->
  lc_lvars (dom Σ) /\
  lvars_fv (dom Σ) ⊆ world_dom (m : WorldT) /\
  basic_context_ty_lvars (dom Σ) τ.
Proof.
  unfold context_ty_wf_lqual, logic_qualifier_denote.
  split.
  - intros [Hlc [Hsub Hbasic]]. tauto.
  - intros [Hlc [Hsub Hbasic]]. exists Hlc, Hsub. exact Hbasic.
Qed.

Lemma context_ty_wf_formula_models_iff Σ τ (m : WfWorldT) :
  res_models m (context_ty_wf_formula Σ τ) <->
  lc_lvars (dom Σ) /\
  lvars_fv (dom Σ) ⊆ world_dom (m : WorldT) /\
  basic_context_ty_lvars (dom Σ) τ.
Proof.
  unfold res_models, context_ty_wf_formula.
  cbn [formula_measure res_models_fuel].
  split.
  - intros [_ Hden].
    apply context_ty_wf_lqual_denote_iff. exact Hden.
  - intros Hden. split.
    + destruct Hden as [_ [Hsub _]]. exact Hsub.
    + apply context_ty_wf_lqual_denote_iff. exact Hden.
Qed.

Lemma context_ty_wf_formula_scope_dom Σ τ (m : WfWorldT) :
  res_models m (context_ty_wf_formula Σ τ) ->
  lvars_fv (dom Σ) ⊆ world_dom (m : WorldT).
Proof.
  intros Hmodels.
  apply context_ty_wf_formula_models_iff in Hmodels as [_ [Hsub _]].
  exact Hsub.
Qed.

Lemma context_ty_wf_formula_basic_lvars Σ τ (m : WfWorldT) :
  res_models m (context_ty_wf_formula Σ τ) ->
  basic_context_ty_lvars (dom Σ) τ.
Proof.
  intros Hmodels.
  apply context_ty_wf_formula_models_iff in Hmodels as [_ [_ Hbasic]].
  exact Hbasic.
Qed.

Lemma context_ty_wf_formula_fv_cty_subset Σ τ (m : WfWorldT) :
  res_models m (context_ty_wf_formula Σ τ) ->
  fv_cty τ ⊆ lvars_fv (dom Σ).
Proof.
  intros Hmodels.
  pose proof (context_ty_wf_formula_basic_lvars Σ τ m Hmodels)
    as [Hvars _].
  rewrite <- context_ty_lvars_fv.
  apply lvars_fv_mono. exact Hvars.
Qed.

Lemma context_ty_wf_formula_insert_fresh_lvar
    (Σ : lty_env) τ (m mx : WfWorldT) x T Fx :
  LVFree x ∉ dom Σ ->
  ext_out Fx = {[x]} ->
  res_extend_by m Fx mx ->
  res_models m (context_ty_wf_formula Σ τ) ->
  res_models mx (context_ty_wf_formula (<[LVFree x := T]> Σ) τ).
Proof.
  intros HxΣ Hout Hext Hm.
  apply context_ty_wf_formula_models_iff in Hm as [Hlc [Hsub Hbasic]].
  apply context_ty_wf_formula_models_iff.
	  split.
	  - intros v Hv.
	    rewrite (dom_insert_L (M := gmap logic_var) (D := gset logic_var)) in Hv.
    apply elem_of_union in Hv as [Hv|Hv].
    + rewrite elem_of_singleton in Hv. subst v. exact I.
    + exact (Hlc v Hv).
  - split.
    + pose proof (res_extend_by_dom_base_subset m Fx mx Hext) as Hbase_dom.
	      pose proof (res_extend_by_dom_output_subset m Fx mx Hext) as Hout_dom.
	      intros a Ha.
	      rewrite (dom_insert_L (M := gmap logic_var) (D := gset logic_var)) in Ha.
      rewrite lvars_fv_union, lvars_fv_singleton_free in Ha.
      apply elem_of_union in Ha as [Ha|Ha].
      * rewrite elem_of_singleton in Ha. subst a.
        unfold ext_out in Hout.
        rewrite Hout in Hout_dom. set_solver.
      * set_solver.
    + change (basic_context_ty_lvars
        (dom ((<[LVFree x := T]> (Σ : gmap logic_var ty))
          : gmap logic_var ty)) τ).
      apply basic_context_ty_lvars_insert_fresh. exact Hbasic.
Qed.

Lemma expr_basic_typing_lqual_denote_iff Σ e T (m : WfWorldT) :
  logic_qualifier_denote (expr_basic_typing_lqual Σ e T) m <->
  lc_lvars (dom Σ) /\
  lvars_fv (dom Σ) ⊆ world_dom (m : WorldT) /\
  basic_tm_has_ltype Σ e T.
Proof.
  unfold expr_basic_typing_lqual, logic_qualifier_denote.
  split.
  - intros [Hlc [Hsub Hbasic]]. tauto.
  - intros [Hlc [Hsub Hbasic]]. exists Hlc, Hsub. exact Hbasic.
Qed.

Lemma expr_basic_typing_formula_models_iff Σ e T (m : WfWorldT) :
  res_models m (expr_basic_typing_formula Σ e T) <->
  lc_lvars (dom Σ) /\
  lvars_fv (dom Σ) ⊆ world_dom (m : WorldT) /\
  basic_tm_has_ltype Σ e T.
Proof.
  unfold res_models, expr_basic_typing_formula.
  cbn [formula_measure res_models_fuel].
  split.
  - intros [_ Hden].
    apply expr_basic_typing_lqual_denote_iff. exact Hden.
  - intros Hden. split.
    + destruct Hden as [_ [Hsub _]]. exact Hsub.
    + apply expr_basic_typing_lqual_denote_iff. exact Hden.
Qed.

Lemma expr_basic_typing_formula_scope_dom Σ e T (m : WfWorldT) :
  res_models m (expr_basic_typing_formula Σ e T) ->
  lvars_fv (dom Σ) ⊆ world_dom (m : WorldT).
Proof.
  intros Hmodels.
  apply expr_basic_typing_formula_models_iff in Hmodels as [_ [Hsub _]].
  exact Hsub.
Qed.

Lemma expr_basic_typing_formula_basic_ltype Σ e T (m : WfWorldT) :
  res_models m (expr_basic_typing_formula Σ e T) ->
  basic_tm_has_ltype Σ e T.
Proof.
  intros Hmodels.
  apply expr_basic_typing_formula_models_iff in Hmodels as [_ [_ Hbasic]].
  exact Hbasic.
Qed.

Lemma expr_basic_typing_formula_tapp_tm_tlete_assoc
    (Σ : lty_env) e1 e2 y T (m : WfWorldT) :
  lc_tm (tlete e1 e2) ->
  res_models m (expr_basic_typing_formula Σ
    (tlete e1 (tapp_tm e2 (vfvar y))) T) ->
  res_models m (expr_basic_typing_formula Σ
    (tapp_tm (tlete e1 e2) (vfvar y)) T).
Proof.
  intros Hlc Hmodels.
  apply expr_basic_typing_formula_models_iff in Hmodels as [HlcΣ [Hsub Hbasic]].
  apply expr_basic_typing_formula_models_iff.
  split; [exact HlcΣ|].
  split; [exact Hsub|].
  eapply basic_tm_has_ltype_tapp_tm_tlete_assoc; eauto.
Qed.

Lemma expr_basic_typing_formula_tapp_tm_tlete_assoc_rev
    (Σ : lty_env) e1 e2 y T (m : WfWorldT) :
  lc_tm (tlete e1 e2) ->
  res_models m (expr_basic_typing_formula Σ
    (tapp_tm (tlete e1 e2) (vfvar y)) T) ->
  res_models m (expr_basic_typing_formula Σ
    (tlete e1 (tapp_tm e2 (vfvar y))) T).
Proof.
  intros Hlc Hmodels.
  apply expr_basic_typing_formula_models_iff in Hmodels as [HlcΣ [Hsub Hbasic]].
  apply expr_basic_typing_formula_models_iff.
  split; [exact HlcΣ|].
  split; [exact Hsub|].
  eapply basic_tm_has_ltype_tapp_tm_tlete_assoc_rev; eauto.
Qed.

Lemma expr_basic_typing_formula_tapp_tlete_assoc_spine
    (Σ : lty_env) e1 e2 y ys T (m : WfWorldT) :
  lc_tm (tlete e1 e2) ->
  res_models m (expr_basic_typing_formula Σ
    (tapp_tm_fvar_spine (tlete e1 (tapp_tm e2 (vfvar y))) ys) T) ->
  res_models m (expr_basic_typing_formula Σ
    (tapp_tm_fvar_spine (tapp_tm (tlete e1 e2) (vfvar y)) ys) T).
Proof.
  intros Hlc Hmodels.
  apply expr_basic_typing_formula_models_iff in Hmodels as [HlcΣ [Hsub Hbasic]].
  apply expr_basic_typing_formula_models_iff.
  split; [exact HlcΣ|].
  split; [exact Hsub|].
  eapply basic_tm_has_ltype_tapp_tlete_assoc_spine; eauto.
Qed.

Lemma res_models_open_expr_basic_typing_to_open
    k y Σ e T (m : WfWorldT) :
  y ∉ lvars_fv (dom Σ) ∪ fv_tm e ->
  res_models m (formula_open k y (expr_basic_typing_formula Σ e T)) ->
  res_models m
    (expr_basic_typing_formula
      (lty_env_open_one k y Σ) (open_tm k (vfvar y) e) T).
Proof.
  intros Hy Hmodels.
  unfold res_models, expr_basic_typing_formula, expr_basic_typing_lqual in Hmodels.
  cbn [formula_open lqual_open formula_measure res_models_fuel] in Hmodels.
  destruct Hmodels as [_ Hden].
  unfold logic_qualifier_denote in Hden.
  cbn [lqual_dom lqual_prop] in Hden.
  destruct Hden as [Hlc [Hsub Hbasic]].
  apply expr_basic_typing_formula_models_iff.
  split.
  - rewrite lty_env_open_one_dom. exact Hlc.
  - split.
    + rewrite lty_env_open_one_dom. exact Hsub.
    + apply basic_tm_has_ltype_open_one_fresh; assumption.
Qed.

Lemma res_models_open_expr_basic_typing_bind0_to_open
    y Σ T e U (m : WfWorldT) :
  LVFree y ∉ dom Σ ->
  lty_env_closed Σ ->
  y ∉ fv_tm e ->
  res_models m
    (formula_open 0 y (expr_basic_typing_formula (typed_lty_env_bind Σ T) e U)) ->
  res_models m
    (expr_basic_typing_formula
      (<[LVFree y := T]> Σ) (open_tm 0 (vfvar y) e) U).
Proof.
  intros Hfresh Hclosed Hye Hmodels.
  apply res_models_open_expr_basic_typing_to_open in Hmodels.
  - rewrite typed_lty_env_bind_open_current in Hmodels by assumption.
    exact Hmodels.
  - rewrite typed_lty_env_bind_lvars_fv_dom.
    intros Hy.
    apply elem_of_union in Hy as [HyΣ|Hy]; [|exact (Hye Hy)].
    apply Hfresh. apply lvars_fv_elem. exact HyΣ.
Qed.

Lemma res_models_open_expr_basic_typing_iff
    k y Σ e T (m : WfWorldT) :
  y ∉ lvars_fv (dom Σ) ∪ fv_tm e ->
  res_models m (formula_open k y (expr_basic_typing_formula Σ e T)) <->
  res_models m
    (expr_basic_typing_formula
      (lty_env_open_one k y Σ) (open_tm k (vfvar y) e) T).
Proof.
  intros Hy. split.
  - apply res_models_open_expr_basic_typing_to_open.
    exact Hy.
  - intros Hmodels.
    apply expr_basic_typing_formula_models_iff in Hmodels
      as [Hlc [Hsub Hbasic]].
    unfold res_models, expr_basic_typing_formula, expr_basic_typing_lqual.
    cbn [formula_open lqual_open formula_measure res_models_fuel].
    split.
    + rewrite lty_env_open_one_dom in Hsub. exact Hsub.
    + unfold logic_qualifier_denote.
      cbn [lqual_dom lqual_prop].
      split.
      * rewrite lty_env_open_one_dom in Hlc. exact Hlc.
      * split.
        -- rewrite lty_env_open_one_dom in Hsub. exact Hsub.
        -- eapply basic_tm_has_ltype_close_one_fresh; eauto.
Qed.

Lemma res_models_open_expr_basic_typing_bind0_iff
    y Σ T e U (m : WfWorldT) :
  LVFree y ∉ dom Σ ->
  lty_env_closed Σ ->
  y ∉ fv_tm e ->
  res_models m
    (formula_open 0 y (expr_basic_typing_formula (typed_lty_env_bind Σ T) e U)) <->
  res_models m
    (expr_basic_typing_formula
      (<[LVFree y := T]> Σ) (open_tm 0 (vfvar y) e) U).
Proof.
  intros Hfresh Hclosed Hye.
  rewrite (res_models_open_expr_basic_typing_iff
    0 y (typed_lty_env_bind Σ T) e U m).
  - rewrite typed_lty_env_bind_open_current by assumption.
    reflexivity.
  - rewrite typed_lty_env_bind_lvars_fv_dom.
    intros Hy.
    apply elem_of_union in Hy as [HyΣ|Hy]; [|exact (Hye Hy)].
    apply Hfresh. apply lvars_fv_elem. exact HyΣ.
Qed.

Lemma expr_basic_typing_formula_insert_fresh_lvar
    (Σ : lty_env) e U (m mx : WfWorldT) x T Fx :
  LVFree x ∉ dom Σ ->
  ext_out Fx = {[x]} ->
  res_extend_by m Fx mx ->
  res_models m (expr_basic_typing_formula Σ e U) ->
  res_models mx (expr_basic_typing_formula (<[LVFree x := T]> Σ) e U).
Proof.
  intros HxΣ Hout Hext Hm.
  apply expr_basic_typing_formula_models_iff in Hm as [Hlc [Hsub Hbasic]].
  apply expr_basic_typing_formula_models_iff.
	  split.
	  - intros v Hv.
	    rewrite (dom_insert_L (M := gmap logic_var) (D := gset logic_var)) in Hv.
    apply elem_of_union in Hv as [Hv|Hv].
    + rewrite elem_of_singleton in Hv. subst v. exact I.
    + exact (Hlc v Hv).
  - split.
    + pose proof (res_extend_by_dom_base_subset m Fx mx Hext) as Hbase_dom.
	      pose proof (res_extend_by_dom_output_subset m Fx mx Hext) as Hout_dom.
	      intros a Ha.
	      rewrite (dom_insert_L (M := gmap logic_var) (D := gset logic_var)) in Ha.
      rewrite lvars_fv_union, lvars_fv_singleton_free in Ha.
      apply elem_of_union in Ha as [Ha|Ha].
      * rewrite elem_of_singleton in Ha. subst a.
        unfold ext_out in Hout.
        rewrite Hout in Hout_dom. set_solver.
      * set_solver.
    + apply basic_tm_has_ltype_insert_fresh_lvar; assumption.
Qed.

Lemma context_ty_wf_formula_drop_fresh_lvar
    (Σ : lty_env) (τ : context_ty) (m mx : WfWorldT) x T Fx :
  LVFree x ∉ dom Σ ->
  LVFree x ∉ context_ty_lvars τ ->
  ext_out Fx = {[x]} ->
  res_extend_by m Fx mx ->
  res_models mx (context_ty_wf_formula (<[LVFree x := T]> Σ) τ) ->
  res_models m (context_ty_wf_formula Σ τ).
Proof.
  intros HxΣ Hxτ Hout Hext Hmx.
  apply context_ty_wf_formula_models_iff in Hmx as [Hlcx [Hsubx Hbasicx]].
  apply context_ty_wf_formula_models_iff.
	  split.
	  - intros v Hv.
	    apply Hlcx.
	    destruct (decide (v = LVFree x)) as [->|Hvne].
	    + apply elem_of_dom. exists T. rewrite lookup_insert_eq. reflexivity.
	    + apply elem_of_dom in Hv as [Tv HTv].
	      apply elem_of_dom. exists Tv.
      rewrite lookup_insert_ne by congruence. exact HTv.
  - split.
    + pose proof (res_extend_by_dom m Fx mx Hext) as Hdom.
      intros z Hz.
      specialize (Hsubx z).
      unfold ext_out in Hout.
      rewrite Hdom, Hout in Hsubx.
      apply elem_of_union in Hsubx as [Hzm|Hzx].
      * exact Hzm.
      * rewrite elem_of_singleton in Hzx. subst z.
        exfalso. apply HxΣ. rewrite <- lvars_fv_elem. exact Hz.
	      * rewrite lvars_fv_elem.
	        rewrite lvars_fv_elem in Hz.
	        destruct (decide (z = x)) as [->|Hzx].
	        -- exfalso. exact (HxΣ Hz).
	        -- apply elem_of_dom in Hz as [Tz HTz].
	           apply elem_of_dom. exists Tz.
           rewrite lookup_insert_ne by congruence. exact HTz.
    + destruct Hbasicx as [Hvars Hshape].
	      split; [| exact Hshape].
	      intros v Hv.
	      specialize (Hvars v Hv).
	      assert (Hvne : v <> LVFree x).
      { intros ->. exact (Hxτ Hv). }
      apply elem_of_dom in Hvars as [Tv HTv].
      rewrite lookup_insert_ne in HTv by congruence.
      apply elem_of_dom_2 in HTv. exact HTv.
Qed.

Lemma expr_basic_typing_formula_tlete_intro
    (Σ : lty_env) e1 e2 T (m : WfWorldT) :
  res_models m (basic_world_formula Σ) ->
  lty_env_to_atom_env Σ ⊢ₑ tlete e1 e2 ⋮ T ->
  res_models m (expr_basic_typing_formula Σ (tlete e1 e2) T).
Proof.
  intros Hworld Hty.
  apply basic_world_formula_models_iff in Hworld as [Hlc [Hsub _]].
  apply expr_basic_typing_formula_models_iff.
  split; [exact Hlc|].
  split; [exact Hsub|].
  apply basic_tm_has_ltype_of_atom_typing; [|exact Hty].
  exact Hlc.
Qed.

End BasicTypingFormula.
