(** * BasicDenotation.StoreTyping

    Basic typing for stores, worlds, and extension outputs. *)

From ContextBasicDenotation Require Import Notation.
From ContextLogic Require Import FormulaConnectives.
From ContextAlgebra Require Import ResourceAlgebra.

Section StoreTyping.

Definition storeA_has_type
    {K : Type} `{Countable K}
    (Σ : gmap K ty) (σ : gmap K value) : Prop :=
  forall x T v,
    Σ !! x = Some T ->
    σ !! x = Some v ->
    ∅ ⊢ᵥ v ⋮ T.

Definition atom_store_has_ltype (Σ : lty_env) (σ : StoreT) : Prop :=
  forall x v,
    σ !! x = Some v ->
    exists T,
      Σ !! LVFree x = Some T /\
      ∅ ⊢ᵥ v ⋮ T.

Definition worldA_has_type
    {K : Type} `{Countable K}
    (Σ : gmap K ty) (m : @WorldA K _ _ value) : Prop :=
  dom Σ ⊆ worldA_dom m /\
  forall σ, m σ -> storeA_has_type Σ σ.

Definition world_has_type (Σ : gmap atom ty) (m : World) : Prop :=
  worldA_has_type Σ m.

Definition lworld_has_type (Σ : lty_env) (m : LWorld) : Prop :=
  worldA_has_type Σ m.

Definition wfworld_closed_on (X : aset) (m : WfWorld) : Prop :=
  forall σ, (m : World) σ -> store_closed (store_restrict σ X).

Definition wfworld_closed (m : WfWorld) : Prop :=
  wfworld_closed_on (world_dom (m : World)) m.

Definition basic_world_lqual (Σ : lty_env) : logic_qualifier :=
  lqual (dom Σ) (fun w => lworld_has_type Σ (@lw value _ w : LWorld)).

Definition basic_world_formula (Σ : lty_env) : Formula :=
  FAtom (basic_world_lqual Σ).

Lemma atom_store_has_ltype_closed Σ σ :
  atom_store_has_ltype Σ σ ->
  store_closed σ.
Proof.
  intros Hty. split.
  - unfold closed_env. apply map_Forall_lookup_2.
    intros x v Hlook.
    destruct (Hty x v Hlook) as [T [_ Hv]].
    pose proof (basic_typing_contains_fv_value ∅ v T Hv).
    set_solver.
  - unfold lc_env. apply map_Forall_lookup_2.
    intros x v Hlook.
    destruct (Hty x v Hlook) as [T [_ Hv]].
    exact (typing_value_lc _ _ _ Hv).
Qed.

Lemma formula_fv_basic_world_formula (Σ : lty_env) :
  formula_fv (basic_world_formula Σ) = lvars_fv (dom Σ).
Proof. apply formula_fv_atom. Qed.

Lemma wfworld_closed_on_mono X Y (m : WfWorld) :
  X ⊆ Y ->
  wfworld_closed_on Y m ->
  wfworld_closed_on X m.
Proof.
  intros HXY Hclosed σ Hσ.
  specialize (Hclosed σ Hσ).
  rewrite <- (storeA_restrict_twice_subset σ Y X HXY).
  apply store_closed_restrict. exact Hclosed.
Qed.

Lemma wfworld_closed_on_le X (m n : WfWorld) :
  X ⊆ world_dom (m : World) ->
  m ⊑ n ->
  wfworld_closed_on X m ->
  wfworld_closed_on X n.
Proof.
  intros HXm Hle Hclosed σ Hσ.
  assert (Hmσ : (m : World) (store_restrict σ (world_dom (m : World)))).
  {
    change ((m : World) = raw_restrict (n : World) (world_dom (m : World)))
      in Hle.
    rewrite Hle.
    unfold raw_restrict.
    cbn [world_stores worldA_stores].
    exists σ. split; [exact Hσ |].
	    pose proof (wfworld_store_dom n σ Hσ) as Hdomσ.
	    pose proof (f_equal world_dom Hle) as Hdomle.
	    change (world_dom (m : World) =
	      worldA_dom (ResourceCore.rawA_restrict (n : World)
	        (world_dom (m : World)))) in Hdomle.
	    change (storeA_restrict σ (world_dom (m : World)) =
	      storeA_restrict σ
	        (worldA_dom (ResourceCore.rawA_restrict (n : World)
	          (world_dom (m : World))) : aset)).
	    rewrite <- Hdomle. reflexivity.
  }
  specialize (Hclosed _ Hmσ).
  rewrite storeA_restrict_twice_subset in Hclosed by exact HXm.
  exact Hclosed.
Qed.

Lemma wfworld_closed_on_restrict X Y (m : WfWorld) :
  X ⊆ Y ->
  wfworld_closed_on X m ->
  wfworld_closed_on X (res_restrict m Y).
Proof.
  intros HXY Hclosed σ Hσ.
  destruct Hσ as [τ [Hτ Hσ]].
  subst σ.
  specialize (Hclosed τ Hτ).
  rewrite (storeA_restrict_twice_subset τ Y X HXY).
  exact Hclosed.
Qed.

Lemma store_closed_restrict_union_from_parts
    (σ : StoreT) X Y :
  store_closed (store_restrict σ X) ->
  store_closed (store_restrict σ Y) ->
  store_closed (store_restrict σ (X ∪ Y)).
Proof.
  intros [HXclosed HXlc] [HYclosed HYlc].
  split.
  - unfold closed_env.
    apply map_Forall_lookup_2. intros x v Hlookup.
    apply storeA_restrict_lookup_some in Hlookup as [Hxy Hlookup].
    apply elem_of_union in Hxy as [Hx|Hy].
    + eapply closed_env_lookup; [exact HXclosed|].
      apply storeA_restrict_lookup_some_2; [exact Hlookup|exact Hx].
    + eapply closed_env_lookup; [exact HYclosed|].
      apply storeA_restrict_lookup_some_2; [exact Hlookup|exact Hy].
  - unfold lc_env.
    apply map_Forall_lookup_2. intros x v Hlookup.
    apply storeA_restrict_lookup_some in Hlookup as [Hxy Hlookup].
    apply elem_of_union in Hxy as [Hx|Hy].
    + eapply lc_env_lookup; [exact HXlc|].
      apply storeA_restrict_lookup_some_2; [exact Hlookup|exact Hx].
    + eapply lc_env_lookup; [exact HYlc|].
      apply storeA_restrict_lookup_some_2; [exact Hlookup|exact Hy].
Qed.

Lemma wfworld_closed_on_union X Y (m : WfWorld) :
  wfworld_closed_on X m ->
  wfworld_closed_on Y m ->
  wfworld_closed_on (X ∪ Y) m.
Proof.
  intros HX HY σ Hσ.
  apply store_closed_restrict_union_from_parts; [apply HX | apply HY];
    exact Hσ.
Qed.

Lemma storeA_has_type_swap
    {K : Type} `{Countable K} 
    (x y : K) (Σ : gmap K ty) (σ : gmap K value) :
  storeA_has_type (storeA_swap x y Σ) σ <->
  storeA_has_type Σ (storeA_swap x y σ).
Proof.
  split; intros Htyped z T v HΣ Hσ.
  - eapply Htyped with (x := swap x y z).
    + rewrite storeA_swap_lookup. exact HΣ.
    + rewrite storeA_swap_lookup_inv in Hσ. exact Hσ.
  - rewrite storeA_swap_lookup_inv in HΣ.
    eapply Htyped with (x := swap x y z).
    + exact HΣ.
    + rewrite storeA_swap_lookup. exact Hσ.
Qed.

Lemma lworld_has_type_swap k y Σ (w : LWfWorld) :
  lworld_has_type (lty_env_open_one k y Σ) (w : LWorld) <->
  lworld_has_type Σ (lres_swap (LVBound k) (LVFree y) w : LWorld).
Proof.
  unfold lworld_has_type, worldA_has_type.
  split; intros [Hdom Hstores]; split.
  - rewrite lty_env_open_one_dom in Hdom.
    rewrite lworld_dom_lres_swap.
    change (dom (Σ : gmap logic_var ty) ⊆
      lvars_open k y (lworld_dom (w : LWorld))).
    rewrite <- (lvars_open_involutive k y (worldA_dom (w : LWorld))) in Hdom.
    apply lvars_open_subseteq_iff in Hdom. exact Hdom.
  - intros σ Hσ.
    unfold lres_swap in Hσ.
    destruct Hσ as [σ0 [Hσ0 Hrekey]]. subst σ.
    change (storeA_has_type Σ (storeA_swap (LVBound k) (LVFree y) σ0)).
    apply storeA_has_type_swap.
    change (storeA_has_type
      (storeA_swap (LVBound k) (LVFree y) Σ) σ0).
    apply Hstores. exact Hσ0.
  - rewrite lworld_dom_lres_swap in Hdom.
    rewrite lty_env_open_one_dom.
    change (lvars_open k y (dom (Σ : gmap logic_var ty)) ⊆
      lworld_dom (w : LWorld)).
    rewrite <- (lvars_open_involutive k y (lworld_dom (w : LWorld))).
    apply lvars_open_subseteq_iff. exact Hdom.
  - intros σ Hσ.
    apply storeA_has_type_swap.
    apply Hstores.
    unfold lres_swap.
    exists σ. split; [exact Hσ | reflexivity].
Qed.

Lemma formula_open_basic_world_formula k y Σ :
  formula_open k y (basic_world_formula Σ) =
  basic_world_formula (lty_env_open_one k y Σ).
Proof.
  unfold basic_world_formula, basic_world_lqual.
  cbn [formula_open lqual_open].
  f_equal.
  apply logic_qualifier_ext.
  - rewrite lty_env_open_one_dom. reflexivity.
  - intros w1 w2 Hlw. cbn [lqual_prop].
    split; intros Htyped.
    + apply (proj2 (lworld_has_type_swap k y Σ (@lw value _ w2))).
      change (lworld_has_type Σ
        (lres_swap (LVBound k) (LVFree y) (@lw value _ w1) : LWorld)) in Htyped.
      rewrite Hlw in Htyped. exact Htyped.
    + apply (proj1 (lworld_has_type_swap k y Σ (@lw value _ w2))) in Htyped.
      change (lworld_has_type Σ
        (lres_swap (LVBound k) (LVFree y) (@lw value _ w1) : LWorld)).
      rewrite Hlw. exact Htyped.
Qed.

Lemma formula_open_basic_world_bind0 y Σ T :
  LVFree y ∉ dom Σ ->
  lty_env_closed Σ ->
  formula_open 0 y (basic_world_formula (typed_lty_env_bind Σ T)) =
  basic_world_formula (<[LVFree y := T]> Σ).
Proof.
  intros Hfresh Hclosed.
  rewrite formula_open_basic_world_formula.
  rewrite typed_lty_env_bind_open_current by assumption.
  reflexivity.
Qed.

Lemma formula_open_env_basic_world_formula η Σ :
  open_env_fresh_for_lvars η (dom Σ) ->
  open_env_values_inj η ->
  formula_open_env η (basic_world_formula Σ) =
  basic_world_formula (lty_env_open_lvars η Σ).
Proof.
  revert Σ.
  induction η as [|k x η Hnone Hfold IH] using fin_maps.map_fold_ind.
  - intros Σ _ _.
    rewrite formula_open_env_empty, lty_env_open_lvars_empty. reflexivity.
  - intros Σ Hfresh Hinj.
    pose proof (open_env_values_inj_insert_inv η k x Hnone Hinj)
      as [Hinjη Havoid].
    pose proof (open_env_fresh_for_lvars_insert_tail η k x
      (dom Σ) Hnone Hfresh) as Hfreshη.
    rewrite formula_open_env_insert_fresh by assumption.
    rewrite IH by (exact Hfreshη || exact Hinjη).
    rewrite formula_open_basic_world_formula.
    rewrite lty_env_open_lvars_insert_fresh by assumption.
    reflexivity.
Qed.

Definition extension_has_type
    (Σout : gmap atom ty) (min : WfWorld) (F : fiber_extension) : Prop :=
  world_dom (min : World) = ext_in F /\
  dom Σout = ext_out F /\
  forall σ my,
    (min : World) σ ->
    ext_rel F σ my ->
    world_has_type Σout (my : World).

Definition extension_has_ltype
    (Σout : lty_env) (min : WfWorld) (F : fiber_extension) : Prop :=
  world_dom (min : World) = ext_in F /\
  lc_lvars (dom Σout) /\
  lvars_fv (dom Σout) = ext_out F /\
  forall σ my,
    (min : World) σ ->
    ext_rel F σ my ->
    lworld_has_type Σout (res_lift_free my : LWorld).

Lemma storeA_has_type_restrict_store
    {K : Type} `{Countable K}
    (Σ : gmap K ty) (σ : gmap K value) X :
  dom Σ ⊆ X ->
  storeA_has_type Σ (storeA_restrict σ X) <->
  storeA_has_type Σ σ.
Proof.
  intros HΣX. split; intros Htyped x T v HΣ Hσ.
	  - eapply Htyped; [exact HΣ|].
	    apply storeA_restrict_lookup_some_2; [exact Hσ|].
	    apply HΣX. eapply elem_of_dom_2; exact HΣ.
  - eapply Htyped; [exact HΣ|].
    apply storeA_restrict_lookup_some in Hσ as [_ Hσ].
    exact Hσ.
Qed.

Lemma storeA_has_type_lift_free_restrict_fv
    (Σ : lty_env) (σ : Store (V := value)) :
  lc_lvars (dom Σ) ->
  storeA_has_type Σ
    (lstore_lift_free (store_restrict σ (lvars_fv (dom Σ)))) <->
  storeA_has_type Σ (lstore_lift_free σ).
	Proof.
	  intros Hlc. split; intros Htyped v T u HΣ Hu.
	  - destruct v as [k | x].
	    + exfalso. apply (Hlc (LVBound k)).
	      eapply elem_of_dom_2; exact HΣ.
    + eapply Htyped; [exact HΣ|].
      change (((lstore_lift_free (store_restrict σ (lvars_fv (dom Σ)))
        : LStore (V := value)) : gmap logic_var value) !! LVFree x = Some u).
      rewrite lstore_lift_free_lookup_free.
      apply storeA_restrict_lookup_some_2.
	      * change (((lstore_lift_free σ : LStore (V := value)) : gmap logic_var value)
	          !! LVFree x = Some u) in Hu.
	        rewrite lstore_lift_free_lookup_free in Hu. exact Hu.
	      * apply lvars_fv_elem. eapply elem_of_dom_2; exact HΣ.
  - destruct v as [k | x].
    + change (((lstore_lift_free (store_restrict σ (lvars_fv (dom Σ)))
        : LStore (V := value)) : gmap logic_var value) !! LVBound k = Some u) in Hu.
      rewrite lstore_lift_free_lookup_bound in Hu. discriminate.
    + eapply Htyped; [exact HΣ|].
      change (((lstore_lift_free (store_restrict σ (lvars_fv (dom Σ)))
        : LStore (V := value)) : gmap logic_var value) !! LVFree x = Some u) in Hu.
      rewrite lstore_lift_free_lookup_free in Hu.
      apply storeA_restrict_lookup_some in Hu as [_ Hu].
      change (((lstore_lift_free σ : LStore (V := value)) : gmap logic_var value) !! LVFree x = Some u).
      rewrite lstore_lift_free_lookup_free. exact Hu.
Qed.

Lemma basic_world_lqual_denote_spec (Σ : lty_env) (m : WfWorld) :
  logic_qualifier_denote (basic_world_lqual Σ) m <->
  exists (Hlc : lc_lvars (dom Σ))
         (Hsub : lvars_fv (dom Σ) ⊆ world_dom (m : World)),
    lworld_has_type Σ
      (@lw value (dom Σ)
        (lworld_on_lift (dom Σ) m Hlc Hsub) : LWorld).
Proof.
  unfold basic_world_lqual, logic_qualifier_denote. simpl.
  split; intros [Hlc [Hsub Htyped]]; exists Hlc, Hsub; exact Htyped.
Qed.

Lemma basic_world_lqual_denote_iff_res_lift_free
    (Σ : lty_env) (m : WfWorld) :
  logic_qualifier_denote (basic_world_lqual Σ) m <->
  lc_lvars (dom Σ) /\
  lvars_fv (dom Σ) ⊆ world_dom (m : World) /\
  lworld_has_type Σ (res_lift_free m : LWorld).
Proof.
  split.
  - intros Hden.
    apply basic_world_lqual_denote_spec in Hden.
    destruct Hden as [Hlc [Hsub Htyped_on]].
    split; [exact Hlc|]. split; [exact Hsub|].
    destruct Htyped_on as [_ Hstores_on].
    unfold lworld_has_type, worldA_has_type. split.
    + intros v Hv.
      rewrite res_lift_free_dom.
      destruct v as [k | x].
      * exfalso. exact (Hlc (LVBound k) Hv).
      * unfold lvars_of_atoms. apply elem_of_map.
        exists x. split; [reflexivity|].
        apply Hsub. apply lvars_fv_elem. exact Hv.
    + intros τ Hτ.
      destruct Hτ as [σ [Hσ ->]].
      apply (proj1 (storeA_has_type_lift_free_restrict_fv Σ σ Hlc)).
      apply (proj1 (storeA_has_type_restrict_store Σ
        (lstore_lift_free (store_restrict σ (lvars_fv (dom Σ))))
        (dom Σ) ltac:(set_solver))).
      apply Hstores_on.
      unfold lworld_on_lift. cbn [lw lraw_world raw_worldA worldA_stores].
      exists (lstore_lift_free (store_restrict σ (lvars_fv (dom Σ)))).
      split.
      * exists (store_restrict σ (lvars_fv (dom Σ))). split; [|reflexivity].
        simpl. exists σ. split; [exact Hσ | reflexivity].
      * reflexivity.
  - intros [Hlc [Hsub Htyped_free]].
    apply basic_world_lqual_denote_spec.
    exists Hlc, Hsub.
    destruct Htyped_free as [_ Hstores_free].
    unfold lworld_has_type, worldA_has_type. split.
    + intros v Hv.
      change (v ∈ lworld_dom
        (@lw value (dom Σ) (lworld_on_lift (dom Σ) m Hlc Hsub))).
      rewrite (@lw_dom value (dom Σ) (lworld_on_lift (dom Σ) m Hlc Hsub)).
      exact Hv.
    + intros τ Hτ.
      unfold lworld_on_lift in Hτ.
      cbn [lw lraw_world raw_worldA worldA_stores] in Hτ.
      destruct Hτ as [τ0 [Hτ0 Hrestrict]]. subst τ.
      destruct Hτ0 as [σr [Hσr ->]].
      simpl in Hσr.
      destruct Hσr as [σ [Hσ Hσr]]. subst σr.
      apply (proj2 (storeA_has_type_restrict_store Σ
        (lstore_lift_free (store_restrict σ (lvars_fv (dom Σ))))
        (dom Σ) ltac:(set_solver))).
      apply (proj2 (storeA_has_type_lift_free_restrict_fv Σ σ Hlc)).
      apply Hstores_free. exists σ. split; [exact Hσ | reflexivity].
Qed.

Lemma basic_world_formula_models_iff (Σ : lty_env) (m : WfWorld) :
  res_models m (basic_world_formula Σ) <->
  lc_lvars (dom Σ) /\
  lvars_fv (dom Σ) ⊆ world_dom (m : World) /\
  lworld_has_type Σ (res_lift_free m : LWorld).
Proof.
  unfold res_models, basic_world_formula.
  cbn [formula_measure res_models_fuel].
  split.
  - intros [_ Hden].
    apply basic_world_lqual_denote_iff_res_lift_free. exact Hden.
  - intros Hden. split.
    + destruct Hden as [_ [Hsub _]].
      unfold formula_scoped_in_world.
      rewrite formula_fv_atom. exact Hsub.
    + apply basic_world_lqual_denote_iff_res_lift_free. exact Hden.
Qed.

Lemma basic_world_formula_subenv
    (Σsmall Σbig : lty_env) (m : WfWorld) :
  (forall v T, Σsmall !! v = Some T -> Σbig !! v = Some T) ->
  res_models m (basic_world_formula Σbig) ->
  res_models m (basic_world_formula Σsmall).
Proof.
  intros Hlookup Hbig.
  apply basic_world_formula_models_iff in Hbig as [Hlc_big [Hscope_big Htyped_big]].
  apply basic_world_formula_models_iff.
  assert (Hdom : dom (Σsmall : gmap logic_var ty) ⊆
                 dom (Σbig : gmap logic_var ty)).
  {
    intros v Hv.
    apply elem_of_dom in Hv as [T Hv].
    apply elem_of_dom. exists T. eapply Hlookup. exact Hv.
  }
  split.
  - intros v Hv. apply Hlc_big. exact (Hdom v Hv).
  - split.
    + intros a Ha. apply Hscope_big.
      apply lvars_fv_elem in Ha. apply lvars_fv_elem.
      exact (Hdom (LVFree a) Ha).
    + unfold lworld_has_type, worldA_has_type in Htyped_big |- *.
      destruct Htyped_big as [Hdom_big Hstores_big].
      split.
      * intros v Hv. apply Hdom_big. exact (Hdom v Hv).
      * intros σ Hσ v T val HΣ Hv.
        eapply Hstores_big; [exact Hσ | | exact Hv].
        eapply Hlookup. exact HΣ.
Qed.

Lemma basic_world_formula_union
    (Σ1 Σ2 : lty_env) (m : WfWorld) :
  res_models m (basic_world_formula Σ1) ->
  res_models m (basic_world_formula Σ2) ->
  res_models m (basic_world_formula
    ((@union (gmap logic_var ty) _ Σ1 Σ2) : lty_env)).
Proof.
  intros H1 H2.
  apply basic_world_formula_models_iff in H1 as [Hlc1 [Hscope1 Htyped1]].
  apply basic_world_formula_models_iff in H2 as [Hlc2 [Hscope2 Htyped2]].
  apply basic_world_formula_models_iff.
  split.
  - intros v Hv.
    change (v ∈ dom ((Σ1 : gmap logic_var ty) ∪ (Σ2 : gmap logic_var ty))) in Hv.
    rewrite dom_union_L in Hv.
    apply elem_of_union in Hv as [Hv|Hv]; [apply Hlc1 | apply Hlc2]; exact Hv.
  - split.
    + intros a Ha.
      change (a ∈ lvars_fv
        (dom ((Σ1 : gmap logic_var ty) ∪ (Σ2 : gmap logic_var ty)))) in Ha.
      rewrite dom_union_L, lvars_fv_union in Ha.
      apply elem_of_union in Ha as [Ha|Ha]; [apply Hscope1 | apply Hscope2]; exact Ha.
    + unfold lworld_has_type, worldA_has_type in Htyped1, Htyped2 |- *.
      destruct Htyped1 as [Hdom1 Hstores1].
      destruct Htyped2 as [Hdom2 Hstores2].
      split.
      * intros v Hv.
        change (v ∈ dom ((Σ1 : gmap logic_var ty) ∪ (Σ2 : gmap logic_var ty))) in Hv.
        rewrite dom_union_L in Hv.
        apply elem_of_union in Hv as [Hv|Hv]; [apply Hdom1 | apply Hdom2]; exact Hv.
      * intros σ Hσ v T val HΣ Hv.
        change (((Σ1 : gmap logic_var ty) ∪ (Σ2 : gmap logic_var ty)) !!
          v = Some T) in HΣ.
        rewrite map_lookup_union_Some_raw in HΣ.
        destruct HΣ as [HΣ1 | [_ HΣ2]].
        -- eapply Hstores1; eauto.
        -- eapply Hstores2; eauto.
Qed.

Lemma basic_world_formula_res_subset
    (Σ : lty_env) (m n : WfWorld) :
  res_subset n m ->
  res_models m (basic_world_formula Σ) ->
  res_models n (basic_world_formula Σ).
Proof.
  intros Hsub Hm.
  destruct Hsub as [Hdom Hstores].
  apply basic_world_formula_models_iff in Hm as [Hlc [Hscope Htyped]].
  apply basic_world_formula_models_iff.
  split; [exact Hlc|]. split.
  - intros a Ha.
    set_solver.
  - unfold lworld_has_type, worldA_has_type in Htyped |- *.
    destruct Htyped as [Hdom_typed Hstores_typed].
    split.
    + intros v Hv.
      rewrite !res_lift_free_dom in Hdom_typed.
      rewrite !res_lift_free_dom.
      set_solver.
    + intros σ Hσ. apply Hstores_typed.
      destruct Hσ as [σa [Hσa ->]].
      exists σa. split; [apply Hstores; exact Hσa | reflexivity].
Qed.

Lemma basic_world_formula_wfworld_closed_on_dom
    (Σ : lty_env) (m : WfWorld) :
  res_models m (basic_world_formula Σ) ->
  wfworld_closed_on (lvars_fv (dom Σ)) m.
Proof.
  intros Hmodels σ Hσ.
  apply basic_world_formula_models_iff in Hmodels as [_ [_ Htyped]].
  unfold lworld_has_type, worldA_has_type in Htyped.
  destruct Htyped as [_ Hstores].
  specialize (Hstores (lstore_lift_free σ)).
  assert (Hlift : (res_lift_free m : LWorld) (lstore_lift_free σ)).
  { exists σ. split; [exact Hσ | reflexivity]. }
  specialize (Hstores Hlift).
  split.
	  - unfold closed_env. intros x v Hlookup.
	    apply storeA_restrict_lookup_some in Hlookup as [Hx Hlookup].
	    rewrite lvars_fv_elem in Hx.
	    apply elem_of_dom in Hx as [T HΣ].
    pose proof (Hstores (LVFree x) T v HΣ) as Hval.
    assert (Hlookup_lift : lstore_lift_free σ !! LVFree x = Some v).
    {
      change (((lstore_lift_free σ : LStore (V := value)) : gmap logic_var value) !!
        LVFree x = Some v).
      rewrite lstore_lift_free_lookup_free. exact Hlookup.
    }
    specialize (Hval Hlookup_lift).
    cbn [stale stale_value_inst].
    apply basic_typing_closed_value in Hval. exact Hval.
	  - unfold lc_env. intros x v Hlookup.
	    apply storeA_restrict_lookup_some in Hlookup as [Hx Hlookup].
	    rewrite lvars_fv_elem in Hx.
	    apply elem_of_dom in Hx as [T HΣ].
    pose proof (Hstores (LVFree x) T v HΣ) as Hval.
    assert (Hlookup_lift : lstore_lift_free σ !! LVFree x = Some v).
    {
      change (((lstore_lift_free σ : LStore (V := value)) : gmap logic_var value) !!
        LVFree x = Some v).
      rewrite lstore_lift_free_lookup_free. exact Hlookup.
    }
    specialize (Hval Hlookup_lift).
    exact (typing_value_lc _ _ _ Hval).
Qed.

Lemma basic_world_formula_wfworld_closed_on_atoms
    (Σ : lty_env) X (m : WfWorld) :
  lvars_of_atoms X ⊆ dom Σ ->
  res_models m (basic_world_formula Σ) ->
  wfworld_closed_on X m.
Proof.
  intros HX Hmodels.
  eapply wfworld_closed_on_mono.
  - intros x Hx.
    apply lvars_fv_elem.
    apply HX.
    unfold lvars_of_atoms. apply elem_of_map.
    exists x. split; [reflexivity | exact Hx].
  - apply basic_world_formula_wfworld_closed_on_dom. exact Hmodels.
Qed.

End StoreTyping.
