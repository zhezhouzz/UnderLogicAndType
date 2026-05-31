(** * BasicDenotation.StoreTyping

    Basic typing for stores, worlds, and extension outputs. *)

From ContextBasicDenotation Require Import Notation.
From ContextLogic Require Import FormulaConnectives.

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

Lemma atom_store_has_ltype_dom_subset Σ σ :
  atom_store_has_ltype Σ σ ->
  lvars_of_atoms (dom (σ : gmap atom value)) ⊆ dom Σ.
Proof.
  intros Hty v Hv.
  unfold lvars_of_atoms in Hv.
  apply elem_of_map in Hv as [x [Hv Hx]].
  subst v.
  apply elem_of_dom in Hx as [v Hv].
  destruct (Hty x v Hv) as [T [HΣ _]].
  apply elem_of_dom_2 in HΣ. exact HΣ.
Qed.

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
Proof. reflexivity. Qed.

Lemma formula_lvars_fv_basic_world_formula Σ :
  lvars_fv (formula_lvars (basic_world_formula Σ)) = lvars_fv (dom Σ).
Proof.
  change (lvars_fv (formula_lvars (basic_world_formula Σ)))
    with (formula_fv (basic_world_formula Σ)).
  apply formula_fv_basic_world_formula.
Qed.

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

Lemma extension_has_type_to_ltype
    (Σout : gmap atom ty) (min : WfWorld) F :
  extension_has_type Σout min F ->
  extension_has_ltype (atom_env_to_lty_env Σout) min F.
Proof.
  intros [Hin [Hout Hstores]].
  unfold extension_has_ltype.
  split.
  - exact Hin.
  - split.
    + change (lc_lvars (dom ((@atom_store_to_lvar_store ty) Σout
          : gmap logic_var ty))).
      rewrite atom_store_to_lvar_store_dom.
      intros [k|x] Hv; cbn [lc_logic_var_key]; [|exact I].
      unfold lvars_of_atoms in Hv.
      apply elem_of_map in Hv as [? [Hbad _]]. discriminate.
    + split.
      * change (lvars_fv (dom ((@atom_store_to_lvar_store ty) Σout
            : gmap logic_var ty)) = ext_out F).
        rewrite atom_store_to_lvar_store_dom, lvars_fv_of_atoms. exact Hout.
      * intros σin mout Hσin HF.
        specialize (Hstores σin mout Hσin HF) as Htyped.
        unfold lworld_has_type, worldA_has_type.
        split.
        -- change (dom ((@atom_store_to_lvar_store ty) Σout
              : gmap logic_var ty) ⊆ lworld_dom (res_lift_free mout : LWorld)).
           rewrite atom_store_to_lvar_store_dom, res_lift_free_dom.
           unfold world_has_type, worldA_has_type in Htyped.
           destruct Htyped as [Hdom _].
           intros v Hv.
           unfold lvars_of_atoms in *.
           apply elem_of_map in Hv as [x [-> Hx]].
           apply elem_of_map. exists x. split; [reflexivity|].
           apply Hdom. exact Hx.
        -- intros τ Hτ.
           unfold res_lift_free in Hτ. cbn [worldA_stores] in Hτ.
           destruct Hτ as [σ0 [Hσ0 ->]].
           intros v T u HΣ Hu.
           destruct v as [k|x].
           ++ change (((@atom_store_to_lvar_store ty) Σout
                 : gmap logic_var ty) !! LVBound k = Some T) in HΣ.
              rewrite atom_store_to_lvar_store_lookup_bound_none in HΣ. discriminate.
           ++ change (((@atom_store_to_lvar_store ty) Σout
                 : gmap logic_var ty) !! LVFree x = Some T) in HΣ.
              rewrite atom_store_to_lvar_store_lookup_free in HΣ.
              change (((lstore_lift_free σ0 : LStore (V := value)) : gmap logic_var value) !!
                LVFree x = Some u) in Hu.
              rewrite lstore_lift_free_lookup_free in Hu.
              unfold world_has_type, worldA_has_type in Htyped.
              destruct Htyped as [_ Htyped].
              eapply Htyped; eauto.
Qed.

Lemma extension_has_type_input_resource_eq
    (Σout : gmap atom ty) (min1 min2 : WfWorld) F :
  min1 = min2 ->
  extension_has_type Σout min1 F ->
  extension_has_type Σout min2 F.
Proof. intros -> Htyped. exact Htyped. Qed.

Lemma extension_has_ltype_input_resource_eq
    (Σout : lty_env) (min1 min2 : WfWorld) F :
  min1 = min2 ->
  extension_has_ltype Σout min1 F ->
  extension_has_ltype Σout min2 F.
Proof. intros -> Htyped. exact Htyped. Qed.

Lemma storeA_has_type_restrict
    {K : Type} `{Countable K}
    (Σ : gmap K ty) (σ : gmap K value) X :
  storeA_has_type Σ σ ->
  storeA_has_type (storeA_restrict Σ X) σ.
Proof.
  intros Htyped x T v HΣ Hσ.
  apply storeA_restrict_lookup_some in HΣ as [_ HΣ].
    eapply Htyped; eauto.
Qed.

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

Lemma worldA_has_type_restrict_env
    {K : Type} `{Countable K}
    (Σ : gmap K ty) (m : @WorldA K _ _ value) X :
  worldA_has_type Σ m ->
  worldA_has_type (storeA_restrict Σ X) m.
	Proof.
	  intros [Hdom Hstores]. split.
	  - intros x Hx.
	    apply elem_of_dom in Hx as [T HT].
	    apply storeA_restrict_lookup_some in HT as [_ HT].
	    apply Hdom.
	    eapply elem_of_dom_2; exact HT.
  - intros σ Hσ.
    apply storeA_has_type_restrict.
    exact (Hstores σ Hσ).
Qed.

Lemma world_has_type_restrict_world
    (Σ : gmap atom ty) (m : WfWorld) X :
  dom Σ ⊆ X ->
  world_has_type Σ (m : World) ->
  world_has_type Σ (res_restrict m X : World).
Proof.
  intros HΣX [Hdom Hstores]. split.
  - simpl. set_solver.
  - intros σ Hσ.
    destruct Hσ as [σ0 [Hσ0 Hrestrict]].
    intros x T v HΣ Hσx.
    rewrite <- Hrestrict in Hσx.
    apply storeA_restrict_lookup_some in Hσx as [_ Hσ0x].
    eapply Hstores; eauto.
Qed.

Lemma world_has_type_extend_by
    (Σbase Σout : gmap atom ty) (m my : WfWorld) F :
  world_has_type Σbase (m : World) ->
  extension_has_type Σout (res_restrict m (ext_in F)) F ->
  dom Σbase ## dom Σout ->
  res_extend_by m F my ->
  world_has_type (Σbase ∪ Σout) (my : World).
Proof.
  intros [Hbase_dom Hbase_stores] [_ [Hout_dom Hout_stores]] Hdisj Hext.
  change (dom (Σbase : gmap atom ty) ⊆ world_dom (m : World)) in Hbase_dom.
  change (dom (Σout : gmap atom ty) = ext_out F) in Hout_dom.
  change (dom (Σbase : gmap atom ty) ## dom (Σout : gmap atom ty)) in Hdisj.
  destruct Hext as [Happ [Hmy_dom Hmy_stores]].
  split.
  - intros x Hx.
    apply elem_of_dom in Hx as [T Hlookup].
    rewrite map_lookup_union_Some_raw in Hlookup.
    replace (worldA_dom (raw_world my))
      with (worldA_dom (raw_world m) ∪ extA_out F) by (symmetry; exact Hmy_dom).
    destruct Hlookup as [Hbase | [_ Hout]].
    + apply elem_of_dom_2 in Hbase.
      apply Hbase_dom in Hbase. set_solver.
    + apply elem_of_dom_2 in Hout.
      rewrite Hout_dom in Hout. set_solver.
  - intros σ Hσ.
    apply (proj1 (Hmy_stores σ)) in Hσ.
    destruct Hσ as [σm [we [σe [Hσm [HF [Hσe ->]]]]]].
    intros x T v HΣ Hσ.
    change (((Σbase : gmap atom ty) ∪ (Σout : gmap atom ty)) !! x = Some T) in HΣ.
    change (((σm : gmap atom value) ∪ (σe : gmap atom value)) !! x = Some v) in Hσ.
    rewrite map_lookup_union_Some_raw in HΣ.
    destruct HΣ as [HΣbase | [HΣbase_none HΣout]].
    + rewrite map_lookup_union_Some_raw in Hσ.
      destruct Hσ as [Hσm_lookup | [Hσm_none Hσe_lookup]].
      * eapply Hbase_stores; eauto.
      * exfalso.
        apply elem_of_dom_2 in HΣbase.
        apply Hbase_dom in HΣbase.
        pose proof (wfworldA_store_dom m σm Hσm) as Hdomσm.
        change (dom (σm : gmap atom value) = world_dom (m : World)) in Hdomσm.
        rewrite <- Hdomσm in HΣbase.
        rewrite elem_of_dom in HΣbase.
        destruct HΣbase as [? Hsome].
        change ((σm : gmap atom value) !! x = None) in Hσm_none.
        congruence.
    + rewrite map_lookup_union_Some_raw in Hσ.
      destruct Hσ as [Hσm_lookup | [_ Hσe_lookup]].
      * exfalso.
        apply elem_of_dom_2 in HΣout.
        rewrite Hout_dom in HΣout.
        pose proof (extA_app_out _ _ Happ) as Hout_disj.
        pose proof (wfworldA_store_dom m σm Hσm) as Hdomσm.
        change (dom (σm : gmap atom value) = world_dom (m : World)) in Hdomσm.
        change ((σm : gmap atom value) !! x = Some v) in Hσm_lookup.
        apply elem_of_dom_2 in Hσm_lookup.
        rewrite Hdomσm in Hσm_lookup.
        set_solver.
	      * eapply Hout_stores; eauto.
	        simpl. exists σm. split; [exact Hσm | reflexivity].
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
    + destruct Hden as [_ [Hsub _]]. exact Hsub.
    + apply basic_world_lqual_denote_iff_res_lift_free. exact Hden.
Qed.

Lemma basic_world_formula_fibvars_elim
    (D : lvset) (Σ : lty_env) (m : WfWorld) :
  res_models m (FFibVars D (basic_world_formula Σ)) ->
  res_models m (basic_world_formula Σ).
Proof.
Admitted.

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

Lemma basic_world_formula_extend_by_typed_extension
    (Σbase Σout : lty_env) (m mx : WfWorld) (Fx : fiber_extension) :
  dom Σbase ## dom Σout ->
  res_models m (basic_world_formula Σbase) ->
  extension_has_ltype Σout (res_restrict m (ext_in Fx)) Fx ->
  res_extend_by m Fx mx ->
  res_models mx (basic_world_formula
    ((@union (gmap logic_var ty) _ Σbase Σout) : lty_env)).
Proof.
  intros Hdisj Hbase Hout Hext.
  apply basic_world_formula_models_iff in Hbase as [Hlc_base [Hsub_base Htyped_base]].
  destruct Hout as [_ [Hlc_out [Hout_dom Hout_typed]]].
  apply basic_world_formula_models_iff.
  split.
  - intros v Hv.
    change (v ∈ dom ((Σbase : gmap logic_var ty) ∪ (Σout : gmap logic_var ty))) in Hv.
    rewrite dom_union_L in Hv.
    apply elem_of_union in Hv.
    destruct Hv as [Hv|Hv]; [apply Hlc_base | apply Hlc_out]; exact Hv.
  - split.
    + intros a Ha.
      pose proof (res_extend_by_dom_base_subset m Fx mx Hext) as Hbase_mx.
      pose proof (res_extend_by_dom_output_subset m Fx mx Hext) as Hout_mx.
      change (a ∈ lvars_fv
        (dom ((Σbase : gmap logic_var ty) ∪ (Σout : gmap logic_var ty)))) in Ha.
      rewrite dom_union_L, lvars_fv_union in Ha.
      apply elem_of_union in Ha.
      destruct Ha as [Ha|Ha].
      * set_solver.
      * rewrite Hout_dom in Ha. set_solver.
    + unfold lworld_has_type, worldA_has_type. split.
      * intros v Hv.
        rewrite res_lift_free_dom.
        pose proof (res_extend_by_dom_base_subset m Fx mx Hext) as Hbase_mx.
        pose proof (res_extend_by_dom_output_subset m Fx mx Hext) as Hout_mx.
        change (v ∈ dom ((Σbase : gmap logic_var ty) ∪ (Σout : gmap logic_var ty))) in Hv.
        rewrite dom_union_L in Hv.
        apply elem_of_union in Hv.
        destruct v as [k|a].
        -- destruct Hv as [Hv|Hv].
           ++ exfalso. exact (Hlc_base (LVBound k) Hv).
           ++ exfalso. exact (Hlc_out (LVBound k) Hv).
        -- unfold lvars_of_atoms. apply elem_of_map.
           exists a. split; [reflexivity|].
           change (a ∈ world_dom (mx : World)).
           destruct Hv as [Hv|Hv].
           ++ pose proof (Hsub_base a ltac:(apply lvars_fv_elem; exact Hv)).
              set_solver.
           ++ apply Hout_mx.
              change (a ∈ ext_out Fx).
              rewrite <- Hout_dom. apply lvars_fv_elem. exact Hv.
      * intros τ Hτ.
        destruct Hτ as [σ [Hσ ->]].
        apply (proj1 (resA_extend_by_store_iff m Fx mx σ Hext)) in Hσ.
        destruct Hσ as [σm [we [σe [Hσm [HF [Hσe ->]]]]]].
        intros v U u HΣ Hu.
        change (((Σbase : gmap logic_var ty) ∪ (Σout : gmap logic_var ty)) !! v = Some U) in HΣ.
        rewrite map_lookup_union_Some_raw in HΣ.
        destruct HΣ as [HΣbase | [HΣbase_none HΣout]].
        -- destruct Htyped_base as [_ Hbase_stores].
           specialize (Hbase_stores (lstore_lift_free σm)).
           assert (Hlift_base :
             worldA_stores (res_lift_free m : LWorld) (lstore_lift_free σm)).
           { exists σm. split; [exact Hσm|reflexivity]. }
           specialize (Hbase_stores Hlift_base).
           eapply Hbase_stores; [exact HΣbase|].
           destruct v as [k|a].
           ++ exfalso.
              apply (Hlc_base (LVBound k)).
              apply elem_of_dom_2 in HΣbase. exact HΣbase.
           ++ change (((lstore_lift_free σm : LStore (V := value))
                : gmap logic_var value) !! LVFree a = Some u).
              rewrite lstore_lift_free_lookup_free.
              change (((lstore_lift_free (σm ∪ σe) : LStore (V := value))
                : gmap logic_var value) !! LVFree a = Some u) in Hu.
              rewrite lstore_lift_free_lookup_free in Hu.
              change (((σm : gmap atom value) ∪ (σe : gmap atom value)) !! a = Some u) in Hu.
              rewrite map_lookup_union_Some_raw in Hu.
              destruct Hu as [Hu|[Hnone _]]; [exact Hu|].
              exfalso.
              pose proof (wfworldA_store_dom m σm Hσm) as Hdomσm.
              change (dom (σm : gmap atom value) = world_dom (m : World)) in Hdomσm.
              change (((σm : gmap atom value) !! a) = None) in Hnone.
              apply not_elem_of_dom in Hnone.
              apply Hnone.
              rewrite Hdomσm.
              apply Hsub_base. apply lvars_fv_elem.
              apply elem_of_dom_2 in HΣbase. exact HΣbase.
        -- specialize (Hout_typed (store_restrict σm (ext_in Fx)) we).
           assert (Hσproj : (res_restrict m (ext_in Fx) : World) (store_restrict σm (ext_in Fx))).
           { simpl. exists σm. split; [exact Hσm|reflexivity]. }
           specialize (Hout_typed Hσproj HF).
           destruct Hout_typed as [_ Hout_stores].
           specialize (Hout_stores (lstore_lift_free σe)).
           assert (Hlift_out :
             worldA_stores (res_lift_free we : LWorld) (lstore_lift_free σe)).
           { exists σe. split; [exact Hσe|reflexivity]. }
           specialize (Hout_stores Hlift_out).
           eapply Hout_stores; [exact HΣout|].
           destruct v as [k|a].
           ++ exfalso.
              apply (Hlc_out (LVBound k)).
              apply elem_of_dom_2 in HΣout. exact HΣout.
           ++ change (((lstore_lift_free σe : LStore (V := value))
                : gmap logic_var value) !! LVFree a = Some u).
              rewrite lstore_lift_free_lookup_free.
              change (((lstore_lift_free (σm ∪ σe) : LStore (V := value))
                : gmap logic_var value) !! LVFree a = Some u) in Hu.
              rewrite lstore_lift_free_lookup_free in Hu.
              change (((σm : gmap atom value) ∪ (σe : gmap atom value)) !! a = Some u) in Hu.
              rewrite map_lookup_union_Some_raw in Hu.
              destruct Hu as [Hσm_a|[_ Hσe_a]]; [|exact Hσe_a].
              exfalso.
              change ((Σout : gmap logic_var ty) !! LVFree a = Some U) in HΣout.
              apply elem_of_dom_2 in HΣout.
              apply lvars_fv_elem in HΣout.
              change (a ∈ lvars_fv (dom Σout)) in HΣout.
              rewrite Hout_dom in HΣout.
              pose proof (res_extend_by_output_fresh m Fx mx Hext) as Hfresh.
              change (ext_out Fx ## world_dom (m : World)) in Hfresh.
              pose proof (wfworldA_store_dom m σm Hσm) as Hdomσm.
              change (dom (σm : gmap atom value) = world_dom (m : World)) in Hdomσm.
              change (((σm : gmap atom value) !! a) = Some u) in Hσm_a.
              apply elem_of_dom_2 in Hσm_a. rewrite Hdomσm in Hσm_a.
              set_solver.
Qed.

Lemma basic_world_formula_insert_typed_extension
    (Σ : lty_env) (m mx : WfWorld) x T (Fx : fiber_extension) :
  LVFree x ∉ dom Σ ->
  res_models m (basic_world_formula Σ) ->
  extension_has_ltype (<[LVFree x := T]> ∅)
    (res_restrict m (ext_in Fx)) Fx ->
  res_extend_by m Fx mx ->
  res_models mx (basic_world_formula (<[LVFree x := T]> Σ)).
Proof.
  intros HxΣ Hworld HFx Hext.
  assert (Hdisj :
    dom Σ ## dom (<[LVFree x := T]> (∅ : gmap logic_var ty) : lty_env)).
  {
    change (dom (Σ : gmap logic_var ty) ##
      dom ((<[LVFree x := T]> (∅ : gmap logic_var ty))
        : gmap logic_var ty)).
    rewrite dom_insert_L, dom_empty_L.
    change (LVFree x ∉ dom (Σ : gmap logic_var ty)) in HxΣ.
    set_solver.
  }
  pose proof (basic_world_formula_extend_by_typed_extension
    Σ (<[LVFree x := T]> (∅ : gmap logic_var ty) : lty_env)
    m mx Fx Hdisj Hworld HFx Hext) as Hmodels.
  change (res_models mx (basic_world_formula
    ((Σ : gmap logic_var ty) ∪
      (<[LVFree x := T]> (∅ : gmap logic_var ty)))) : Prop) in Hmodels.
  change (<[LVFree x := T]> (∅ : gmap logic_var ty))
    with ({[LVFree x := T]} : gmap logic_var ty) in Hmodels.
  rewrite storeA_union_singleton_insert_fresh in Hmodels.
  - exact Hmodels.
  - change (LVFree x ∉ dom (Σ : gmap logic_var ty)). exact HxΣ.
Qed.

Lemma basic_world_formula_drop_result_extension
    (Σ : lty_env) (m mx : WfWorld) x T Fx :
  LVFree x ∉ dom Σ ->
  ext_out Fx = {[x]} ->
  res_extend_by m Fx mx ->
  res_models mx (basic_world_formula (<[LVFree x := T]> Σ)) ->
  res_models m (basic_world_formula Σ).
Proof.
  intros HxΣ Hout Hext Hmx.
  apply basic_world_formula_models_iff in Hmx as [Hlc_ins [Hsub_ins Htyped_ins]].
  apply basic_world_formula_models_iff.
  assert (HlcΣ : lc_lvars (dom Σ)).
  {
    intros v Hv. apply Hlc_ins.
    change (v ∈ dom (<[LVFree x := T]> (Σ : gmap logic_var ty))).
    rewrite dom_insert_L. set_solver.
  }
  split; [exact HlcΣ|]. split.
  - intros a Ha.
    assert (Ha_ins : a ∈ lvars_fv (dom (<[LVFree x := T]> (Σ : gmap logic_var ty)))).
    {
      apply lvars_fv_elem in Ha.
      apply lvars_fv_elem.
      change (LVFree a ∈ dom (Σ : gmap logic_var ty)) in Ha.
      apply elem_of_dom in Ha as [Ta HTa].
      change (LVFree a ∈ dom (<[LVFree x := T]> (Σ : gmap logic_var ty) :
        gmap logic_var ty)).
      apply elem_of_dom. exists Ta.
      destruct (decide (a = x)) as [->|Hax].
      - exfalso. apply HxΣ. apply elem_of_dom_2 in HTa. exact HTa.
      - rewrite lookup_insert_ne by congruence. exact HTa.
    }
    specialize (Hsub_ins a Ha_ins).
    pose proof (res_extend_by_dom m Fx mx Hext) as Hdom_mx.
    change (world_dom (mx : World) = world_dom (m : World) ∪ ext_out Fx) in Hdom_mx.
    rewrite Hdom_mx, Hout in Hsub_ins.
    assert (a <> x).
    {
      intros ->. apply HxΣ.
      apply lvars_fv_elem. exact Ha.
    }
    set_solver.
  - unfold lworld_has_type, worldA_has_type. split.
    + intros v Hv.
      rewrite res_lift_free_dom.
      destruct v as [k|a].
      * exfalso. exact (HlcΣ (LVBound k) Hv).
      * unfold lvars_of_atoms. apply elem_of_map.
        exists a. split; [reflexivity|].
        assert (Ha_ins : a ∈ lvars_fv (dom (<[LVFree x := T]> (Σ : gmap logic_var ty)))).
        {
          apply lvars_fv_elem.
          change (LVFree a ∈ dom (Σ : gmap logic_var ty)) in Hv.
          apply elem_of_dom in Hv as [Ta HTa].
          change (LVFree a ∈ dom (<[LVFree x := T]> (Σ : gmap logic_var ty) :
            gmap logic_var ty)).
          apply elem_of_dom. exists Ta.
          destruct (decide (a = x)) as [->|Hax].
          - exfalso. apply HxΣ. apply elem_of_dom_2 in HTa. exact HTa.
          - rewrite lookup_insert_ne by congruence. exact HTa.
        }
        specialize (Hsub_ins a Ha_ins).
        pose proof (res_extend_by_dom m Fx mx Hext) as Hdom_mx.
        change (world_dom (mx : World) = world_dom (m : World) ∪ ext_out Fx) in Hdom_mx.
        rewrite Hdom_mx, Hout in Hsub_ins.
        assert (a <> x) by (intros ->; exact (HxΣ Hv)).
        set_solver.
    + intros τ Hτ.
      destruct Hτ as [σ [Hσ ->]].
      intros v U u HΣ Hu.
      assert (HΣins : <[LVFree x := T]> Σ !! v = Some U).
      {
        destruct v as [k|a].
        - change ((<[LVFree x := T]> (Σ : gmap logic_var ty) :
            gmap logic_var ty) !! LVBound k = Some U).
          rewrite lookup_insert_ne by discriminate.
          exact HΣ.
        - change ((<[LVFree x := T]> (Σ : gmap logic_var ty) :
            gmap logic_var ty) !! LVFree a = Some U).
          destruct (decide (a = x)) as [->|Hax].
          + exfalso. apply HxΣ.
            change ((Σ : gmap logic_var ty) !! LVFree x = Some U) in HΣ.
            apply elem_of_dom_2 in HΣ. exact HΣ.
          + rewrite lookup_insert_ne by congruence.
            exact HΣ.
      }
      pose proof (wfworldA_store_dom m σ Hσ) as Hdomσ.
      change (dom (σ : gmap atom value) = world_dom (m : World)) in Hdomσ.
      assert (Hproj_dom : dom (store_restrict σ (ext_in Fx) : gmap atom value) = ext_in Fx).
      {
        rewrite storeA_restrict_dom.
        pose proof (res_extend_by_input_dom m Fx mx Hext) as Hin.
        unfold ext_in in Hin. rewrite Hdomσ. set_solver.
      }
      destruct (extA_rel_nonempty Fx (store_restrict σ (ext_in Fx)) Hproj_dom)
        as [we [σe [HF Hσe]]].
      assert (Hmx_store : (mx : World) (σ ∪ σe)).
      {
        apply (proj2 (resA_extend_by_store_iff m Fx mx (σ ∪ σe) Hext)).
        exists σ, we, σe. repeat split; try assumption.
      }
      destruct Htyped_ins as [_ Hstores_ins].
      specialize (Hstores_ins (lstore_lift_free (σ ∪ σe))).
      assert (Hlift_mx :
        worldA_stores (res_lift_free mx : LWorld)
          (lstore_lift_free (σ ∪ σe))).
      { exists (σ ∪ σe). split; [exact Hmx_store|reflexivity]. }
      specialize (Hstores_ins Hlift_mx).
      eapply Hstores_ins; [exact HΣins|].
      destruct v as [k|a].
      * exfalso.
        apply (HlcΣ (LVBound k)).
        change ((Σ : gmap logic_var ty) !! LVBound k = Some U) in HΣ.
        apply elem_of_dom_2 in HΣ. exact HΣ.
      * change (((lstore_lift_free (σ ∪ σe) : LStore (V := value))
           : gmap logic_var value) !! LVFree a = Some u).
        rewrite lstore_lift_free_lookup_free.
        change (((lstore_lift_free σ : LStore (V := value))
          : gmap logic_var value) !! LVFree a = Some u) in Hu.
        rewrite lstore_lift_free_lookup_free in Hu.
        change (((σ : gmap atom value) ∪ (σe : gmap atom value)) !! a = Some u).
        rewrite map_lookup_union_Some_raw.
        left. exact Hu.
Qed.

End StoreTyping.
