(** * BasicDenotation.BasicTypingFormula

    Encoding CoreLang basic type well-formedness side conditions as
    ContextLogic formulas.  We keep only the component formulas; obligation
    wrapper sugar is intentionally avoided on the new route. *)

From CoreLang Require Import LocallyNamelessExtra.
From ContextBasicDenotation Require Import Notation StoreTyping TermSyntax TermOpen.
From ContextBase Require Import BaseTactics.
From ContextLogic Require Import FormulaConnectives.
From ContextQualifier Require Import Qualifier.

Section BasicTypingFormula.

Lemma basic_world_formula_empty (m : WfWorldT) :
  res_models m (basic_world_formula (∅ : lty_env)).
Proof.
  apply basic_world_formula_models_iff.
  split.
  - rewrite dom_empty_L. unfold lc_lvars. set_solver.
  - split.
    + rewrite dom_empty_L, lvars_fv_empty. set_solver.
    + unfold lworld_has_type, worldA_has_type, storeA_has_type.
      split; [rewrite dom_empty_L; set_solver|].
      intros σ _ v T val Hlookup _.
      rewrite lookup_empty in Hlookup. discriminate.
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
        basic_tm_has_ltype
          (lty_env_open_one 0 x (typed_lty_env_bind Σ s))
          (e ^^ x) T) ->
      basic_value_has_ltype Σ (vlam s e) (s →ₜ T)
  | BVT_Fix Σ sx T vf (L : aset) :
      (forall x, x ∉ L ->
        basic_value_has_ltype
          (lty_env_open_one 0 x (typed_lty_env_bind Σ sx))
          (vf ^^ x)
          ((sx →ₜ T) →ₜ T)) ->
      basic_value_has_ltype Σ (vfix (sx →ₜ T) vf) (sx →ₜ T)

with basic_tm_has_ltype : lty_env -> tm -> ty -> Prop :=
  | BTT_Ret Σ v T :
      basic_value_has_ltype Σ v T ->
      basic_tm_has_ltype Σ (tret v) T
  | BTT_Let Σ T1 T2 e1 e2 (L : aset) :
      basic_tm_has_ltype Σ e1 T1 ->
      (forall x, x ∉ L ->
        basic_tm_has_ltype
          (lty_env_open_one 0 x (typed_lty_env_bind Σ T1))
          (e2 ^^ x) T2) ->
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
	      basic_tm_has_ltype Σ (tmatch v et ef) T
	  | BTT_TreeNode Σ root left right :
	      basic_value_has_ltype Σ root (TBase TNat) ->
	      basic_value_has_ltype Σ left (TBase TTree) ->
	      basic_value_has_ltype Σ right (TBase TTree) ->
	      basic_tm_has_ltype Σ (tnode root left right) (TBase TTree)
	  | BTT_TreeMatch Σ v T eleaf enode (L : aset) :
	      basic_value_has_ltype Σ v (TBase TTree) ->
	      basic_tm_has_ltype Σ eleaf T ->
	      (forall root left right,
	        root ∉ L -> left ∉ L ∪ {[root]} ->
	        right ∉ L ∪ {[root]} ∪ {[left]} ->
	        basic_tm_has_ltype
	          (tree_node_branch_open_env Σ root left right)
	          (open_tree_node_branch root left right enode) T) ->
	      basic_tm_has_ltype Σ (tmatchtree v eleaf enode) T
	  | BTT_ListCons Σ hd tl :
	      basic_value_has_ltype Σ hd (TBase TNat) ->
	      basic_value_has_ltype Σ tl (TBase TList) ->
	      basic_tm_has_ltype Σ (tcons hd tl) (TBase TList)
	  | BTT_ListMatch Σ v T enil econs (L : aset) :
	      basic_value_has_ltype Σ v (TBase TList) ->
	      basic_tm_has_ltype Σ enil T ->
	      (forall hd tl,
	        hd ∉ L -> tl ∉ L ∪ {[hd]} ->
	        basic_tm_has_ltype
	          (list_cons_branch_open_env Σ hd tl)
	          (open_list_cons_branch hd tl econs) T) ->
	      basic_tm_has_ltype Σ (tmatchlist v enil econs) T.

Scheme basic_value_has_ltype_ind' := Induction for basic_value_has_ltype Sort Prop
  with basic_tm_has_ltype_ind' := Induction for basic_tm_has_ltype Sort Prop.
Combined Scheme basic_has_ltype_mutind
  from basic_value_has_ltype_ind', basic_tm_has_ltype_ind'.

Hint Constructors basic_value_has_ltype basic_tm_has_ltype : core.

Lemma basic_has_ltype_lvars_mutual :
  (forall Σ v T,
    basic_value_has_ltype Σ v T ->
    lvars_of_atoms (fv_value v) ⊆ dom Σ) /\
  (forall Σ e T,
    basic_tm_has_ltype Σ e T ->
    lvars_of_atoms (fv_tm e) ⊆ dom Σ).
Proof.
  apply basic_has_ltype_mutind; cbn [fv_value fv_tm]; intros.
  - set_solver.
  - match goal with
    | Hlook : _ !! _ = Some _ |- _ =>
        apply elem_of_dom_2 in Hlook; set_solver
    end.
  - set_solver.
  - set (y := fresh_for (L ∪ fv_tm e ∪ lvars_fv (dom Σ))).
    assert (Hy : y ∉ L ∪ fv_tm e ∪ lvars_fv (dom Σ)).
    { subst y. apply fresh_for_not_in. }
    match goal with
    | Hopen_typed : forall z, z ∉ _ ->
        lvars_of_atoms (fv_tm _) ⊆ _ |- _ =>
        pose proof (Hopen_typed y ltac:(set_solver)) as Hopened
    end.
    pose proof (open_fv_tm' e (vfvar y) 0) as Hopen.
    cbn [fv_value] in Hopen.
    rewrite lty_env_open_one_dom in Hopened.
    apply lvars_fv_mono in Hopened.
    rewrite lvars_fv_open in Hopened.
    rewrite lvar_store_bind_lvars_fv_dom in Hopened.
    intros v Hv.
    unfold lvars_of_atoms in Hv.
    apply elem_of_map in Hv as [a [-> Ha]].
    apply lvars_fv_elem.
    assert (HaOpen :
      a ∈ lvars_fv (lvars_of_atoms (fv_tm (open_tm 0 (vfvar y) e)))).
    { rewrite lvars_fv_of_atoms. apply Hopen. exact Ha. }
    pose proof (Hopened a HaOpen) as HaΣ.
    apply elem_of_union in HaΣ as [HaΣ|HaΣ].
    + apply elem_of_difference in HaΣ as [HaΣ _]. exact HaΣ.
    + destruct (decide (0 ∈ lvars_bv (dom (typed_lty_env_bind Σ s))));
        set_solver.
  - set (y := fresh_for (L ∪ fv_value vf ∪ lvars_fv (dom Σ))).
    assert (Hy : y ∉ L ∪ fv_value vf ∪ lvars_fv (dom Σ)).
    { subst y. apply fresh_for_not_in. }
    match goal with
    | Hopen_typed : forall z, z ∉ _ ->
        lvars_of_atoms (fv_value _) ⊆ _ |- _ =>
        pose proof (Hopen_typed y ltac:(set_solver)) as Hopened
    end.
    pose proof (open_fv_value' vf (vfvar y) 0) as Hopen.
    cbn [fv_value] in Hopen.
    rewrite lty_env_open_one_dom in Hopened.
    apply lvars_fv_mono in Hopened.
    rewrite lvars_fv_open in Hopened.
    rewrite lvar_store_bind_lvars_fv_dom in Hopened.
    intros v Hv.
    unfold lvars_of_atoms in Hv.
    apply elem_of_map in Hv as [a [-> Ha]].
    apply lvars_fv_elem.
    assert (HaOpen :
      a ∈ lvars_fv (lvars_of_atoms (fv_value (open_value 0 (vfvar y) vf)))).
    { rewrite lvars_fv_of_atoms. apply Hopen. exact Ha. }
    pose proof (Hopened a HaOpen) as HaΣ.
	    apply elem_of_union in HaΣ as [HaΣ|HaΣ].
	    + apply elem_of_difference in HaΣ as [HaΣ _]. exact HaΣ.
	    + destruct (decide (0 ∈ lvars_bv (dom (typed_lty_env_bind Σ sx))));
	        set_solver.
  - set_solver.
	  - set (y := fresh_for (L ∪ fv_tm e2 ∪ lvars_fv (dom Σ))).
    assert (Hy : y ∉ L ∪ fv_tm e2 ∪ lvars_fv (dom Σ)).
    { subst y. apply fresh_for_not_in. }
    match goal with
    | Hopen_typed : forall z, z ∉ _ ->
        lvars_of_atoms (fv_tm _) ⊆ _ |- _ =>
        pose proof (Hopen_typed y ltac:(set_solver)) as Hopened
    end.
    pose proof (open_fv_tm' e2 (vfvar y) 0) as Hopen.
    cbn [fv_value] in Hopen.
    rewrite lty_env_open_one_dom in Hopened.
    apply lvars_fv_mono in Hopened.
    rewrite lvars_fv_open in Hopened.
    rewrite lvar_store_bind_lvars_fv_dom in Hopened.
    intros v Hv.
    unfold lvars_of_atoms in Hv.
    apply elem_of_map in Hv as [a [-> Ha]].
    apply elem_of_union in Ha as [Ha|Ha].
    + match goal with
      | IH : lvars_of_atoms (fv_tm _) ⊆ dom Σ |- _ => apply IH
      end.
      unfold lvars_of_atoms. apply elem_of_map.
      exists a. split; [reflexivity|exact Ha].
    + apply lvars_fv_elem.
      assert (HaOpen :
        a ∈ lvars_fv (lvars_of_atoms (fv_tm (open_tm 0 (vfvar y) e2)))).
      { rewrite lvars_fv_of_atoms. apply Hopen. exact Ha. }
	      pose proof (Hopened a HaOpen) as HaΣ.
		      apply elem_of_union in HaΣ as [HaΣ|HaΣ].
		      * apply elem_of_difference in HaΣ as [HaΣ _]. exact HaΣ.
		      * destruct (decide (0 ∈ lvars_bv (dom (typed_lty_env_bind Σ T1))));
		          set_solver.
  - set_solver.
  - set_solver.
  - set_solver.
  - set_solver.
		  - set (root := fresh_for
	      (L ∪ fv_tm enode ∪ lvars_fv (dom Σ))).
	    assert (Hroot : root ∉ L ∪ fv_tm enode ∪ lvars_fv (dom Σ)).
	    { subst root. apply fresh_for_not_in. }
	    set (left0 := fresh_for
	      (L ∪ fv_tm enode ∪ lvars_fv (dom Σ) ∪ {[root]})).
	    assert (Hleft : left0 ∉
	      L ∪ fv_tm enode ∪ lvars_fv (dom Σ) ∪ {[root]}).
	    { subst left0. apply fresh_for_not_in. }
	    set (right0 := fresh_for
	      (L ∪ fv_tm enode ∪ lvars_fv (dom Σ) ∪ {[root]} ∪ {[left0]})).
		    assert (Hright : right0 ∉
		      L ∪ fv_tm enode ∪ lvars_fv (dom Σ) ∪ {[root]} ∪ {[left0]}).
		    { subst right0. apply fresh_for_not_in. }
		    assert (HrootL : root ∉ L).
		    {
		      intros Hin. apply Hroot.
		      apply elem_of_union_l. apply elem_of_union_l. exact Hin.
		    }
		    assert (HleftL : left0 ∉ L).
		    {
		      intros Hin. apply Hleft.
		      apply elem_of_union_l. apply elem_of_union_l.
		      apply elem_of_union_l. exact Hin.
		    }
			    assert (HrightL : right0 ∉ L).
			    {
			      intros Hin. apply Hright.
			      apply elem_of_union_l. apply elem_of_union_l.
			      apply elem_of_union_l. apply elem_of_union_l. exact Hin.
			    }
				    assert (Hleft_nested : left0 ∉ L ∪ {[root]}).
				    {
				      intros Hin. apply Hleft.
				      apply elem_of_union in Hin as [Hin|Hin].
				      - apply elem_of_union_l. apply elem_of_union_l.
				        apply elem_of_union_l. exact Hin.
				      - apply elem_of_union_r. exact Hin.
				    }
				    assert (Hright_nested : right0 ∉ L ∪ {[root]} ∪ {[left0]}).
				    {
				      intros Hin. apply Hright.
				      apply elem_of_union in Hin as [Hin|Hin].
				      - apply elem_of_union in Hin as [Hin|Hin].
				        + apply elem_of_union_l. apply elem_of_union_l.
				          apply elem_of_union_l. apply elem_of_union_l. exact Hin.
				        + apply elem_of_union_l. apply elem_of_union_r. exact Hin.
				      - apply elem_of_union_r. exact Hin.
				    }
			    match goal with
			    | Hopen_typed : forall root left right,
			        root ∉ _ -> left ∉ _ ∪ {[root]} ->
			        right ∉ _ ∪ {[root]} ∪ {[left]} ->
			        lvars_of_atoms (fv_tm _) ⊆ _ |- _ =>
			        pose proof (Hopen_typed root left0 right0
			          HrootL Hleft_nested Hright_nested) as Hopened
				    end.
		    apply lvars_fv_mono in Hopened.
		    intros u Hu.
		    unfold lvars_of_atoms in Hu.
		    apply elem_of_map in Hu as [a [-> Ha]].
	    apply elem_of_union in Ha as [Ha|Ha].
	    + apply elem_of_union in Ha as [Ha|Ha].
	      * match goal with
	        | IH : lvars_of_atoms (fv_value _) ⊆ dom Σ |- _ => apply IH
	        end.
	        unfold lvars_of_atoms. apply elem_of_map.
	        exists a. split; [reflexivity|exact Ha].
	      * match goal with
	        | IH : lvars_of_atoms (fv_tm _) ⊆ dom Σ |- _ => apply IH
	        end.
	        unfold lvars_of_atoms. apply elem_of_map.
	        exists a. split; [reflexivity|exact Ha].
	    + apply lvars_fv_elem.
		        assert (HaOpen : a ∈ fv_tm
		          (open_tree_node_branch root left0 right0 enode)).
		        {
		          unfold open_tree_node_branch, open_tree_node_branch_value.
		          apply (open_fv_tm'
		            (open_tm 1 (vfvar left0)
		              (open_tm 0 (vfvar root) enode)) (vfvar right0) 2).
		          apply (open_fv_tm'
		            (open_tm 0 (vfvar root) enode) (vfvar left0) 1).
		          apply (open_fv_tm' enode (vfvar root) 0).
		          exact Ha.
		        }
	        assert (HaOpenLvars :
	          a ∈ lvars_fv
	            (lvars_of_atoms
	              (fv_tm (open_tree_node_branch root left0 right0 enode)))).
		        { rewrite lvars_fv_of_atoms. exact HaOpen. }
		        pose proof (Hopened a HaOpenLvars) as HaBranchΣ.
		        pose proof (tree_node_branch_open_env_lvars_fv_dom_subset
		          Σ root left0 right0 a HaBranchΣ) as HaΣ.
		        assert (HrootFV : root ∉ fv_tm enode).
		        {
		          intros Hin. apply Hroot.
		          apply elem_of_union_l. apply elem_of_union_r. exact Hin.
		        }
		        assert (HleftFV : left0 ∉ fv_tm enode).
		        {
		          intros Hin. apply Hleft.
		          apply elem_of_union_l. apply elem_of_union_l.
		          apply elem_of_union_r. exact Hin.
		        }
		        assert (HrightFV : right0 ∉ fv_tm enode).
		        {
		          intros Hin. apply Hright.
		          apply elem_of_union_l. apply elem_of_union_l.
		          apply elem_of_union_l. apply elem_of_union_r. exact Hin.
		        }
		        apply elem_of_union in HaΣ as [HaΣ|HaRight].
		        * apply elem_of_union in HaΣ as [HaΣ|HaLeft].
		          -- apply elem_of_union in HaΣ as [HaBase|HaRoot].
		             ++ exact HaBase.
		             ++ rewrite elem_of_singleton in HaRoot.
		                subst a. contradiction.
		          -- rewrite elem_of_singleton in HaLeft.
		             subst a. contradiction.
		        * rewrite elem_of_singleton in HaRight.
		          subst a. contradiction.
  - set_solver.
  - set (hd := fresh_for
      (L ∪ fv_tm econs ∪ lvars_fv (dom Σ))).
    assert (Hhd : hd ∉ L ∪ fv_tm econs ∪ lvars_fv (dom Σ)).
    { subst hd. apply fresh_for_not_in. }
    set (tl := fresh_for
      (L ∪ fv_tm econs ∪ lvars_fv (dom Σ) ∪ {[hd]})).
    assert (Htl : tl ∉
      L ∪ fv_tm econs ∪ lvars_fv (dom Σ) ∪ {[hd]}).
    { subst tl. apply fresh_for_not_in. }
    assert (HhdL : hd ∉ L) by set_solver.
    assert (Htl_nested : tl ∉ L ∪ {[hd]}) by set_solver.
    match goal with
    | Hopen_typed : forall hd tl,
        hd ∉ _ -> tl ∉ _ ∪ {[hd]} ->
        lvars_of_atoms (fv_tm _) ⊆ _ |- _ =>
        pose proof (Hopen_typed hd tl HhdL Htl_nested) as Hopened
    end.
    apply lvars_fv_mono in Hopened.
    intros u Hu.
    unfold lvars_of_atoms in Hu.
    apply elem_of_map in Hu as [a [-> Ha]].
    apply elem_of_union in Ha as [Ha|Ha].
    + apply elem_of_union in Ha as [Ha|Ha].
      * match goal with
        | IH : lvars_of_atoms (fv_value _) ⊆ dom Σ |- _ => apply IH
        end.
        unfold lvars_of_atoms. apply elem_of_map.
        exists a. split; [reflexivity|exact Ha].
      * match goal with
        | IH : lvars_of_atoms (fv_tm _) ⊆ dom Σ |- _ => apply IH
        end.
        unfold lvars_of_atoms. apply elem_of_map.
        exists a. split; [reflexivity|exact Ha].
    + apply lvars_fv_elem.
      assert (HaOpen : a ∈ fv_tm (open_list_cons_branch hd tl econs)).
      {
        unfold open_list_cons_branch, open_list_cons_branch_value.
        apply (open_fv_tm'
          (open_tm 0 (vfvar hd) econs) (vfvar tl) 1).
        apply (open_fv_tm' econs (vfvar hd) 0).
        exact Ha.
      }
      assert (HaOpenLvars :
        a ∈ lvars_fv
          (lvars_of_atoms (fv_tm (open_list_cons_branch hd tl econs)))).
      { rewrite lvars_fv_of_atoms. exact HaOpen. }
      pose proof (Hopened a HaOpenLvars) as HaBranchΣ.
      pose proof (list_cons_branch_open_env_lvars_fv_dom_subset
        Σ hd tl a HaBranchΣ) as HaΣ.
      assert (HhdFV : hd ∉ fv_tm econs) by set_solver.
      assert (HtlFV : tl ∉ fv_tm econs) by set_solver.
      apply elem_of_union in HaΣ as [HaΣ|HaTl].
      * apply elem_of_union in HaΣ as [HaBase|HaHd].
        -- exact HaBase.
        -- rewrite elem_of_singleton in HaHd. subst a. contradiction.
      * rewrite elem_of_singleton in HaTl. subst a. contradiction.
Qed.

Lemma basic_value_has_ltype_lvars Σ v T :
  basic_value_has_ltype Σ v T ->
  lvars_of_atoms (fv_value v) ⊆ dom Σ.
Proof.
  exact (proj1 basic_has_ltype_lvars_mutual Σ v T).
Qed.

Lemma basic_tm_has_ltype_lvars Σ e T :
  basic_tm_has_ltype Σ e T ->
  lvars_of_atoms (fv_tm e) ⊆ dom Σ.
Proof.
  exact (proj2 basic_has_ltype_lvars_mutual Σ e T).
Qed.

Lemma lty_env_open_one_mono k x (Σ Σ' : lty_env) :
  Σ ⊆ Σ' ->
  lty_env_open_one k x Σ ⊆ lty_env_open_one k x Σ'.
Proof.
  intros Hsub.
  apply map_subseteq_spec. intros v T Hlook.
  unfold lty_env_open_one, lvar_store_open_one in *.
  apply storeA_rekey_lookup_Some_inj_on in Hlook as [u [-> Hu]].
  - apply storeA_rekey_lookup_Some_inj_on.
    + intros a b _ _ Hab. eapply swap_inj. exact Hab.
    + exists u. split; [reflexivity|].
      eapply lookup_weaken; eassumption.
  - intros a b _ _ Hab. eapply swap_inj. exact Hab.
Qed.

Lemma lty_env_shift_mono (Σ Σ' : lty_env) :
  Σ ⊆ Σ' ->
  lty_env_shift Σ ⊆ lty_env_shift Σ'.
Proof.
  intros Hsub.
  apply map_subseteq_spec. intros v T Hlook.
  unfold lty_env_shift, lvar_store_shift, lvar_store_shift_from in *.
  apply storeA_rekey_lookup_Some_inj_on in Hlook as [u [-> Hu]].
  - apply storeA_rekey_lookup_Some_inj_on.
    + intros a b _ _ Hab. eapply logic_var_shift_from_inj. exact Hab.
    + exists u. split; [reflexivity|].
      eapply lookup_weaken; eassumption.
  - intros a b _ _ Hab. eapply logic_var_shift_from_inj. exact Hab.
Qed.

Lemma typed_lty_env_bind_mono (Σ Σ' : lty_env) T :
  Σ ⊆ Σ' ->
  typed_lty_env_bind Σ T ⊆ typed_lty_env_bind Σ' T.
Proof.
  intros Hsub.
  unfold typed_lty_env_bind, lvar_store_bind.
  apply insert_mono.
  apply lty_env_shift_mono. exact Hsub.
Qed.

Lemma lty_env_open_one_typed_bind_mono k x (Σ Σ' : lty_env) T :
  Σ ⊆ Σ' ->
  lty_env_open_one k x (typed_lty_env_bind Σ T) ⊆
  lty_env_open_one k x (typed_lty_env_bind Σ' T).
Proof.
  intros Hsub.
  apply lty_env_open_one_mono.
  apply typed_lty_env_bind_mono. exact Hsub.
Qed.

Lemma tree_node_branch_open_env_mono
    (Σ Σ' : lty_env) root left right :
  Σ ⊆ Σ' ->
  tree_node_branch_open_env Σ root left right ⊆
  tree_node_branch_open_env Σ' root left right.
Proof.
  intros Hsub.
  unfold tree_node_branch_open_env, tree_node_branch_bound_env.
  repeat apply lty_env_open_one_mono.
  repeat apply typed_lty_env_bind_mono.
  exact Hsub.
Qed.

Lemma list_cons_branch_open_env_mono
    (Σ Σ' : lty_env) hd tl :
  Σ ⊆ Σ' ->
  list_cons_branch_open_env Σ hd tl ⊆
  list_cons_branch_open_env Σ' hd tl.
Proof.
  intros Hsub.
  unfold list_cons_branch_open_env, list_cons_branch_bound_env.
  repeat apply lty_env_open_one_mono.
  repeat apply typed_lty_env_bind_mono.
  exact Hsub.
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
    apply lty_env_open_one_typed_bind_mono. exact H0.
  - eapply BVT_Fix with (L := L). intros x Hx.
    eapply H; [exact Hx|].
    apply lty_env_open_one_typed_bind_mono. exact H0.
  - eapply BTT_Let with (L := L).
    + eapply H; exact H1.
    + intros x Hx. eapply H0; [exact Hx|].
      apply lty_env_open_one_typed_bind_mono. exact H1.
	  - eapply BTT_TreeMatch with (L := L).
	    + eapply H; exact H2.
	    + eapply H0; exact H2.
	    + intros root left right Hroot Hleft Hright.
	      eapply H1; [exact Hroot|exact Hleft|exact Hright|].
	      apply tree_node_branch_open_env_mono. exact H2.
  - eapply BTT_ListMatch with (L := L).
    + eapply H; exact H2.
    + eapply H0; exact H2.
    + intros hd tl Hhd Htl.
      eapply H1; [exact Hhd|exact Htl|].
      apply list_cons_branch_open_env_mono. exact H2.
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

Lemma basic_has_ltype_lc_mutual :
  (forall Σ v T,
    lc_lvars (dom Σ) ->
    basic_value_has_ltype Σ v T ->
    lc_value v) /\
  (forall Σ e T,
    lc_lvars (dom Σ) ->
    basic_tm_has_ltype Σ e T ->
    lc_tm e).
Proof.
  enough (
    (forall Σ v T (Hty : basic_value_has_ltype Σ v T),
      lc_lvars (dom Σ) -> lc_value v) /\
    (forall Σ e T (Hty : basic_tm_has_ltype Σ e T),
      lc_lvars (dom Σ) -> lc_tm e)) as Hreg.
  {
    split; intros; eapply Hreg; eauto.
  }
  apply basic_has_ltype_mutind
    with (P := fun Σ v T _ => lc_lvars (dom Σ) -> lc_value v)
         (P0 := fun Σ e T _ => lc_lvars (dom Σ) -> lc_tm e);
    intros; eauto.
  - exfalso.
    match goal with
    | Hlc : lc_lvars (dom ?Σ),
      Hlook : ?Σ !! LVBound ?k = Some ?T |- _ =>
        apply (Hlc (LVBound k));
        eapply elem_of_dom_2; exact Hlook
    end.
  - eapply LC_lam with (L := L ∪ lvars_fv (dom Σ)). intros x Hx.
    eapply H; [set_solver|].
    + intros v Hv.
      assert (Hfreshx : LVFree x ∉ dom Σ).
      { intros Hdom.
        apply Hx. apply elem_of_union_r. apply lvars_fv_elem. exact Hdom. }
      pose proof (typed_lty_env_bind_open_current x Σ s Hfreshx H0) as Henv.
      rewrite Henv in Hv.
      rewrite dom_insert in Hv.
      apply elem_of_union in Hv as [Hv|Hv].
      * rewrite elem_of_singleton in Hv. subst v. exact I.
      * exact (H0 v Hv).
  - eapply LC_fix with (L := L ∪ lvars_fv (dom Σ)). intros x Hx.
    eapply H; [set_solver|].
    + intros v Hv.
      assert (Hfreshx : LVFree x ∉ dom Σ).
      { intros Hdom.
        apply Hx. apply elem_of_union_r. apply lvars_fv_elem. exact Hdom. }
      pose proof (typed_lty_env_bind_open_current x Σ sx Hfreshx H0) as Henv.
      rewrite Henv in Hv.
      rewrite dom_insert in Hv.
      apply elem_of_union in Hv as [Hv|Hv].
      * rewrite elem_of_singleton in Hv. subst v. exact I.
      * exact (H0 v Hv).
	  - eapply LC_lete with (L := L ∪ lvars_fv (dom Σ)).
	    + eauto.
	    + intros x Hx. eapply H0; [set_solver|].
	      * intros v Hv.
        assert (Hfreshx : LVFree x ∉ dom Σ).
        { intros Hdom.
          apply Hx. apply elem_of_union_r. apply lvars_fv_elem. exact Hdom. }
        pose proof (typed_lty_env_bind_open_current x Σ T1 Hfreshx H1) as Henv.
        rewrite Henv in Hv.
	        rewrite dom_insert in Hv.
	        apply elem_of_union in Hv as [Hv|Hv].
	        -- rewrite elem_of_singleton in Hv. subst v. exact I.
	        -- exact (H1 v Hv).
		  - eapply LC_matchtree with (L := L ∪ lvars_fv (dom Σ)).
		    + eauto.
		    + eauto.
		    + intros root left right Hroot Hleft Hright.
		      assert (HrootL : root ∉ L).
		      { intros Hin. apply Hroot. apply elem_of_union_l. exact Hin. }
		      assert (HleftL : left ∉ L ∪ {[root]}).
		      {
		        intros Hin. apply Hleft.
		        apply elem_of_union in Hin as [Hin|Hin];
		          [apply elem_of_union_l; apply elem_of_union_l; exact Hin
		          |apply elem_of_union_r; exact Hin].
		      }
		      assert (HrightL : right ∉ L ∪ {[root]} ∪ {[left]}).
		      {
		        intros Hin. apply Hright.
		        apply elem_of_union in Hin as [Hin|Hin].
		        { apply elem_of_union in Hin as [Hin|Hin].
		          { apply elem_of_union_l. apply elem_of_union_l.
		            apply elem_of_union_l. exact Hin. }
		          { apply elem_of_union_l. apply elem_of_union_r. exact Hin. } }
		        { apply elem_of_union_r. exact Hin. }
		      }
		      assert (HrootΣ : root ∉ lvars_fv (dom Σ)).
		      { intros Hin. apply Hroot. apply elem_of_union_r. exact Hin. }
		      assert (HleftΣ : left ∉ lvars_fv (dom Σ)).
		      {
		        intros Hin. apply Hleft.
		        apply elem_of_union_l. apply elem_of_union_r. exact Hin.
		      }
		      assert (HrightΣ : right ∉ lvars_fv (dom Σ)).
		      {
		        intros Hin. apply Hright.
		        apply elem_of_union_l. apply elem_of_union_l.
		        apply elem_of_union_r. exact Hin.
		      }
			      assert (Hroot_left : root <> left).
			      {
			        intro Heq. apply Hleft. apply elem_of_union_r.
			        rewrite elem_of_singleton. symmetry. exact Heq.
			      }
			      assert (Hroot_right : root <> right).
			      {
			        intro Heq. apply Hright. apply elem_of_union_l.
			        apply elem_of_union_r.
			        rewrite elem_of_singleton. symmetry. exact Heq.
			      }
			      assert (Hleft_right : left <> right).
			      {
			        intro Heq. apply Hright. apply elem_of_union_r.
			        rewrite elem_of_singleton. symmetry. exact Heq.
			      }
		      eapply H1; [exact HrootL|exact HleftL|exact HrightL|].
		      apply tree_node_branch_open_env_lc_dom.
		      * exact H2.
		      * exact HrootΣ.
		      * exact HleftΣ.
		      * exact HrightΣ.
		      * exact Hroot_left.
		      * exact Hroot_right.
		      * exact Hleft_right.
  - eapply LC_matchlist with (L := L ∪ lvars_fv (dom Σ)).
    + eauto.
    + eauto.
    + intros hd tl Hhd Htl.
      assert (HhdL : hd ∉ L) by set_solver.
      assert (HtlL : tl ∉ L ∪ {[hd]}) by set_solver.
      assert (HhdΣ : hd ∉ lvars_fv (dom Σ)) by set_solver.
      assert (HtlΣ : tl ∉ lvars_fv (dom Σ)) by set_solver.
      assert (Hhd_tl : hd <> tl).
      { intro Heq. apply Htl. apply elem_of_union_r.
        rewrite elem_of_singleton. symmetry. exact Heq. }
      eapply H1; [exact HhdL|exact HtlL|].
      apply list_cons_branch_open_env_lc_dom.
      * exact H2.
      * exact HhdΣ.
      * exact HtlΣ.
      * exact Hhd_tl.
Qed.

Lemma basic_value_has_ltype_lc Σ v T :
  lc_lvars (dom Σ) ->
  basic_value_has_ltype Σ v T ->
  lc_value v.
Proof.
  exact (proj1 basic_has_ltype_lc_mutual Σ v T).
Qed.

Lemma basic_tm_has_ltype_lc Σ e T :
  lc_lvars (dom Σ) ->
  basic_tm_has_ltype Σ e T ->
  lc_tm e.
Proof.
  exact (proj2 basic_has_ltype_lc_mutual Σ e T).
Qed.

Lemma basic_tm_has_ltype_ret_fvar_lookup
    (Σ : lty_env) x T :
  basic_tm_has_ltype Σ (tret (vfvar x)) T ->
  Σ !! LVFree x = Some T.
Proof.
  intros Hty.
  inversion Hty; subst; clear Hty.
  match goal with
  | H : basic_value_has_ltype _ (vfvar x) _ |- _ =>
      inversion H; subst; eauto
  end.
Qed.

Lemma lty_env_open_one_typed_bind_lookup_free_ne
    (Σ : lty_env) T y z :
  z <> y ->
  lty_env_open_one 0 y (typed_lty_env_bind Σ T) !! LVFree z =
  Σ !! LVFree z.
Proof.
  intros Hzy.
  unfold lty_env_open_one, lvar_store_open_one.
  change ((kmap (M1:=gmap logic_var) (M2:=gmap logic_var)
    (logic_var_open 0 y) (typed_lty_env_bind Σ T) : gmap logic_var ty) !!
    LVFree z =
    Σ !! LVFree z).
  replace (LVFree z) with (logic_var_open 0 y (LVFree z)) at 1.
  - rewrite (lookup_kmap (M1:=gmap logic_var) (M2:=gmap logic_var)
      (Inj0:=swap_inj (LVBound 0) (LVFree y))
      (logic_var_open 0 y) (typed_lty_env_bind Σ T) (LVFree z)).
    apply typed_lty_env_bind_lookup_free.
  - rewrite logic_var_open_sym.
    unfold swap.
    repeat case_decide; congruence.
Qed.

Lemma lty_env_open_one_typed_bind_lookup_current
    (Σ : lty_env) T y :
  lty_env_open_one 0 y (typed_lty_env_bind Σ T) !! LVFree y =
  Some T.
Proof.
  unfold lty_env_open_one, lvar_store_open_one.
  change ((kmap (M1:=gmap logic_var) (M2:=gmap logic_var)
    (logic_var_open 0 y) (typed_lty_env_bind Σ T) : gmap logic_var ty) !!
    LVFree y =
    Some T).
  replace (LVFree y) with (logic_var_open 0 y (LVBound 0)) at 1.
  - rewrite (lookup_kmap (M1:=gmap logic_var) (M2:=gmap logic_var)
      (Inj0:=swap_inj (LVBound 0) (LVFree y))
      (logic_var_open 0 y) (typed_lty_env_bind Σ T) (LVBound 0)).
    unfold typed_lty_env_bind, lvar_store_bind.
    rewrite lookup_insert.
    destruct (decide (LVBound 0 = LVBound 0)); [reflexivity|congruence].
  - rewrite logic_var_open_sym.
    unfold swap.
    repeat case_decide; try congruence.
Qed.

Lemma lty_env_restrict_open_bind_body_subset
    (Σ : lty_env) T x Dbody D :
  LVFree x ∉ dom Σ ->
  x ∉ lvars_fv D ->
  lvars_bv Dbody = ∅ ->
  Dbody ⊆ D ∪ {[LVFree x]} ->
  storeA_restrict (lty_env_open_one 0 x (typed_lty_env_bind Σ T)) Dbody ⊆
  lty_env_open_one 0 x (typed_lty_env_bind (storeA_restrict Σ D) T).
Proof.
  intros HxΣ HxD Hbv Hsub.
  apply map_subseteq_spec. intros v U Hlook.
  apply storeA_restrict_lookup_some in Hlook as [HvD Hlook].
  destruct v as [k|z].
  - exfalso.
    assert (k ∈ lvars_bv Dbody) by (rewrite lvars_bv_elem; exact HvD).
    rewrite Hbv in H. clear -H. set_solver.
  - destruct (decide (z = x)) as [->|Hzx].
    + rewrite lty_env_open_one_typed_bind_lookup_current.
      rewrite lty_env_open_one_typed_bind_lookup_current in Hlook.
      inversion Hlook. reflexivity.
    + rewrite lty_env_open_one_typed_bind_lookup_free_ne by exact Hzx.
      rewrite lty_env_open_one_typed_bind_lookup_free_ne in Hlook by exact Hzx.
      apply (storeA_restrict_lookup_some_2 _ _ _ _ Hlook).
      assert (HzD : LVFree z ∈ D).
      {
        specialize (Hsub _ HvD).
        apply elem_of_union in Hsub as [HzD|HzxD]; [exact HzD|].
        rewrite elem_of_singleton in HzxD. inversion HzxD. subst z.
        contradiction.
      }
      exact HzD.
Qed.

Lemma lty_env_restrict_tree_branch_body_subset
    (Σ : lty_env) root left right Dbody D :
  root ∉ lvars_fv D ->
  left ∉ lvars_fv D ->
  right ∉ lvars_fv D ->
  lvars_bv Dbody = ∅ ->
  Dbody ⊆ D ∪ {[LVFree root]} ∪ {[LVFree left]} ∪ {[LVFree right]} ->
  storeA_restrict
    (<[LVFree right := TBase TTree]>
      (<[LVFree left := TBase TTree]>
        (<[LVFree root := TBase TNat]> Σ))) Dbody ⊆
  <[LVFree right := TBase TTree]>
    (<[LVFree left := TBase TTree]>
      (<[LVFree root := TBase TNat]> (storeA_restrict Σ D))).
Proof.
  intros HrootD HleftD HrightD Hbv Hsub.
  apply map_subseteq_spec. intros v U Hlook.
  apply storeA_restrict_lookup_some in Hlook as [HvD Hlook].
  destruct v as [k|z].
  - exfalso.
    assert (k ∈ lvars_bv Dbody) by (rewrite lvars_bv_elem; exact HvD).
    rewrite Hbv in H. clear -H. set_solver.
	  - destruct (decide (z = right)) as [->|Hzr].
	    + rewrite lookup_insert in Hlook.
	      destruct (decide (LVFree right = LVFree right)) as [_|Hbad] in Hlook;
	        [|congruence].
	      rewrite lookup_insert.
	      destruct (decide (LVFree right = LVFree right)) as [_|Hbad];
	        [exact Hlook|congruence].
	    + rewrite lookup_insert_ne in Hlook by (intros Heq; inversion Heq; congruence).
	      rewrite lookup_insert_ne by (intros Heq; inversion Heq; congruence).
	      destruct (decide (z = left)) as [->|Hzl].
	      * rewrite lookup_insert in Hlook.
	        destruct (decide (LVFree left = LVFree left)) as [_|Hbad] in Hlook;
	          [|congruence].
	        rewrite lookup_insert.
	        destruct (decide (LVFree left = LVFree left)) as [_|Hbad];
	          [exact Hlook|congruence].
	      * rewrite lookup_insert_ne in Hlook by (intros Heq; inversion Heq; congruence).
	        rewrite lookup_insert_ne by (intros Heq; inversion Heq; congruence).
	        destruct (decide (z = root)) as [->|Hzroot].
	        -- rewrite lookup_insert in Hlook.
	           destruct (decide (LVFree root = LVFree root)) as [_|Hbad] in Hlook;
	             [|congruence].
	           rewrite lookup_insert.
	           destruct (decide (LVFree root = LVFree root)) as [_|Hbad];
	             [exact Hlook|congruence].
	        -- rewrite lookup_insert_ne in Hlook by (intros Heq; inversion Heq; congruence).
	           rewrite lookup_insert_ne by (intros Heq; inversion Heq; congruence).
	           apply (storeA_restrict_lookup_some_2 _ _ _ _ Hlook).
		   assert (LVFree z ∈ D).
		   {
			     specialize (Hsub _ HvD).
			     set_unfold in Hsub.
			     set_unfold.
		     intuition; try congruence;
		       try match goal with
		       | H : LVFree _ = LVFree _ |- _ => inversion H; congruence
		       end.
		   }
		   exact H.
Qed.

Lemma lty_env_restrict_tree_node_branch_open_env_body_subset
    (Σ : lty_env) root left right Dbody D :
  root <> left ->
  root <> right ->
  left <> right ->
  root ∉ lvars_fv D ->
  left ∉ lvars_fv D ->
  right ∉ lvars_fv D ->
  lvars_bv Dbody = ∅ ->
  Dbody ⊆ D ∪ {[LVFree root]} ∪ {[LVFree left]} ∪ {[LVFree right]} ->
  storeA_restrict (tree_node_branch_open_env Σ root left right) Dbody ⊆
  tree_node_branch_open_env (storeA_restrict Σ D) root left right.
Proof.
  intros Hroot_left Hroot_right Hleft_right HrootD HleftD HrightD Hbv Hsub.
  apply map_subseteq_spec. intros v U Hlook.
  apply storeA_restrict_lookup_some in Hlook as [HvD Hlook].
  destruct v as [k|z].
  - exfalso.
    assert (k ∈ lvars_bv Dbody) by (rewrite lvars_bv_elem; exact HvD).
    rewrite Hbv in H. clear -H. set_solver.
  - replace (tree_node_branch_open_env Σ root left right !! LVFree z)
      with ((<[LVFree right := TBase TTree]>
        (<[LVFree left := TBase TTree]>
          (<[LVFree root := TBase TNat]> Σ))) !! LVFree z) in Hlook.
    2:{ symmetry. apply tree_node_branch_open_env_lookup_free; assumption. }
    replace (tree_node_branch_open_env (storeA_restrict Σ D) root left right
        !! LVFree z)
      with ((<[LVFree right := TBase TTree]>
        (<[LVFree left := TBase TTree]>
          (<[LVFree root := TBase TNat]> (storeA_restrict Σ D)))) !! LVFree z).
    2:{ symmetry. apply tree_node_branch_open_env_lookup_free; assumption. }
    destruct (decide (z = right)) as [->|Hzr].
    + rewrite lookup_insert in Hlook.
      destruct (decide (LVFree right = LVFree right)) as [_|Hbad] in Hlook;
        [|congruence].
      rewrite lookup_insert.
      destruct (decide (LVFree right = LVFree right)) as [_|Hbad];
        [exact Hlook|congruence].
    + rewrite lookup_insert_ne in Hlook by (intros Heq; inversion Heq; congruence).
      rewrite lookup_insert_ne by (intros Heq; inversion Heq; congruence).
      destruct (decide (z = left)) as [->|Hzl].
      * rewrite lookup_insert in Hlook.
        destruct (decide (LVFree left = LVFree left)) as [_|Hbad] in Hlook;
          [|congruence].
        rewrite lookup_insert.
        destruct (decide (LVFree left = LVFree left)) as [_|Hbad];
          [exact Hlook|congruence].
      * rewrite lookup_insert_ne in Hlook by (intros Heq; inversion Heq; congruence).
        rewrite lookup_insert_ne by (intros Heq; inversion Heq; congruence).
        destruct (decide (z = root)) as [->|Hzroot].
        -- rewrite lookup_insert in Hlook.
           destruct (decide (LVFree root = LVFree root)) as [_|Hbad] in Hlook;
             [|congruence].
           rewrite lookup_insert.
           destruct (decide (LVFree root = LVFree root)) as [_|Hbad];
             [exact Hlook|congruence].
        -- rewrite lookup_insert_ne in Hlook by (intros Heq; inversion Heq; congruence).
           rewrite lookup_insert_ne by (intros Heq; inversion Heq; congruence).
           apply (storeA_restrict_lookup_some_2 _ _ _ _ Hlook).
           assert (HzD : LVFree z ∈ D).
           {
             specialize (Hsub _ HvD).
             apply elem_of_union in Hsub as [Hsub|Hright].
             - apply elem_of_union in Hsub as [Hsub|Hleft].
               + apply elem_of_union in Hsub as [HzD|Hroot]; [exact HzD|].
                 rewrite elem_of_singleton in Hroot. inversion Hroot. subst z.
                 contradiction.
               + rewrite elem_of_singleton in Hleft. inversion Hleft. subst z.
                 contradiction.
             - rewrite elem_of_singleton in Hright. inversion Hright. subst z.
               contradiction.
           }
           exact HzD.
Qed.

Lemma lty_env_restrict_list_cons_branch_open_env_body_subset
    (Σ : lty_env) hd tl Dbody D :
  hd <> tl ->
  hd ∉ lvars_fv D ->
  tl ∉ lvars_fv D ->
  lvars_bv Dbody = ∅ ->
  Dbody ⊆ D ∪ {[LVFree hd]} ∪ {[LVFree tl]} ->
  storeA_restrict (list_cons_branch_open_env Σ hd tl) Dbody ⊆
  list_cons_branch_open_env (storeA_restrict Σ D) hd tl.
Proof.
  intros Hhd_tl HhdD HtlD Hbv Hsub.
  apply map_subseteq_spec. intros v U Hlook.
  apply storeA_restrict_lookup_some in Hlook as [HvD Hlook].
  destruct v as [k|z].
  - exfalso.
    assert (k ∈ lvars_bv Dbody) by (rewrite lvars_bv_elem; exact HvD).
    rewrite Hbv in H. clear -H. set_solver.
  - replace (list_cons_branch_open_env Σ hd tl !! LVFree z)
      with ((<[LVFree tl := TBase TList]>
        (<[LVFree hd := TBase TNat]> Σ)) !! LVFree z) in Hlook.
    2:{ symmetry. apply list_cons_branch_open_env_lookup_free. exact Hhd_tl. }
    replace (list_cons_branch_open_env (storeA_restrict Σ D) hd tl
        !! LVFree z)
      with ((<[LVFree tl := TBase TList]>
        (<[LVFree hd := TBase TNat]> (storeA_restrict Σ D))) !! LVFree z).
    2:{ symmetry. apply list_cons_branch_open_env_lookup_free. exact Hhd_tl. }
    destruct (decide (z = tl)) as [->|Hztl].
    + rewrite lookup_insert in Hlook.
      destruct (decide (LVFree tl = LVFree tl)) as [_|Hbad] in Hlook;
        [|congruence].
      rewrite lookup_insert.
      destruct (decide (LVFree tl = LVFree tl)) as [_|Hbad];
        [exact Hlook|congruence].
    + rewrite lookup_insert_ne in Hlook by (intros Heq; inversion Heq; congruence).
      rewrite lookup_insert_ne by (intros Heq; inversion Heq; congruence).
      destruct (decide (z = hd)) as [->|Hzhd].
      * rewrite lookup_insert in Hlook.
        destruct (decide (LVFree hd = LVFree hd)) as [_|Hbad] in Hlook;
          [|congruence].
        rewrite lookup_insert.
        destruct (decide (LVFree hd = LVFree hd)) as [_|Hbad];
          [exact Hlook|congruence].
      * rewrite lookup_insert_ne in Hlook by (intros Heq; inversion Heq; congruence).
        rewrite lookup_insert_ne by (intros Heq; inversion Heq; congruence).
        apply (storeA_restrict_lookup_some_2 _ _ _ _ Hlook).
        assert (HzD : LVFree z ∈ D).
        {
          specialize (Hsub _ HvD).
          apply elem_of_union in Hsub as [Hsub|Htl].
          - apply elem_of_union in Hsub as [HzD|Hhd].
            + exact HzD.
            + rewrite elem_of_singleton in Hhd. inversion Hhd. subst z.
              contradiction.
          - rewrite elem_of_singleton in Htl. inversion Htl. subst z.
            contradiction.
        }
        exact HzD.
Qed.

Lemma lc_matchtree_iff_parts v eleaf enode :
  lc_tm (tmatchtree v eleaf enode) ->
  lc_value v /\
  lc_tm eleaf /\
	  exists L : aset,
	    forall root left right,
	      root ∉ L ->
	      left ∉ L ∪ {[root]} ->
	      right ∉ L ∪ {[root]} ∪ {[left]} ->
	      lc_tm (open_tree_node_branch root left right enode).
Proof.
  intros Hlc. inversion Hlc; subst.
  repeat split; eauto.
Qed.

Lemma lc_matchlist_iff_parts v enil econs :
  lc_tm (tmatchlist v enil econs) ->
  lc_value v /\
  lc_tm enil /\
	  exists L : aset,
	    forall hd tl,
	      hd ∉ L ->
	      tl ∉ L ∪ {[hd]} ->
	      lc_tm (open_list_cons_branch hd tl econs).
Proof.
  intros Hlc. inversion Hlc; subst.
  repeat split; eauto.
Qed.

Lemma basic_has_ltype_restrict_lvars_lc_mutual :
  (forall Σ v T,
    basic_value_has_ltype Σ v T ->
    lc_value v ->
    forall D,
      value_lvars v ⊆ D ->
      basic_value_has_ltype (storeA_restrict Σ D) v T) /\
  (forall Σ e T,
    basic_tm_has_ltype Σ e T ->
    lc_tm e ->
    forall D,
      tm_lvars e ⊆ D ->
      basic_tm_has_ltype (storeA_restrict Σ D) e T).
Proof.
  apply basic_has_ltype_mutind; intros; eauto.
  - constructor.
    match goal with
    | Hlook : ?Σ !! LVFree ?x = Some ?T |- _ =>
      apply (storeA_restrict_lookup_some_2 _ _ _ _ Hlook)
    end.
    match goal with
    | Hsub : value_lvars (vfvar _) ⊆ _ |- _ =>
        cbn [value_lvars value_lvars_at] in Hsub; set_solver
    end.
  - exfalso. eapply lc_bvar_absurd; eassumption.
  - apply lc_lam_iff_body in H0 as Hbody_lc.
    eapply BVT_Lam with
      (L := L ∪ lvars_fv D ∪ lvars_fv (dom Σ) ∪ fv_tm e).
    intros x Hx.
    pose proof (H x ltac:(set_solver)) as IHbody.
    specialize (IHbody (body_open_tm _ _ Hbody_lc (LC_fvar x))
      (tm_lvars (e ^^ x))).
    eapply basic_tm_has_ltype_weaken.
    + apply IHbody. reflexivity.
    + eapply lty_env_restrict_open_bind_body_subset.
      * intros Hdom. apply Hx.
        apply elem_of_union_l. apply elem_of_union_r.
        apply lvars_fv_elem. exact Hdom.
      * intros Hbad. apply Hx.
        apply elem_of_union_l. apply elem_of_union_l.
        apply elem_of_union_r. exact Hbad.
      * apply tm_lvars_no_bv_of_lc.
        apply body_open_tm; [exact Hbody_lc|constructor].
      * eapply tm_lvars_open_body_subset_lc; [exact Hbody_lc|].
        cbn [value_lvars value_lvars_at] in H1. exact H1.
  - apply lc_fix_iff_body in H0 as Hbody_lc.
    eapply BVT_Fix with
      (L := L ∪ lvars_fv D ∪ lvars_fv (dom Σ) ∪ fv_value vf).
    intros x Hx.
    pose proof (H x ltac:(set_solver)) as IHbody.
    specialize (IHbody (body_open_value _ _ Hbody_lc (LC_fvar x))
      (value_lvars (vf ^^ x))).
    eapply basic_value_has_ltype_weaken.
    + apply IHbody. reflexivity.
    + eapply lty_env_restrict_open_bind_body_subset.
      * intros Hdom. apply Hx.
        apply elem_of_union_l. apply elem_of_union_r.
        apply lvars_fv_elem. exact Hdom.
      * intros Hbad. apply Hx.
        apply elem_of_union_l. apply elem_of_union_l.
        apply elem_of_union_r. exact Hbad.
      * apply value_lvars_no_bv_of_lc.
        apply body_open_value; [exact Hbody_lc|constructor].
      * eapply value_lvars_open_body_subset_lc; [exact Hbody_lc|].
        cbn [value_lvars value_lvars_at] in H1. exact H1.
  - apply lc_ret_iff_value in H0.
    constructor. eapply H; eauto.
  - apply lc_lete_iff_body in H1 as [Hlc1 Hbody2].
    eapply BTT_Let with
      (L := L ∪ lvars_fv D ∪ lvars_fv (dom Σ) ∪ fv_tm e2).
    + eapply H; eauto. cbn [tm_lvars tm_lvars_at] in H2. set_solver.
    + intros x Hx.
      pose proof (H0 x ltac:(set_solver)) as IHbody.
      specialize (IHbody (body_open_tm _ _ Hbody2 (LC_fvar x))
        (tm_lvars (e2 ^^ x))).
      eapply basic_tm_has_ltype_weaken.
      * apply IHbody. reflexivity.
      * eapply lty_env_restrict_open_bind_body_subset.
        -- intros Hdom. apply Hx.
           apply elem_of_union_l. apply elem_of_union_r.
           apply lvars_fv_elem. exact Hdom.
        -- intros Hbad. apply Hx.
           apply elem_of_union_l. apply elem_of_union_l.
           apply elem_of_union_r. exact Hbad.
        -- apply tm_lvars_no_bv_of_lc.
           apply body_open_tm; [exact Hbody2|constructor].
        -- eapply tm_lvars_open_body_subset_lc; [exact Hbody2|].
           cbn [tm_lvars tm_lvars_at] in H2. set_solver.
  - match goal with
    | Hlc : lc_tm (tprim _ _) |- _ => apply lc_prim_iff_value in Hlc
    end.
    eapply BTT_Op.
    + match goal with
      | Hop : prim_op_type _ = _ |- _ => exact Hop
      end.
    +
    eapply H; eauto.
  - match goal with
    | Hlc : lc_tm (tapp _ _) |- _ =>
        apply lc_app_iff_values in Hlc as [Hlc1 Hlc2]
    end.
    eapply BTT_App.
    + eapply H; eauto.
      match goal with
      | Hsub : tm_lvars (tapp _ _) ⊆ _ |- _ =>
          cbn [tm_lvars tm_lvars_at] in Hsub; set_solver
      end.
    + eapply H0; eauto.
      match goal with
      | Hsub : tm_lvars (tapp _ _) ⊆ _ |- _ =>
          cbn [tm_lvars tm_lvars_at] in Hsub; set_solver
      end.
  - match goal with
    | Hlc : lc_tm (tmatch _ _ _) |- _ =>
        apply lc_match_iff_parts in Hlc as [Hlcv [Hlcet Hlcef]]
    end.
    eapply BTT_Match.
    + eapply H; eauto.
      match goal with
      | Hsub : tm_lvars (tmatch _ _ _) ⊆ _ |- _ =>
          cbn [tm_lvars tm_lvars_at] in Hsub; set_solver
      end.
    + eapply H0; eauto.
      match goal with
      | Hsub : tm_lvars (tmatch _ _ _) ⊆ _ |- _ =>
          cbn [tm_lvars tm_lvars_at] in Hsub; set_solver
      end.
    + eapply H1; eauto.
      match goal with
      | Hsub : tm_lvars (tmatch _ _ _) ⊆ _ |- _ =>
          cbn [tm_lvars tm_lvars_at] in Hsub; set_solver
      end.
  - match goal with
    | Hlc : lc_tm (tnode _ _ _) |- _ =>
        inversion Hlc; subst; clear Hlc
    end.
    eapply BTT_TreeNode.
    + eapply H; eauto.
      match goal with
      | Hsub : tm_lvars (tnode _ _ _) ⊆ _ |- _ =>
          cbn [tm_lvars tm_lvars_at] in Hsub; set_solver
      end.
    + eapply H0; eauto.
      match goal with
      | Hsub : tm_lvars (tnode _ _ _) ⊆ _ |- _ =>
          cbn [tm_lvars tm_lvars_at] in Hsub; set_solver
      end.
    + eapply H1; eauto.
      match goal with
      | Hsub : tm_lvars (tnode _ _ _) ⊆ _ |- _ =>
          cbn [tm_lvars tm_lvars_at] in Hsub; set_solver
      end.
  - match goal with
    | Hlc : lc_tm (tmatchtree _ _ _) |- _ =>
        apply lc_matchtree_iff_parts in Hlc as [Hlcv [Hlcleaf [Llc Hlcnode]]]
    end.
		    eapply BTT_TreeMatch with
		      (L := L ∪ Llc ∪ lvars_fv D ∪ lvars_fv (dom Σ) ∪ fv_tm enode).
		    + assert (Hv_sub : value_lvars v ⊆ D).
		      {
		        intros u Hu. apply H3.
		        cbn [tm_lvars tm_lvars_at].
		        apply elem_of_union_l. apply elem_of_union_l. exact Hu.
		      }
		      eapply H; [exact Hlcv|exact Hv_sub].
		    + assert (Hleaf_sub : tm_lvars eleaf ⊆ D).
		      {
		        intros u Hu. apply H3.
		        cbn [tm_lvars tm_lvars_at].
		        apply elem_of_union_l. apply elem_of_union_r. exact Hu.
		      }
		      eapply H0; [exact Hlcleaf|exact Hleaf_sub].
		    + intros root left right Hroot Hleft Hright.
		      assert (HrootL : root ∉ L).
		      {
		        intros Hin. apply Hroot.
		        repeat apply elem_of_union_l. exact Hin.
		      }
		      assert (HleftL : left ∉ L ∪ {[root]}).
		      {
		        intros Hin. apply Hleft.
		        apply elem_of_union in Hin as [Hin|Hin].
		        - apply elem_of_union_l. repeat apply elem_of_union_l. exact Hin.
		        - apply elem_of_union_r. exact Hin.
		      }
		      assert (HrightL : right ∉ L ∪ {[root]} ∪ {[left]}).
		      {
		        intros Hin. apply Hright.
		        apply elem_of_union in Hin as [Hin|Hin].
		        - apply elem_of_union in Hin as [Hin|Hin].
		          + apply elem_of_union_l. apply elem_of_union_l.
		            repeat apply elem_of_union_l. exact Hin.
		          + apply elem_of_union_l. apply elem_of_union_r. exact Hin.
		        - apply elem_of_union_r. exact Hin.
		      }
		      assert (HrootD : root ∉ lvars_fv D).
		      {
		        intros Hin. apply Hroot.
		        apply elem_of_union_l. apply elem_of_union_l.
		        apply elem_of_union_r. exact Hin.
		      }
		      assert (HleftD : left ∉ lvars_fv D).
		      {
		        intros Hin. apply Hleft.
		        apply elem_of_union_l. apply elem_of_union_l.
		        apply elem_of_union_l. apply elem_of_union_r. exact Hin.
		      }
		      assert (HrightD : right ∉ lvars_fv D).
		      {
		        intros Hin. apply Hright.
		        apply elem_of_union_l. apply elem_of_union_l.
		        apply elem_of_union_l. apply elem_of_union_l.
		        apply elem_of_union_r. exact Hin.
		      }
		      assert (HrootΣ : root ∉ lvars_fv (dom Σ)).
		      {
		        intros Hin. apply Hroot.
		        apply elem_of_union_l. apply elem_of_union_r. exact Hin.
		      }
		      assert (HleftΣ : left ∉ lvars_fv (dom Σ)).
		      {
		        intros Hin. apply Hleft.
		        apply elem_of_union_l. apply elem_of_union_l.
		        apply elem_of_union_r. exact Hin.
		      }
		      assert (HrightΣ : right ∉ lvars_fv (dom Σ)).
		      {
		        intros Hin. apply Hright.
		        apply elem_of_union_l. apply elem_of_union_l.
		        apply elem_of_union_l. apply elem_of_union_r. exact Hin.
		      }
		      assert (Hroot_left : root <> left).
		      {
		        intro Heq. apply Hleft. apply elem_of_union_r.
		        rewrite elem_of_singleton. symmetry. exact Heq.
		      }
		      assert (Hroot_right : root <> right).
		      {
		        intro Heq. apply Hright. apply elem_of_union_l.
		        apply elem_of_union_r.
		        rewrite elem_of_singleton. symmetry. exact Heq.
		      }
			      assert (Hleft_right : left <> right).
			      {
			        intro Heq. apply Hright. apply elem_of_union_r.
			        rewrite elem_of_singleton. symmetry. exact Heq.
			      }
			      assert (HrootLlc : root ∉ Llc) by (clear -Hroot; set_solver).
			      assert (HleftLlc : left ∉ Llc ∪ {[root]})
			        by (clear -Hleft; set_solver).
			      assert (HrightLlc : right ∉ Llc ∪ {[root]} ∪ {[left]})
			        by (clear -Hright; set_solver).
			      assert (Hbranch_lc :
			        lc_tm (open_tree_node_branch root left right enode)).
			      { eapply Hlcnode; [exact HrootLlc|exact HleftLlc|exact HrightLlc]. }
		      pose proof (H1 root left right HrootL HleftL HrightL) as IHbranch.
		      eapply basic_tm_has_ltype_weaken.
		      * apply IHbranch.
		        -- exact Hbranch_lc.
	        -- reflexivity.
			      * eapply lty_env_restrict_tree_node_branch_open_env_body_subset.
			        -- exact Hroot_left.
			        -- exact Hroot_right.
			        -- exact Hleft_right.
			        -- exact HrootD.
			        -- exact HleftD.
			        -- exact HrightD.
			        -- apply tm_lvars_no_bv_of_lc.
			           exact Hbranch_lc.
	        -- intros u Hu.
	           rewrite (tm_lvars_lc_eq_atoms
	             (open_tree_node_branch root left right enode)) in Hu.
	           2:{ exact Hbranch_lc. }
           unfold lvars_of_atoms in Hu.
           apply elem_of_map in Hu as [a [-> Ha0]].
           unfold open_tree_node_branch, open_tree_node_branch_value in Ha0.
	           pose proof (open_fv_tm
	             (open_tm 1 (vfvar left) (open_tm 0 (vfvar root) enode))
	             (vfvar right) 2 a Ha0) as Ha1.
	           cbn [fv_value] in Ha1.
	           apply elem_of_union in Ha1 as [Ha1|Ha1].
	           ++ rewrite elem_of_singleton in Ha1. subst a.
	              apply elem_of_union_r. apply elem_of_singleton. reflexivity.
	           ++ pose proof (open_fv_tm
	                (open_tm 0 (vfvar root) enode) (vfvar left) 1 a Ha1) as Ha2.
	              cbn [fv_value] in Ha2.
	              apply elem_of_union in Ha2 as [Ha2|Ha2].
	              ** rewrite elem_of_singleton in Ha2. subst a.
	                 apply elem_of_union_l. apply elem_of_union_r.
	                 apply elem_of_singleton. reflexivity.
	              ** pose proof (open_fv_tm enode (vfvar root) 0 a Ha2) as Ha3.
	                 cbn [fv_value] in Ha3.
	                 apply elem_of_union in Ha3 as [Ha3|Ha3].
	                 --- rewrite elem_of_singleton in Ha3. subst a.
	                     apply elem_of_union_l. apply elem_of_union_l.
	                     apply elem_of_union_r. apply elem_of_singleton.
	                     reflexivity.
                 --- assert (LVFree a ∈ D) as HaD.
                     {
                       match goal with
                       | Hsub : tm_lvars (tmatchtree _ _ _) ⊆ D |- _ =>
                           cbn [tm_lvars tm_lvars_at] in Hsub;
                           apply Hsub
                       end.
                       apply elem_of_union_r.
                       apply lvars_fv_elem.
	                       rewrite tm_lvars_at_fv. exact Ha3.
	                     }
	                     apply elem_of_union_l. apply elem_of_union_l.
	                     apply elem_of_union_l. exact HaD.
  - match goal with
    | Hlc : lc_tm (tcons _ _) |- _ =>
        inversion Hlc; subst; clear Hlc
    end.
    eapply BTT_ListCons.
    + eapply H; eauto.
      match goal with
      | Hsub : tm_lvars (tcons _ _) ⊆ _ |- _ =>
          cbn [tm_lvars tm_lvars_at] in Hsub; set_solver
      end.
    + eapply H0; eauto.
      match goal with
      | Hsub : tm_lvars (tcons _ _) ⊆ _ |- _ =>
          cbn [tm_lvars tm_lvars_at] in Hsub; set_solver
      end.
  - match goal with
    | Hlc : lc_tm (tmatchlist _ _ _) |- _ =>
        apply lc_matchlist_iff_parts in Hlc as [Hlcv [Hlcnil [Llc Hlccons]]]
    end.
    eapply BTT_ListMatch with
      (L := L ∪ Llc ∪ lvars_fv D ∪ lvars_fv (dom Σ) ∪ fv_tm econs).
    + assert (Hv_sub : value_lvars v ⊆ D).
      {
        intros u Hu. apply H3.
        cbn [tm_lvars tm_lvars_at].
        apply elem_of_union_l. apply elem_of_union_l. exact Hu.
      }
      eapply H; [exact Hlcv|exact Hv_sub].
    + assert (Hnil_sub : tm_lvars enil ⊆ D).
      {
        intros u Hu. apply H3.
        cbn [tm_lvars tm_lvars_at].
        apply elem_of_union_l. apply elem_of_union_r. exact Hu.
      }
      eapply H0; [exact Hlcnil|exact Hnil_sub].
    + intros hd tl Hhd Htl.
      assert (HhdL : hd ∉ L) by (clear -Hhd; set_solver).
      assert (HtlL : tl ∉ L ∪ {[hd]}) by (clear -Htl; set_solver).
      assert (HhdD : hd ∉ lvars_fv D) by (clear -Hhd; set_solver).
      assert (HtlD : tl ∉ lvars_fv D) by (clear -Htl; set_solver).
      assert (HhdΣ : hd ∉ lvars_fv (dom Σ)) by (clear -Hhd; set_solver).
      assert (HtlΣ : tl ∉ lvars_fv (dom Σ)) by (clear -Htl; set_solver).
      assert (Hhd_tl : hd <> tl).
      {
        intro Heq. apply Htl. apply elem_of_union_r.
        rewrite elem_of_singleton. symmetry. exact Heq.
      }
      assert (HhdLlc : hd ∉ Llc) by (clear -Hhd; set_solver).
      assert (HtlLlc : tl ∉ Llc ∪ {[hd]}) by (clear -Htl; set_solver).
      assert (Hbranch_lc :
        lc_tm (open_list_cons_branch hd tl econs)).
      { eapply Hlccons; [exact HhdLlc|exact HtlLlc]. }
      pose proof (H1 hd tl HhdL HtlL) as IHbranch.
      eapply basic_tm_has_ltype_weaken.
      * apply IHbranch.
        -- exact Hbranch_lc.
        -- reflexivity.
      * eapply lty_env_restrict_list_cons_branch_open_env_body_subset.
        -- exact Hhd_tl.
        -- exact HhdD.
        -- exact HtlD.
        -- apply tm_lvars_no_bv_of_lc. exact Hbranch_lc.
        -- intros u Hu.
           rewrite (tm_lvars_lc_eq_atoms
             (open_list_cons_branch hd tl econs)) in Hu.
           2:{ exact Hbranch_lc. }
           unfold lvars_of_atoms in Hu.
           apply elem_of_map in Hu as [a [-> Ha0]].
           unfold open_list_cons_branch, open_list_cons_branch_value in Ha0.
           pose proof (open_fv_tm
             (open_tm 0 (vfvar hd) econs) (vfvar tl) 1 a Ha0) as Ha1.
           cbn [fv_value] in Ha1.
           apply elem_of_union in Ha1 as [Ha1|Ha1].
           ++ rewrite elem_of_singleton in Ha1. subst a.
              apply elem_of_union_r. apply elem_of_singleton. reflexivity.
           ++ pose proof (open_fv_tm econs (vfvar hd) 0 a Ha1) as Ha2.
              cbn [fv_value] in Ha2.
              apply elem_of_union in Ha2 as [Ha2|Ha2].
              ** rewrite elem_of_singleton in Ha2. subst a.
                 apply elem_of_union_l. apply elem_of_union_r.
                 apply elem_of_singleton. reflexivity.
              ** assert (LVFree a ∈ D) as HaD.
                 {
                   match goal with
                   | Hsub : tm_lvars (tmatchlist _ _ _) ⊆ D |- _ =>
                       cbn [tm_lvars tm_lvars_at] in Hsub;
                       apply Hsub
                   end.
                   apply elem_of_union_r.
                   apply lvars_fv_elem.
                   rewrite tm_lvars_at_fv. exact Ha2.
                 }
                 apply elem_of_union_l. apply elem_of_union_l. exact HaD.
Qed.

Lemma basic_value_has_ltype_restrict_lvars_lc Σ v T D :
  basic_value_has_ltype Σ v T ->
  lc_value v ->
  value_lvars v ⊆ D ->
  basic_value_has_ltype (storeA_restrict Σ D) v T.
Proof.
  intros Hty Hlc Hsub.
  exact (proj1 basic_has_ltype_restrict_lvars_lc_mutual
    Σ v T Hty Hlc D Hsub).
Qed.

Lemma basic_tm_has_ltype_restrict_lvars_lc Σ e T D :
  basic_tm_has_ltype Σ e T ->
  lc_tm e ->
  tm_lvars e ⊆ D ->
  basic_tm_has_ltype (storeA_restrict Σ D) e T.
Proof.
  intros Hty Hlc Hsub.
  exact (proj2 basic_has_ltype_restrict_lvars_lc_mutual
    Σ e T Hty Hlc D Hsub).
Qed.

Lemma basic_value_has_ltype_env_agree_lc Σ1 Σ2 v T :
  basic_value_has_ltype Σ1 v T ->
  lc_value v ->
  storeA_restrict Σ1 (value_lvars v) =
    storeA_restrict Σ2 (value_lvars v) ->
  basic_value_has_ltype Σ2 v T.
Proof.
  intros Hty Hlc Hagree.
  eapply (basic_value_has_ltype_weaken
    (storeA_restrict Σ2 (value_lvars v)) Σ2).
  - rewrite <- Hagree.
    eapply basic_value_has_ltype_restrict_lvars_lc;
      [exact Hty|exact Hlc|reflexivity].
  - apply map_subseteq_spec. intros v0 T0 Hlook.
    apply storeA_restrict_lookup_some in Hlook as [_ Hlook].
    exact Hlook.
Qed.

Lemma basic_tm_has_ltype_env_agree_lc Σ1 Σ2 e T :
  basic_tm_has_ltype Σ1 e T ->
  lc_tm e ->
  storeA_restrict Σ1 (tm_lvars e) =
    storeA_restrict Σ2 (tm_lvars e) ->
  basic_tm_has_ltype Σ2 e T.
Proof.
  intros Hty Hlc Hagree.
  eapply (basic_tm_has_ltype_weaken
    (storeA_restrict Σ2 (tm_lvars e)) Σ2).
  - rewrite <- Hagree.
    eapply basic_tm_has_ltype_restrict_lvars_lc;
      [exact Hty|exact Hlc|reflexivity].
  - apply map_subseteq_spec. intros v0 T0 Hlook.
    apply storeA_restrict_lookup_some in Hlook as [_ Hlook].
    exact Hlook.
Qed.

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
  - match goal with
    | |- basic_value_has_ltype (atom_env_to_lty_env ?Γ) _ _ =>
        eapply BVT_Lam with (L := L ∪ dom Γ)
    end.
    intros x Hx.
    pose proof (H x ltac:(set_solver)) as Hbody.
    rewrite lvar_store_open_bind_atom_store by set_solver.
    exact Hbody.
  - match goal with
    | |- basic_value_has_ltype (atom_env_to_lty_env ?Γ) _ _ =>
        eapply BVT_Fix with (L := L ∪ dom Γ)
    end.
    intros x Hx.
    pose proof (H x ltac:(set_solver)) as Hbody.
    rewrite lvar_store_open_bind_atom_store by set_solver.
    exact Hbody.
  - match goal with
    | |- basic_tm_has_ltype (atom_env_to_lty_env ?Γ) _ _ =>
        eapply BTT_Let with (L := L ∪ dom Γ)
    end; eauto.
    intros x Hx.
    pose proof (H0 x ltac:(set_solver)) as Hbody.
    rewrite lvar_store_open_bind_atom_store by set_solver.
    exact Hbody.
  - match goal with
    | |- basic_tm_has_ltype (atom_env_to_lty_env ?Γ) _ _ =>
        eapply BTT_TreeMatch with (L := L ∪ dom Γ)
    end; eauto.
    intros root left right Hroot Hleft Hright.
	    pose proof (H1 root left right
	      ltac:(set_solver) ltac:(set_solver) ltac:(set_solver)) as Hbody.
	    rewrite (tree_node_branch_open_env_norm
	      (atom_env_to_lty_env Γ) root left right).
	    2:{ apply atom_store_to_lvar_store_closed. }
	    2:{ rewrite atom_store_to_lvar_store_dom. clear -Hroot. set_solver. }
	    2:{ rewrite atom_store_to_lvar_store_dom. clear -Hleft. set_solver. }
	    2:{ rewrite atom_store_to_lvar_store_dom. clear -Hright. set_solver. }
	    2:{ clear -Hleft. set_solver. }
	    2:{ clear -Hright. set_solver. }
	    2:{ clear -Hright. set_solver. }
	    rewrite <- !atom_store_to_lvar_store_insert.
	    exact Hbody.
  - match goal with
    | |- basic_tm_has_ltype (atom_env_to_lty_env ?Γ) _ _ =>
        eapply BTT_ListMatch with (L := L ∪ dom Γ)
    end; eauto.
    intros hd tl Hhd Htl.
    pose proof (H1 hd tl
      ltac:(set_solver) ltac:(set_solver)) as Hbody.
    rewrite (list_cons_branch_open_env_norm
      (atom_env_to_lty_env Γ) hd tl).
    2:{ apply atom_store_to_lvar_store_closed. }
    2:{ rewrite atom_store_to_lvar_store_dom. clear -Hhd. set_solver. }
    2:{ rewrite atom_store_to_lvar_store_dom. clear -Htl. set_solver. }
    2:{ clear -Htl. set_solver. }
    rewrite <- !atom_store_to_lvar_store_insert.
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

Lemma basic_has_ltype_to_atom_typing_mutual :
  (forall Σ v T,
    basic_value_has_ltype Σ v T ->
    forall Δ,
      Σ = atom_env_to_lty_env Δ ->
      Δ ⊢ᵥ v ⋮ T) /\
  (forall Σ e T,
    basic_tm_has_ltype Σ e T ->
    forall Δ,
      Σ = atom_env_to_lty_env Δ ->
      Δ ⊢ₑ e ⋮ T).
Proof.
  apply basic_has_ltype_mutind; intros; subst.
  - constructor.
  - constructor.
    match goal with
    | Hlook : (atom_env_to_lty_env Δ : gmap logic_var ty) !! LVFree x =
        Some T |- _ =>
        rewrite atom_store_to_lvar_store_lookup_free in Hlook;
        exact Hlook
    end.
  - match goal with
    | Hlook : (atom_env_to_lty_env Δ : gmap logic_var ty) !! LVBound k =
        Some T |- _ =>
        rewrite atom_store_to_lvar_store_lookup_bound_none in Hlook;
        discriminate
    end.
  - eapply VT_Lam with (L := L ∪ dom Δ).
    intros x Hx.
    specialize (H x ltac:(set_solver) (<[x := s]> Δ)).
    exact (H (lvar_store_open_bind_atom_store Δ s x ltac:(set_solver))).
  - eapply VT_Fix with (L := L ∪ dom Δ).
    intros x Hx.
    specialize (H x ltac:(set_solver) (<[x := sx]> Δ)).
    exact (H (lvar_store_open_bind_atom_store Δ sx x ltac:(set_solver))).
  - eapply TT_Ret. eauto.
  - eapply TT_Let with (L := L ∪ dom Δ).
    + eauto.
    + intros x Hx.
      specialize (H0 x ltac:(set_solver) (<[x := T1]> Δ)).
      exact (H0 (lvar_store_open_bind_atom_store Δ T1 x ltac:(set_solver))).
  - eapply TT_Op; eauto.
  - eapply TT_App; eauto.
  - eapply TT_Match; eauto.
  - eapply TT_TreeNode; eauto.
  - eapply TT_TreeMatch with (L := L ∪ dom Δ).
    + eauto.
    + eauto.
    + intros root left right Hroot Hleft Hright.
      specialize (H1 root left right
        ltac:(set_solver) ltac:(set_solver) ltac:(set_solver)
        (<[right := TBase TTree]>
          (<[left := TBase TTree]>
            (<[root := TBase TNat]> Δ)))).
		      apply H1.
		      rewrite (tree_node_branch_open_env_norm
		        (atom_env_to_lty_env Δ) root left right).
		      2:{ apply atom_store_to_lvar_store_closed. }
		      2:{ rewrite atom_store_to_lvar_store_dom. clear -Hroot. set_solver. }
		      2:{ rewrite atom_store_to_lvar_store_dom. clear -Hleft. set_solver. }
		      2:{ rewrite atom_store_to_lvar_store_dom. clear -Hright. set_solver. }
		      2:{ clear -Hleft. set_solver. }
		      2:{ clear -Hright. set_solver. }
		      2:{ clear -Hright. set_solver. }
		      rewrite <- !atom_store_to_lvar_store_insert.
		      reflexivity.
  - eapply TT_ListCons; eauto.
  - eapply TT_ListMatch with (L := L ∪ dom Δ).
    + eauto.
    + eauto.
    + intros hd tl Hhd Htl.
      specialize (H1 hd tl
        ltac:(set_solver) ltac:(set_solver)
        (<[tl := TBase TList]>
          (<[hd := TBase TNat]> Δ))).
      apply H1.
      rewrite (list_cons_branch_open_env_norm
        (atom_env_to_lty_env Δ) hd tl).
      2:{ apply atom_store_to_lvar_store_closed. }
      2:{ rewrite atom_store_to_lvar_store_dom. clear -Hhd. set_solver. }
      2:{ rewrite atom_store_to_lvar_store_dom. clear -Htl. set_solver. }
      2:{ clear -Htl. set_solver. }
      rewrite <- !atom_store_to_lvar_store_insert.
      reflexivity.
Qed.

Lemma basic_tm_has_ltype_to_atom_env_typing Δ e T :
  basic_tm_has_ltype (atom_env_to_lty_env Δ) e T ->
  Δ ⊢ₑ e ⋮ T.
Proof.
  intros Hty.
  exact (proj2 basic_has_ltype_to_atom_typing_mutual
    (atom_env_to_lty_env Δ) e T Hty Δ eq_refl).
Qed.

Lemma atom_store_has_ltype_env_has_type Σ σ :
  atom_store_has_ltype Σ σ ->
  env_has_type (lty_env_to_atom_env Σ) σ.
Proof.
  intros Hσ x T v HΣx Hσx.
  destruct (Hσ x v Hσx) as [U [HΣU Hv]].
  change ((lvar_store_to_atom_store Σ : gmap atom ty) !! x = Some T)
    in HΣx.
  apply lvar_store_to_atom_store_lookup_some in HΣx as HΣT.
  change (((Σ : gmap logic_var ty) !! LVFree x) = Some U) in HΣU.
  change (((Σ : gmap logic_var ty) !! LVFree x) = Some T) in HΣT.
  rewrite HΣU in HΣT.
  inversion HΣT. subst U. exact Hv.
Qed.

Lemma basic_value_has_ltype_of_empty_atom_typing Σ v T :
  ∅ ⊢ᵥ v ⋮ T ->
  basic_value_has_ltype Σ v T.
Proof.
  intros Hty.
  eapply basic_value_has_ltype_weaken.
  - exact (basic_value_has_ltype_of_atom_env_typing ∅ v T Hty).
  - apply map_empty_subseteq.
Qed.

Lemma empty_basic_value_base_inv v b :
  ∅ ⊢ᵥ v ⋮ TBase b ->
  exists c, v = vconst c /\ base_ty_of_const c = b.
Proof.
  intros Hty.
  inversion Hty; subst; try discriminate.
  exists c. split; [reflexivity|congruence].
Qed.

Lemma basic_has_ltype_unique_mutual :
  (forall Σ v T1,
    basic_value_has_ltype Σ v T1 ->
    forall T2, basic_value_has_ltype Σ v T2 -> T1 = T2) /\
  (forall Σ e T1,
    basic_tm_has_ltype Σ e T1 ->
    forall T2, basic_tm_has_ltype Σ e T2 -> T1 = T2).
Proof.
  apply basic_has_ltype_mutind; intros;
    match goal with
    | |- _ = ?T2 =>
        match goal with
        | H : basic_value_has_ltype _ _ T2 |- _ => inversion H; subst
        | H : basic_tm_has_ltype _ _ T2 |- _ => inversion H; subst
        end
    end.
  - reflexivity.
  - match goal with
    | H1 : ?Σ !! LVFree ?x = Some ?T1,
      H2 : ?Σ !! LVFree ?x = Some ?T2 |- _ =>
        rewrite H1 in H2; inversion H2; reflexivity
    end.
  - match goal with
    | H1 : ?Σ !! LVBound ?k = Some ?T1,
      H2 : ?Σ !! LVBound ?k = Some ?T2 |- _ =>
        rewrite H1 in H2; inversion H2; reflexivity
    end.
  -
	    match goal with
	    | IH : forall x, x ∉ ?L1 -> forall T2,
	        basic_tm_has_ltype
	          (lty_env_open_one 0 x (typed_lty_env_bind _ _))
	          (_ ^^ x) T2 -> _,
	      Hbody : forall x, x ∉ ?L2 ->
	        basic_tm_has_ltype
	          (lty_env_open_one 0 x (typed_lty_env_bind _ _))
	          (_ ^^ x) _ |- _ =>
        set (y := fresh_for (L1 ∪ L2));
        assert (Hy : y ∉ L1 ∪ L2) by (subst y; apply fresh_for_not_in);
        pose proof (IH y ltac:(set_solver) _ (Hbody y ltac:(set_solver))) as Heq
    end.
    subst. reflexivity.
  -
	    match goal with
	    | IH : forall x, x ∉ ?L1 -> forall T2,
	        basic_value_has_ltype
	          (lty_env_open_one 0 x (typed_lty_env_bind _ _))
	          (_ ^^ x) T2 -> _,
	      Hbody : forall x, x ∉ ?L2 ->
	        basic_value_has_ltype
	          (lty_env_open_one 0 x (typed_lty_env_bind _ _))
	          (_ ^^ x) _ |- _ =>
        set (y := fresh_for (L1 ∪ L2));
        assert (Hy : y ∉ L1 ∪ L2) by (subst y; apply fresh_for_not_in);
        pose proof (IH y ltac:(set_solver) _ (Hbody y ltac:(set_solver))) as Heq
    end.
    inversion Heq. reflexivity.
  - eauto.
  - match goal with
    | IH1 : forall T2, basic_tm_has_ltype _ _ T2 -> ?T1 = T2,
      Hty1 : basic_tm_has_ltype _ _ ?T1' |- _ =>
        pose proof (IH1 _ Hty1) as Heq1
    end.
    subst.
	    match goal with
	    | IH2 : forall x, x ∉ ?L1 -> forall T2,
	        basic_tm_has_ltype
	          (lty_env_open_one 0 x (typed_lty_env_bind _ _))
	          (_ ^^ x) T2 -> _,
	      Hbody : forall x, x ∉ ?L2 ->
	        basic_tm_has_ltype
	          (lty_env_open_one 0 x (typed_lty_env_bind _ _))
	          (_ ^^ x) _ |- _ =>
        set (y := fresh_for (L1 ∪ L2));
        assert (Hy : y ∉ L1 ∪ L2) by (subst y; apply fresh_for_not_in);
        exact (IH2 y ltac:(set_solver) _ (Hbody y ltac:(set_solver)))
    end.
  - match goal with
    | Hop1 : prim_op_type ?op = (?a1, ?r1),
      Hop2 : prim_op_type ?op = (?a2, ?r2) |- _ =>
        rewrite Hop1 in Hop2; inversion Hop2; reflexivity
    end.
  - match goal with
    | IH : forall T2, basic_value_has_ltype _ _ T2 -> _,
      Hfun : basic_value_has_ltype _ _ (_ →ₜ _) |- _ =>
        pose proof (IH _ Hfun) as Heq
    end.
    inversion Heq. reflexivity.
  - match goal with
    | IH : forall T2, basic_tm_has_ltype _ _ T2 -> _,
      Hthen : basic_tm_has_ltype _ _ _ |- _ =>
        exact (IH _ Hthen)
    end.
  - reflexivity.
  - match goal with
    | IH : forall T2, basic_tm_has_ltype _ _ T2 -> _,
      Hleaf : basic_tm_has_ltype _ _ _ |- _ =>
        exact (IH _ Hleaf)
    end.
  - reflexivity.
  - match goal with
    | IH : forall T2, basic_tm_has_ltype _ _ T2 -> _,
      Hnil : basic_tm_has_ltype _ _ _ |- _ =>
        exact (IH _ Hnil)
    end.
Qed.

Lemma basic_value_has_ltype_unique Σ v T1 T2 :
  basic_value_has_ltype Σ v T1 ->
  basic_value_has_ltype Σ v T2 ->
  T1 = T2.
Proof.
  intros H1 H2.
  exact (proj1 basic_has_ltype_unique_mutual Σ v T1 H1 T2 H2).
Qed.

Lemma atom_store_has_ltype_lookup_from_basic_ltype Σ σ x vx T :
  atom_store_has_ltype Σ σ ->
  σ !! x = Some vx ->
  basic_value_has_ltype (lty_env_msubst_store σ Σ) vx T ->
  Σ !! LVFree x = Some T.
Proof.
  intros Hσtyped Hσx HvxT.
  destruct (Hσtyped x vx Hσx) as [U [HΣU HvxU]].
  assert (HvxU_basic :
    basic_value_has_ltype (lty_env_msubst_store σ Σ) vx U).
  { apply basic_value_has_ltype_of_empty_atom_typing. exact HvxU. }
  pose proof (basic_value_has_ltype_unique _ _ _ _ HvxU_basic HvxT)
    as ->.
  exact HΣU.
Qed.

Lemma basic_value_has_ltype_msubst_store_back_fvar
    Σ σ x vx T :
  atom_store_has_ltype Σ σ ->
  σ !! x = Some vx ->
  basic_value_has_ltype (lty_env_msubst_store σ Σ) vx T ->
  basic_value_has_ltype Σ (vfvar x) T.
Proof.
  intros Hσ Hlook Hty.
  constructor.
  eapply atom_store_has_ltype_lookup_from_basic_ltype; eauto.
Qed.

(** The syntactic well-formedness of [τ] is not a runtime property of the
    world, but we still package it as a world-independent logic qualifier.
    Unlike [basic_context_ty], this version is scoped by the lvar-domain of [Σ]
    directly, so bound lvars in a type body are preserved until the surrounding
    formula open swaps them to atoms. *)
Definition context_ty_wf_qual
    (Σ : lty_env) (τ : context_ty) : qualifier (V := value) :=
  tqual (dom Σ)
    (fun _ => basic_context_ty_lvars (dom Σ) τ).
Definition context_ty_wf_formula
    (Σ : lty_env) (τ : context_ty) : Formula :=
  FFiberAtom (context_ty_wf_qual Σ τ).
Lemma formula_fv_context_ty_wf_formula Σ τ :
  formula_fv (context_ty_wf_formula Σ τ) = lvars_fv (dom Σ).
Proof.
  unfold context_ty_wf_formula, context_ty_wf_qual.
  rewrite formula_fv_fiber_atom. reflexivity.
Qed.
Definition expr_basic_typing_qual
    (Σ : lty_env) (e : tm) (T : ty) : qualifier (V := value) :=
  tqual (dom Σ)
    (fun _ => basic_tm_has_ltype Σ e T).
Definition expr_basic_typing_formula
    (Σ : lty_env) (e : tm) (T : ty) : Formula :=
  FFiberAtom (expr_basic_typing_qual Σ e T).
Lemma formula_fv_expr_basic_typing_formula Σ e T :
  formula_fv (expr_basic_typing_formula Σ e T) = lvars_fv (dom Σ).
Proof.
  unfold expr_basic_typing_formula, expr_basic_typing_qual.
  rewrite formula_fv_fiber_atom. reflexivity.
Qed.

Lemma context_ty_wf_formula_models_iff Σ τ (m : WfWorldT) :
  res_models m (context_ty_wf_formula Σ τ) <->
  lc_lvars (dom Σ) /\
  lvars_fv (dom Σ) ⊆ world_dom (m : WorldT) /\
  basic_context_ty_lvars (dom Σ) τ.
Proof.
  split.
  - intros Hmodels.
    apply res_models_FFiberAtom_store_iff in Hmodels as [Hscope Hstores].
    destruct (world_wf m) as [[σ Hσ] _].
    specialize (Hstores σ Hσ) as [Hlc [_ Hbasic]].
    split; [exact Hlc|]. split.
    + unfold formula_scoped_in_world in Hscope.
      rewrite formula_fv_fiber_atom in Hscope. exact Hscope.
    + exact Hbasic.
  - intros [Hlc [Hsub Hbasic]].
    apply res_models_FFiberAtom_store_iff.
    split.
    + unfold formula_scoped_in_world.
      rewrite formula_fv_fiber_atom. exact Hsub.
    + intros σ Hσ.
      cbn [context_ty_wf_qual qualifier_holds_store qual_lvars qual_prop].
      exists Hlc.
      assert (Hsubσ : lvars_fv (dom Σ) ⊆ dom (σ : StoreT)).
      {
        intros x Hx.
        change (x ∈ dom (σ : gmap atom value)).
        replace (dom (σ : StoreT)) with (world_dom (m : WorldT))
          by (symmetry; apply (wfworld_store_dom m σ Hσ)).
        exact (Hsub x Hx).
      }
      exists Hsubσ. exact Hbasic.
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

Lemma expr_basic_typing_formula_models_iff Σ e T (m : WfWorldT) :
  res_models m (expr_basic_typing_formula Σ e T) <->
  lc_lvars (dom Σ) /\
  lvars_fv (dom Σ) ⊆ world_dom (m : WorldT) /\
  basic_tm_has_ltype Σ e T.
Proof.
  split.
  - intros Hmodels.
    apply res_models_FFiberAtom_store_iff in Hmodels as [Hscope Hstores].
    destruct (world_wf m) as [[σ Hσ] _].
    specialize (Hstores σ Hσ) as [Hlc [_ Hbasic]].
    split; [exact Hlc|]. split.
    + unfold formula_scoped_in_world in Hscope.
      rewrite formula_fv_fiber_atom in Hscope. exact Hscope.
    + exact Hbasic.
  - intros [Hlc [Hsub Hbasic]].
    apply res_models_FFiberAtom_store_iff.
    split.
    + unfold formula_scoped_in_world.
      rewrite formula_fv_fiber_atom. exact Hsub.
    + intros σ Hσ.
      cbn [expr_basic_typing_qual qualifier_holds_store qual_lvars qual_prop].
      exists Hlc.
      assert (Hsubσ : lvars_fv (dom Σ) ⊆ dom (σ : StoreT)).
      {
        intros x Hx.
        change (x ∈ dom (σ : gmap atom value)).
        replace (dom (σ : StoreT)) with (world_dom (m : WorldT))
          by (symmetry; apply (wfworld_store_dom m σ Hσ)).
        exact (Hsub x Hx).
      }
      exists Hsubσ. exact Hbasic.
Qed.

Lemma expr_basic_typing_formula_basic_ltype Σ e T (m : WfWorldT) :
  res_models m (expr_basic_typing_formula Σ e T) ->
  basic_tm_has_ltype Σ e T.
Proof.
  intros Hmodels.
  apply expr_basic_typing_formula_models_iff in Hmodels as [_ [_ Hbasic]].
  exact Hbasic.
Qed.

Lemma expr_basic_typing_world_closed_on_term Σ e T (m : WfWorldT) :
  res_models m (basic_world_formula Σ) ->
  res_models m (expr_basic_typing_formula Σ e T) ->
  wfworld_closed_on (fv_tm e) m.
Proof.
  intros Hworld Hbasic.
  eapply basic_world_formula_wfworld_closed_on_atoms; [|exact Hworld].
  apply expr_basic_typing_formula_models_iff in Hbasic as [_ [_ Hty]].
  exact (basic_tm_has_ltype_lvars _ _ _ Hty).
Qed.

End BasicTypingFormula.

Notation "'FWfTy' '[' Σ ';' τ ']'" := (context_ty_wf_formula Σ τ)
  (at level 10, Σ at level 9, τ at level 9,
   format "FWfTy [ Σ ;  τ ]") : formula_scope.

Notation "'FHasType' '[' Σ '⊢' e '⋮' T ']'" := (expr_basic_typing_formula Σ e T)
  (at level 10, Σ at level 9, e at level 9, T at level 9,
   format "FHasType [ Σ  ⊢  e  ⋮  T ]") : formula_scope.
