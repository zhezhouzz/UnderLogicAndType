(** * ChoiceTyping.TLetTotal

    Totality and context-preservation helpers for [tlet] result worlds. *)

From CoreLang Require Import Instantiation InstantiationProps OperationalProps BasicTypingProps
  LocallyNamelessProps.
From ChoiceTyping Require Export TLetGraph.
From ChoiceTyping Require Import Naming.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

Lemma expr_total_results_on_le
    X e (m n : WfWorld) :
  X ⊆ world_dom (m : World) →
  m ⊑ n →
  (∀ σ, (m : World) σ →
    ∃ v, subst_map (store_restrict σ X) e →* tret v) →
  ∀ σ, (n : World) σ →
    ∃ v, subst_map (store_restrict σ X) e →* tret v.
Proof.
  intros HXm Hle Hresult σn Hσn.
  unfold sqsubseteq, wf_world_sqsubseteq, raw_le in Hle.
  specialize (Hresult (store_restrict σn (world_dom (m : World)))).
  assert (Hσm :
    (m : World) (store_restrict σn (world_dom (m : World)))).
  {
    rewrite Hle. simpl.
    exists σn. split; [exact Hσn |].
    pose proof (raw_le_dom (m : World) (n : World)
      ltac:(unfold raw_le; exact Hle)) as Hdom_mn.
    replace (world_dom (n : World) ∩ world_dom (m : World))
      with (world_dom (m : World)) by set_solver.
    reflexivity.
  }
  destruct (Hresult Hσm) as [v Hsteps].
  exists v.
  store_norm.
  exact Hsteps.
Qed.

Lemma expr_total_results_on_restrict
    X e (m n : WfWorld) :
  X ⊆ world_dom (m : World) →
  m ⊑ n →
  (∀ σ, (n : World) σ →
    ∃ v, subst_map (store_restrict σ X) e →* tret v) →
  ∀ σ, (m : World) σ →
    ∃ v, subst_map (store_restrict σ X) e →* tret v.
Proof.
  intros HXm Hle Hresult σm Hσm.
  unfold sqsubseteq, wf_world_sqsubseteq, raw_le in Hle.
  rewrite Hle in Hσm. simpl in Hσm.
  destruct Hσm as [σn [Hσn Hrestrict]].
  destruct (Hresult σn Hσn) as [v Hsteps].
  exists v.
  rewrite <- Hrestrict.
  store_norm.
  exact Hsteps.
Qed.

Lemma let_result_world_on_base_mono
    X e x (m n : WfWorld)
    (Hfresh_m : x ∉ world_dom (m : World))
    (Hfresh_n : x ∉ world_dom (n : World))
    Hresult_m Hresult_n :
  X ⊆ world_dom (m : World) →
  m ⊑ n →
  let_result_world_on X e x m Hfresh_m Hresult_m ⊑
    let_result_world_on X e x n Hfresh_n Hresult_n.
Proof.
  intros HXm Hle.
  unfold sqsubseteq, wf_world_sqsubseteq, raw_le.
  apply world_ext.
  - simpl.
    pose proof (raw_le_dom (m : World) (n : World) Hle) as Hdom.
    set_solver.
  - intros σx. simpl. split.
    + intros Hσx.
      destruct Hσx as [σm [vx [Hσm [Hsteps ->]]]].
      unfold sqsubseteq, wf_world_sqsubseteq, raw_le in Hle.
      rewrite Hle in Hσm.
      destruct Hσm as [σn [Hσn Hrestrict_m]].
      exists (<[x := vx]> σn). split.
      * exists σn, vx. repeat split; eauto.
        assert (HstoreX : store_restrict σn X = store_restrict σm X).
        {
          rewrite <- Hrestrict_m.
          store_norm.
          reflexivity.
        }
        rewrite HstoreX. exact Hsteps.
      * rewrite <- Hrestrict_m.
        apply (map_eq (M := gmap atom)). intros z.
        rewrite !store_restrict_lookup.
        destruct (decide (z ∈ world_dom (m : World) ∪ {[x]})) as [Hz|Hz].
        -- destruct (decide (z = x)) as [->|Hzx].
           ++ change ((<[x:=vx]> σn : Store) !! x =
                (<[x:=vx]> (store_restrict σn (world_dom (m : World))) : Store) !! x).
              rewrite !lookup_insert.
              rewrite !decide_True by reflexivity.
              reflexivity.
           ++ change ((<[x:=vx]> σn : Store) !! z =
                (<[x:=vx]> (store_restrict σn (world_dom (m : World))) : Store) !! z).
              rewrite !lookup_insert_ne by congruence.
              rewrite store_restrict_lookup.
              rewrite decide_True by set_solver.
              reflexivity.
        -- destruct (decide (z = x)) as [->|Hzx].
           ++ exfalso. apply Hz. set_solver.
           ++ change (None =
                (<[x:=vx]> (store_restrict σn (world_dom (m : World))) : Store) !! z).
              rewrite lookup_insert_ne by congruence.
              rewrite store_restrict_lookup.
              rewrite decide_False by set_solver.
              reflexivity.
    + intros Hσx.
      destruct Hσx as [σxn [Hσxn Hrestrict]].
      destruct Hσxn as [σn [vx [Hσn [Hsteps ->]]]].
      unfold sqsubseteq, wf_world_sqsubseteq, raw_le in Hle.
      assert (Hσm : (m : World) (store_restrict σn (world_dom (m : World)))).
      {
        pose proof (raw_le_dom (m : World) (n : World)
          ltac:(unfold sqsubseteq, wf_world_sqsubseteq, raw_le; exact Hle)) as Hdom_mn.
        rewrite Hle.
        exists σn. split; [exact Hσn |].
        simpl.
        replace (world_dom (n : World) ∩ world_dom (m : World))
          with (world_dom (m : World)) by set_solver.
        reflexivity.
      }
      exists (store_restrict σn (world_dom (m : World))), vx.
      split; [exact Hσm |].
      split.
      * assert (HstoreX :
          store_restrict (store_restrict σn (world_dom (m : World))) X =
          store_restrict σn X).
        {
          store_norm.
          reflexivity.
        }
        rewrite HstoreX. exact Hsteps.
      * rewrite <- Hrestrict.
        apply (map_eq (M := gmap atom)). intros z.
        rewrite !store_restrict_lookup.
        destruct (decide (z ∈ world_dom (m : World) ∪ {[x]})) as [Hz|Hz].
        -- destruct (decide (z = x)) as [->|Hzx].
           ++ change ((<[x:=vx]> σn : Store) !! x =
                (<[x:=vx]> (store_restrict σn (world_dom (m : World))) : Store) !! x).
              rewrite !lookup_insert.
              rewrite !decide_True by reflexivity.
              reflexivity.
           ++ change ((<[x:=vx]> σn : Store) !! z =
                (<[x:=vx]> (store_restrict σn (world_dom (m : World))) : Store) !! z).
              rewrite !lookup_insert_ne by congruence.
              rewrite store_restrict_lookup.
              rewrite decide_True by set_solver.
              reflexivity.
        -- destruct (decide (z = x)) as [->|Hzx].
           ++ exfalso. apply Hz. set_solver.
           ++ change (None =
                (<[x:=vx]> (store_restrict σn (world_dom (m : World))) : Store) !! z).
              rewrite lookup_insert_ne by congruence.
              rewrite store_restrict_lookup.
              rewrite decide_False by set_solver.
              reflexivity.
Qed.

Lemma let_result_world_on_base_mono_from_total
    X e x (m n : WfWorld)
    (Hfresh_m : x ∉ world_dom (m : World))
    (Hfresh_n : x ∉ world_dom (n : World))
    Hresult_m :
  ∀ (HXm : X ⊆ world_dom (m : World)) (Hle : m ⊑ n),
  let Hresult_n :=
    expr_total_results_on_le X e m n HXm Hle Hresult_m in
  let_result_world_on X e x m Hfresh_m Hresult_m ⊑
    let_result_world_on X e x n Hfresh_n Hresult_n.
Proof.
  intros HXm Hle.
  apply let_result_world_on_base_mono; assumption.
Qed.

Lemma let_result_world_on_preserves_context Σ Γ X e x (w : WfWorld) Hfresh Hresult :
  w ⊨ denot_ctx_in_env Σ Γ →
  let_result_world_on X e x w Hfresh Hresult ⊨ denot_ctx_in_env Σ Γ.
Proof.
  intros Hctx.
  eapply res_models_kripke.
  - apply let_result_world_on_le.
  - exact Hctx.
Qed.

Lemma let_result_world_on_erased_basic
    Σ Γ τ e x (m : WfWorld) Hfresh Hresult :
  choice_typing_wf Σ Γ e τ →
  m ⊨ denot_ctx_in_env Σ Γ →
  x ∉ dom (erase_ctx_under Σ Γ) →
  let_result_world_on (dom (erase_ctx_under Σ Γ)) e x m Hfresh Hresult ⊨
    basic_world_formula
      (erase_ctx_under Σ (CtxComma Γ (CtxBind x τ)))
      (dom (erase_ctx_under Σ (CtxComma Γ (CtxBind x τ)))).
Proof.
  intros Hwf Hm Hx.
  eapply res_models_atom_intro.
  - unfold formula_scoped_in_world, basic_world_formula, basic_world_lqual.
    simpl.
    rewrite erase_ctx_under_comma_bind_dom.
    intros z Hz. simpl.
    apply elem_of_union in Hz as [Hz|Hz].
    + rewrite dom_empty_L in Hz. set_solver.
    + change (z ∈ dom (erase_ctx_under Σ Γ) ∪ {[x]}) in Hz.
      apply elem_of_union in Hz as [Hzold|Hzx].
      * apply elem_of_union. left.
        pose proof (res_models_with_store_fuel_scoped
          (formula_measure (denot_ctx_in_env Σ Γ)) ∅ m
          (denot_ctx_in_env Σ Γ) Hm) as Hscope.
        unfold formula_scoped_in_world in Hscope.
        apply Hscope.
        apply elem_of_union. right.
        apply denot_ctx_in_env_dom_subset_formula_fv.
        destruct Hwf as [Hwfτ _].
        rewrite <- (basic_ctx_erase_dom (dom Σ) Γ
          (wf_ctx_under_basic Σ Γ (wf_choice_ty_under_ctx Σ Γ τ Hwfτ))).
        unfold erase_ctx_under in Hzold.
        rewrite dom_union_L in Hzold.
        exact Hzold.
      * apply elem_of_union. right. exact Hzx.
  - unfold logic_qualifier_denote, basic_world_lqual. simpl.
    rewrite erase_ctx_under_comma_bind_dom.
    split.
    + intros z Hz. simpl.
      apply elem_of_intersection. split; [| exact Hz].
      apply elem_of_union in Hz as [Hz|Hz].
      * apply elem_of_union. left.
        pose proof (res_models_with_store_fuel_scoped
          (formula_measure (denot_ctx_in_env Σ Γ)) ∅ m
          (denot_ctx_in_env Σ Γ) Hm) as Hscope.
        unfold formula_scoped_in_world in Hscope.
        apply Hscope.
        apply elem_of_union. right.
        apply denot_ctx_in_env_dom_subset_formula_fv.
        destruct Hwf as [Hwfτ _].
        rewrite <- (basic_ctx_erase_dom (dom Σ) Γ
          (wf_ctx_under_basic Σ Γ (wf_choice_ty_under_ctx Σ Γ τ Hwfτ))).
        unfold erase_ctx_under in Hz.
        rewrite dom_union_L in Hz.
        exact Hz.
      * apply elem_of_union. right. exact Hz.
    + intros σx Hσx.
      simpl in Hσx.
      destruct Hσx as [σfull [Hσfull Hrestrict_full]].
      destruct (let_result_world_on_elim
        (dom (erase_ctx_under Σ Γ)) e x m Hfresh Hresult σfull Hσfull)
        as [σ [vx [Hσ [Hsteps ->]]]].
      intros z T v Hz HΣext Hlookup.
      rewrite <- Hrestrict_full in Hlookup.
      apply store_restrict_lookup_some in Hlookup as [_ Hlookup].
      destruct (decide (z = x)) as [->|Hzx].
      * change ((<[x := vx]> σ : Store) !! x = Some v) in Hlookup.
        assert (Hins : (<[x := vx]> σ : Store) !! x = Some vx)
          by apply lookup_insert_eq.
        rewrite Hins in Hlookup.
        inversion Hlookup. subst v.
        assert (HT : T = erase_ty τ).
        {
          assert (HΣx :
            erase_ctx_under Σ (CtxComma Γ (CtxBind x τ)) !! x = Some (erase_ty τ)).
          {
            unfold erase_ctx_under. simpl.
            rewrite lookup_union_r.
            - rewrite lookup_union_r.
              + rewrite lookup_singleton. rewrite decide_True by reflexivity. reflexivity.
              + apply not_elem_of_dom. set_solver.
            - apply not_elem_of_dom.
              intros HxΣ. apply Hx.
              unfold erase_ctx_under. rewrite dom_union_L.
              apply elem_of_union. left. exact HxΣ.
          }
          rewrite HΣx in HΣext. inversion HΣext. reflexivity.
        }
        subst T.
        eapply choice_typing_wf_result_typed_restrict_in_ctx; eauto.
      * change ((<[x := vx]> σ : Store) !! z = Some v) in Hlookup.
        rewrite lookup_insert_ne in Hlookup by congruence.
        assert (Hzold : z ∈ dom (erase_ctx_under Σ Γ)) by set_solver.
        pose proof (basic_world_formula_store_restrict_typed
          (erase_ctx_under Σ Γ) (dom (erase_ctx_under Σ Γ)) m σ
          (denot_ctx_in_env_erased_basic Σ Γ m Hm) Hσ) as Htyped_old.
        assert (HΣold : erase_ctx_under Σ Γ !! z = Some T).
        {
          unfold erase_ctx_under in *. simpl in HΣext.
          rewrite lookup_union_Some_raw in HΣext.
          apply lookup_union_Some_raw.
          destruct HΣext as [HΣz | [HΣnone Hz_right]].
          - left. exact HΣz.
          - right. split; [exact HΣnone |].
            rewrite lookup_union_Some_raw in Hz_right.
            destruct Hz_right as [HΓz | [HΓnone Hsingle]].
            + exact HΓz.
            + rewrite lookup_singleton in Hsingle.
              destruct (decide (z = x)) as [->|Hne].
              * contradiction.
              * rewrite decide_False in Hsingle by congruence.
                discriminate.
        }
        eapply Htyped_old.
        -- exact Hzold.
        -- exact HΣold.
        -- apply store_restrict_lookup_some_2; [exact Hlookup | exact Hzold].
Qed.

(** Result-binding compatibility for the let-result world.

    If [m] satisfies [τ] for the expression [e], then the world obtained by
    adding a fresh coordinate [x] containing exactly the possible results of
    [e] satisfies [τ] for [return x].

    This is intentionally a denotation-level transport theorem, not a
    constructor-specific typing case.  The proof must not split into local
    [CTOver]/[CTUnder] cases for the caller.  If structural induction over
    [τ] is needed, it belongs in a generic expression-result transport lemma
    that this theorem instantiates.

    Anti-slip rule: this lemma is about replacing an expression by its fresh
    result representative.  It should be proved by a general
    expression-result transport principle for [denot_ty_on], not by rebuilding
    the proof separately for each type constructor. *)
Lemma denot_ty_on_let_result_representative
    X Σ τ e x (m : WfWorld) Hfresh Hresult :
  basic_choice_ty (dom Σ) τ →
  fv_tm e ⊆ X →
  x ∉ X ∪ fv_cty τ ∪ fv_tm e →
  m ⊨ basic_world_formula Σ (dom Σ) →
  m ⊨ denot_ty_on X Σ τ e →
  let_result_world_on X e x m Hfresh Hresult ⊨
    denot_ty_on (X ∪ {[x]}) (<[x := erase_ty τ]> Σ) τ (tret (vfvar x)).
Proof.
(** Open: this is the same missing transport principle in a specialized
    representative form.  It should follow from a repaired generic
    expression-result/denotation transport theorem, not from a constructor-by-
    constructor proof over [τ]. *)
Admitted.

Lemma let_result_world_on_bound_type
    Σ Γ τ e x (m : WfWorld) Hfresh Hresult :
  choice_typing_wf Σ Γ e τ →
  m ⊨ denot_ctx_in_env Σ Γ →
  m ⊨ denot_ty_in_ctx_under Σ Γ τ e →
  x ∉ dom (erase_ctx_under Σ Γ) ∪ fv_cty τ ∪ fv_tm e →
  let_result_world_on (dom (erase_ctx_under Σ Γ)) e x m Hfresh Hresult ⊨
    denot_ty_on
      (dom (erase_ctx_under Σ Γ) ∪ {[x]})
      (<[x := erase_ty τ]> (erase_ctx_under Σ Γ))
      τ (tret (vfvar x)).
Proof.
  intros Hwf Hm Hτ Hx.
  eapply (denot_ty_on_let_result_representative
    (dom (erase_ctx_under Σ Γ)) (erase_ctx_under Σ Γ) τ e x m Hfresh Hresult).
  - destruct Hwf as [Hwfτ _].
    pose proof (wf_choice_ty_under_basic Σ Γ τ Hwfτ) as Hbasicτ.
    replace (dom (erase_ctx_under Σ Γ)) with (dom Σ ∪ ctx_dom Γ).
    + exact Hbasicτ.
    + pose proof (wf_ctx_under_basic Σ Γ (wf_choice_ty_under_ctx Σ Γ τ Hwfτ))
        as Hctx.
      unfold erase_ctx_under.
      rewrite dom_union_L, (basic_ctx_erase_dom (dom Σ) Γ Hctx).
      reflexivity.
  - pose proof (choice_typing_wf_fv_tm_subset Σ Γ e τ Hwf) as Hfv.
    replace (dom (erase_ctx_under Σ Γ)) with (dom Σ ∪ ctx_dom Γ).
    + exact Hfv.
    + destruct Hwf as [Hwfτ _].
      pose proof (wf_ctx_under_basic Σ Γ (wf_choice_ty_under_ctx Σ Γ τ Hwfτ))
        as Hctx.
      unfold erase_ctx_under.
      rewrite dom_union_L, (basic_ctx_erase_dom (dom Σ) Γ Hctx).
      reflexivity.
  - exact Hx.
  - apply denot_ctx_in_env_erased_basic. exact Hm.
  - exact Hτ.
Qed.

Lemma let_result_world_on_denot_ctx_in_env
    Σ Γ τ e x (m : WfWorld) Hfresh Hresult :
  choice_typing_wf Σ Γ e τ →
  m ⊨ denot_ctx_in_env Σ Γ →
  m ⊨ denot_ty_in_ctx_under Σ Γ τ e →
  x ∉ dom (erase_ctx_under Σ Γ) ∪ fv_cty τ ∪ fv_tm e →
  let_result_world_on (dom (erase_ctx_under Σ Γ)) e x m Hfresh Hresult ⊨
    denot_ctx_in_env Σ (CtxComma Γ (CtxBind x τ)).
Proof.
  intros Hwf Hm Hτ Hx.
  unfold denot_ctx_in_env.
  apply res_models_and_intro_from_models.
  - eapply res_models_kripke.
    + apply let_result_world_on_le.
    + eapply denot_ctx_in_env_basic; eauto.
  - apply res_models_and_intro_from_models.
    + eapply let_result_world_on_erased_basic; eauto. set_solver.
    + apply denot_ctx_under_comma. split.
      * apply denot_ctx_in_env_ctx.
        eapply let_result_world_on_preserves_context; exact Hm.
      * simpl.
        unfold erase_ctx_under.
        eapply let_result_world_on_bound_type; eauto.
Qed.

Lemma let_result_world_on_bound_fresh
    Σ Γ τ e x (m : WfWorld) :
  choice_typing_wf Σ Γ e τ →
  m ⊨ denot_ctx_in_env Σ Γ →
  expr_total_on (dom (erase_ctx_under Σ Γ)) e m →
  x ∉ world_dom (m : World) →
  x ∉ dom (erase_ctx_under Σ Γ) ∪ fv_cty τ ∪ fv_tm e.
Proof.
  intros Hwf Hm Htotal Hfresh.
  destruct Htotal as [Hfv_e _].
  assert (Hfv_τ : fv_cty τ ⊆ dom (erase_ctx_under Σ Γ)).
  {
    destruct Hwf as [Hwfτ _].
    pose proof (wf_choice_ty_under_basic Σ Γ τ Hwfτ) as Hbasic.
    pose proof (basic_choice_ty_fv_subset (dom Σ ∪ ctx_dom Γ) τ Hbasic) as Hfv.
    replace (dom (erase_ctx_under Σ Γ)) with (dom Σ ∪ ctx_dom Γ).
    - exact Hfv.
    - pose proof (wf_ctx_under_basic Σ Γ (wf_choice_ty_under_ctx Σ Γ τ Hwfτ))
        as Hctx.
      unfold erase_ctx_under.
      rewrite dom_union_L, (basic_ctx_erase_dom (dom Σ) Γ Hctx).
      reflexivity.
  }
  assert (Hdom_world : dom (erase_ctx_under Σ Γ) ⊆ world_dom (m : World)).
  {
    pose proof (res_models_with_store_fuel_scoped
      (formula_measure (denot_ctx_in_env Σ Γ)) ∅ m
      (denot_ctx_in_env Σ Γ) Hm) as Hscope.
    unfold formula_scoped_in_world in Hscope.
    intros z Hz. apply Hscope.
    apply elem_of_union. right.
    apply denot_ctx_in_env_dom_subset_formula_fv.
    destruct Hwf as [Hwfτ _].
    replace (dom Σ ∪ ctx_dom Γ) with (dom (erase_ctx_under Σ Γ)).
    - exact Hz.
    - symmetry.
      pose proof (wf_ctx_under_basic Σ Γ (wf_choice_ty_under_ctx Σ Γ τ Hwfτ))
        as Hctx.
      unfold erase_ctx_under.
      rewrite dom_union_L, (basic_ctx_erase_dom (dom Σ) Γ Hctx).
      reflexivity.
  }
  apply not_elem_of_union. split.
  - apply not_elem_of_union. split.
    + intros Hbad. apply Hfresh. apply Hdom_world. exact Hbad.
    + intros Hbad. apply Hfresh. apply Hdom_world. apply Hfv_τ. exact Hbad.
  - intros Hbad. apply Hfresh. apply Hdom_world. apply Hfv_e. exact Hbad.
Qed.

Lemma let_result_world_on_le_store_elim
    X e x (n w : WfWorld) Hfresh Hresult σw :
  w ⊑ let_result_world_on X e x n Hfresh Hresult →
  X ∪ {[x]} ⊆ world_dom (w : World) →
  x ∉ X →
  (w : World) σw →
  ∃ σ vx,
    (n : World) σ ∧
    σw !! x = Some vx ∧
    store_restrict σw X = store_restrict σ X ∧
    subst_map (store_restrict σw X) e →* tret vx.
Proof.
  intros Hle Hscope HxX Hw.
  assert (Hw_raw := Hw).
  unfold sqsubseteq, wf_world_sqsubseteq, raw_le in Hle.
  rewrite Hle in Hw_raw. simpl in Hw_raw.
  destruct Hw_raw as [σwx [Hwx_store Hrestrict_w]].
  destruct (let_result_world_on_elim X e x n Hfresh Hresult
    _ Hwx_store) as [σ [vx [Hσ [Hsteps Hσwx_dom]]]].
  assert (Hstore_eq : store_restrict σw X = store_restrict σ X).
  {
    rewrite <- Hrestrict_w.
    rewrite !store_restrict_restrict.
    replace (world_dom (w : World) ∩ X) with X by set_solver.
    rewrite Hσwx_dom.
    change (store_restrict (<[x:=vx]> σ) X = store_restrict σ X).
    exact (store_restrict_insert_notin σ X x vx HxX).
  }
  exists σ, vx. repeat split; try exact Hσ.
  - assert (Hx_lookup_dom :
      σwx !! x =
      Some vx).
    {
      rewrite Hσwx_dom.
      rewrite lookup_insert. rewrite decide_True by reflexivity. reflexivity.
    }
    rewrite <- Hrestrict_w.
    apply store_restrict_lookup_some_2; [exact Hx_lookup_dom | set_solver].
  - exact Hstore_eq.
  - rewrite Hstore_eq. exact Hsteps.
Qed.

Lemma lc_env_restrict σ X :
  lc_env σ →
  lc_env (store_restrict σ X).
Proof.
  unfold lc_env. intros Hlc.
  apply map_Forall_lookup_2. intros y v Hlookup.
  apply store_restrict_lookup_some in Hlookup as [_ Hlookup].
  exact (map_Forall_lookup_1 _ _ _ _ Hlc Hlookup).
Qed.

Lemma difference_cons_decompose (X S : aset) (y : atom) :
  y ∈ X →
  y ∉ S →
  X ∖ S = (X ∖ ({[y]} ∪ S)) ∪ {[y]}.
Proof.
  intros HyX HyS.
  apply set_eq. intros z. split.
  - intros Hz.
    destruct (decide (z = y)) as [->|Hzy].
    + set_solver.
    + set_solver.
  - intros Hz. set_solver.
Qed.

Lemma fiber_projection_member_elim (w : WfWorld) X σ Hproj σw :
  (res_fiber_from_projection w X σ Hproj : World) σw →
  (w : World) σw ∧ store_restrict σw (dom σ) = σ.
Proof.
  unfold res_fiber_from_projection, res_fiber, raw_fiber.
  simpl. intros H. exact H.
Qed.

Lemma let_result_world_on_fiber_elim
    X e x (n : WfWorld) Hfresh Hresult ρ Hprojn Hprojlet σx :
  X ⊆ world_dom (n : World) →
  x ∉ X →
  (res_fiber_from_projection
    (let_result_world_on X e x n Hfresh Hresult) X ρ Hprojlet : World) σx →
  ∃ σ vx,
    (res_fiber_from_projection n X ρ Hprojn : World) σ ∧
    subst_map (store_restrict σ X) e →* tret vx ∧
    σx = <[x := vx]> σ.
Proof.
  intros _ HxX [Hσx Hσxρ].
  destruct (let_result_world_on_elim X e x n Hfresh Hresult σx Hσx)
    as [σ [vx [Hσ [Hsteps ->]]]].
  exists σ, vx. split.
  - simpl. split; [exact Hσ |].
    assert (Hdomρ : dom ρ ⊆ X).
    { destruct Hprojlet as [τ [_ Hτrestrict]].
      rewrite <- Hτrestrict. rewrite store_restrict_dom. set_solver. }
    assert (Hxdomρ : x ∉ dom ρ) by set_solver.
    assert (Hσρ : store_restrict σ (dom ρ) = ρ).
    {
      transitivity (store_restrict (<[x := vx]> σ) (dom ρ)).
      - symmetry. apply store_restrict_insert_notin. exact Hxdomρ.
      - exact Hσxρ.
    }
    exact Hσρ.
  - split; [exact Hsteps | reflexivity].
Qed.

Lemma let_result_world_on_fiber_intro
    X e x (n : WfWorld) Hfresh Hresult ρ Hprojn Hprojlet σ vx :
  X ⊆ world_dom (n : World) →
  x ∉ X →
  (res_fiber_from_projection n X ρ Hprojn : World) σ →
  subst_map (store_restrict σ X) e →* tret vx →
  (res_fiber_from_projection
    (let_result_world_on X e x n Hfresh Hresult) X ρ Hprojlet : World)
    (<[x := vx]> σ).
Proof.
  intros HXdom HxX Hσ Hsteps.
  destruct Hσ as [Hσn Hσρ].
  assert (Hdomρ : dom ρ = X).
  {
    destruct Hprojn as [σ0 [Hσ0 Hσ0ρ]].
    assert (Hρeq : ρ = store_restrict σ0 X) by (symmetry; exact Hσ0ρ).
    pose proof (wfworld_store_dom n σ0 Hσ0) as Hdomσ0.
    rewrite Hρeq.
    rewrite store_restrict_dom.
    set_solver.
  }
  apply res_fiber_from_projection_member.
  - apply let_result_world_on_member; [exact Hσn | exact Hsteps].
  - rewrite store_restrict_insert_notin by exact HxX.
    rewrite <- Hdomρ. exact Hσρ.
Qed.

Lemma expr_total_on_tlete_from_open
    (X : aset) e1 e2 x (m : WfWorld) Hfresh Hresult :
  x ∉ X →
  x ∉ fv_tm e2 →
  (∀ σ, (m : World) σ → closed_env (store_restrict σ X)) →
  (∀ σ, (m : World) σ → lc_env (store_restrict σ X)) →
  (∀ σ vx,
    (m : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    stale vx = ∅ ∧ is_lc vx) →
  (∀ σ, (m : World) σ → body_tm (subst_map (store_restrict σ X) e2)) →
  expr_total_on (X ∪ {[x]}) (e2 ^^ x)
    (let_result_world_on X e1 x m Hfresh Hresult) →
  fv_tm (tlete e1 e2) ⊆ X →
  expr_total_on X (tlete e1 e2) m.
Proof.
  intros HxX Hxe2 Hclosed Hlc Hresult_closed Hbody Hbody_total Hfv.
  split; [exact Hfv |].
  intros σ Hσ.
  destruct (Hresult σ Hσ) as [vx Hsteps1].
  pose proof (let_result_world_on_member X e1 x m Hfresh Hresult
    σ vx Hσ Hsteps1) as Hσx.
  destruct Hbody_total as [_ Hbody_total].
  specialize (Hbody_total (<[x := vx]> σ) Hσx) as [v Hsteps2].
  exists v.
  change (subst_map (store_restrict σ X) (tlete e1 e2))
    with (m{store_restrict σ X} (tlete e1 e2)).
  rewrite (msubst_lete (store_restrict σ X) e1 e2).
  eapply reduction_lete_intro.
  - apply Hbody. exact Hσ.
  - exact Hsteps1.
  - rewrite store_restrict_insert_fresh_union in Hsteps2.
    2:{
      eapply store_lookup_none_of_dom.
      + apply wfworld_store_dom. exact Hσ.
      + exact Hfresh.
    }
    2:{ exact HxX. }
    eapply (steps_msubst_open_body_result X σ e2 x vx v).
    + exact HxX.
    + exact Hxe2.
    + apply Hclosed. exact Hσ.
    + apply (proj1 (Hresult_closed σ vx Hσ Hsteps1)).
    + apply (proj2 (Hresult_closed σ vx Hσ Hsteps1)).
    + apply Hlc. exact Hσ.
    + exact Hsteps2.
Qed.

Lemma expr_result_value_tlete_from_body_projection
    X e1 e2 x σ vx v :
  x ∉ X →
  x ∉ fv_tm e2 →
  closed_env (store_restrict σ X) →
  lc_env (store_restrict σ X) →
  stale vx = ∅ →
  is_lc vx →
  body_tm (subst_map (store_restrict σ X) e2) →
  subst_map (store_restrict σ X) e1 →* tret vx →
  subst_map (<[x := vx]> (store_restrict σ X)) (e2 ^^ x) →* tret v →
  subst_map (store_restrict σ X) (tlete e1 e2) →* tret v.
Proof.
  intros HxX Hxe2 Hclosed Hlc Hvx_closed Hvx_lc Hbody He1 Hbody_steps.
  change (subst_map (store_restrict σ X) (tlete e1 e2))
    with (m{store_restrict σ X} (tlete e1 e2)).
  rewrite (msubst_lete (store_restrict σ X) e1 e2).
  eapply reduction_lete_intro; [exact Hbody | exact He1 |].
  eapply (steps_msubst_open_body_result X σ e2 x vx v); eauto.
Qed.

Lemma expr_result_value_tlete_from_body_store
    X e1 e2 x ν σ vx v :
  x ∉ X →
  x ∉ fv_tm e2 →
  closed_env (store_restrict σ X) →
  lc_env (store_restrict σ X) →
  stale vx = ∅ →
  is_lc vx →
  body_tm (subst_map (store_restrict σ X) e2) →
  subst_map (store_restrict σ X) e1 →* tret vx →
  expr_result_store ν (subst_map (<[x := vx]> (store_restrict σ X)) (e2 ^^ x)) {[ν := v]} →
  expr_result_store ν (subst_map (store_restrict σ X) (tlete e1 e2)) {[ν := v]}.
Proof.
  intros HxX Hxe2 Hclosed Hlc Hvx_closed Hvx_lc Hbody He1 Hstore.
  destruct Hstore as [v' [Hσ [Hv_closed [Hv_lc Hbody_steps]]]].
  assert (Hv_eq : v' = v).
  {
    assert (Hlookup : ({[ν := v']} : Store) !! ν = Some v).
    {
      rewrite <- Hσ.
      rewrite lookup_singleton. rewrite decide_True by reflexivity.
      reflexivity.
    }
    rewrite lookup_singleton in Hlookup.
    rewrite decide_True in Hlookup by reflexivity.
    inversion Hlookup. reflexivity.
  }
  subst v'.
  exists v. repeat split; try reflexivity; try exact Hv_closed; try exact Hv_lc.
  unfold expr_result_value.
  eapply (expr_result_value_tlete_from_body_projection X e1 e2 x σ vx v); eauto.
Qed.

Lemma expr_result_in_store_ret_fvar_to_source
    ρ e x ν σ vx σν :
  stale vx = ∅ →
  ν ≠ x →
  σ !! x = None →
  subst_map σ (subst_map ρ e) →* tret vx →
  expr_result_in_store ∅ (tret (vfvar x)) ν σν →
  store_restrict (<[x := vx]> σ) ({[x]} ∪ {[ν]}) = σν →
  expr_result_in_store ρ e ν σ.
Proof.
  intros _ _ _ _ Hret _.
  destruct (expr_result_store_elim ν (subst_map ∅ (tret (vfvar x))) σν Hret)
    as [v [-> [Hv_stale [_ Hsteps]]]].
  simpl in Hsteps.
  pose proof (value_steps_self (vfvar x) (tret v) Hsteps) as Heq.
  inversion Heq. subst v.
  simpl in Hv_stale. set_solver.
Qed.

Lemma expr_result_in_store_ret_fvar_to_source_restrict
    e x ν σ vx σν :
  let S := stale e ∪ {[ν]} in
  stale vx = ∅ →
  ν ≠ x →
  x ∉ S →
  closed_env (store_restrict σ S) →
  σ !! x = None →
  subst_map σ e →* tret vx →
  expr_result_in_store ∅ (tret (vfvar x)) ν σν →
  store_restrict (<[x := vx]> σ) ({[x]} ∪ {[ν]}) = σν →
  expr_result_in_store ∅ e ν (store_restrict σ S).
Proof.
  intros S Hvx Hνx HxS Hclosed Hxnone Hsteps_e Hret Hrestrict.
  destruct (expr_result_store_elim ν (subst_map ∅ (tret (vfvar x))) σν Hret)
    as [v [-> [Hv_stale [_ Hsteps]]]].
  simpl in Hsteps.
  pose proof (value_steps_self (vfvar x) (tret v) Hsteps) as Heq.
  inversion Heq. subst v.
  simpl in Hv_stale. set_solver.
Qed.

Lemma closed_env_restrict_insert_result σ S ν vx :
  closed_env (store_restrict σ (S ∖ {[ν]})) →
  σ !! ν = Some vx →
  stale vx = ∅ →
  closed_env (store_restrict σ S).
Proof.
  intros Hclosed Hν Hvx.
  unfold closed_env in *.
  apply map_Forall_lookup_2. intros z v Hz.
  apply store_restrict_lookup_some in Hz as [HzS Hzσ].
  destruct (decide (z = ν)) as [->|Hzν].
  - rewrite Hν in Hzσ. inversion Hzσ. subst. exact Hvx.
  - apply (map_Forall_lookup_1 _ _ z v Hclosed).
    apply store_restrict_lookup_some_2; [exact Hzσ | set_solver].
Qed.

Lemma expr_result_in_world_ret_fvar_to_source_pullback
    e x ν (n p : WfWorld) Hle :
  ν ≠ x →
  x ∉ stale e ∪ {[ν]} →
  {[x]} ∪ {[ν]} ⊆ world_dom (p : World) →
  (∀ σx,
    (n : World) σx →
    ∃ σ vx,
      σx = <[x := vx]> σ ∧
      σ !! x = None ∧
      subst_map σ e →* tret vx) →
  (∀ σ vx,
    (n : World) (<[x := vx]> σ) →
    subst_map σ e →* tret vx →
    closed_env (store_restrict σ ((stale e ∪ {[ν]}) ∖ {[ν]}))) →
  (∀ σ vx,
    (n : World) (<[x := vx]> σ) →
    subst_map σ e →* tret vx →
    stale vx = ∅) →
  expr_result_in_world ∅ (tret (vfvar x)) ν
    (res_restrict p ({[x]} ∪ {[ν]})) →
  expr_result_in_world ∅ e ν
    (res_restrict (res_pullback_projection n p Hle) (stale e ∪ {[ν]})).
Proof.
  intros _ _ Hscope _ _ _ Hret_world.
  exfalso.
  destruct (world_wf p) as [[σp Hσp] _].
  set (σxν := store_restrict σp ({[x]} ∪ {[ν]})).
  assert (Hproj_xν : (res_restrict p ({[x]} ∪ {[ν]}) : World) σxν).
  { exists σp. split; [exact Hσp | reflexivity]. }
  set (σν := store_restrict σp {[ν]}).
  assert (Hproj_ν :
    (res_restrict (res_restrict p ({[x]} ∪ {[ν]})) {[ν]} : World) σν).
  {
    exists σxν. split; [exact Hproj_xν |].
    subst σxν σν.
    rewrite store_restrict_restrict.
    replace (({[x]} ∪ {[ν]}) ∩ {[ν]}) with ({[ν]} : aset) by set_solver.
    reflexivity.
  }
  pose proof (expr_result_in_world_sound ∅ (tret (vfvar x)) ν
    (res_restrict p ({[x]} ∪ {[ν]})) σν Hret_world Hproj_ν) as Hret.
  destruct (expr_result_store_elim ν (subst_map ∅ (tret (vfvar x))) σν Hret)
    as [v [-> [Hv_stale [_ Hsteps]]]].
  simpl in Hsteps.
  pose proof (value_steps_self (vfvar x) (tret v) Hsteps) as Heq.
  inversion Heq. subst v.
  simpl in Hv_stale. set_solver.
Qed.

(** Semantic compatibility of bunched let.

    This is the remaining tlet-specific denotation theorem.  Its proof should
    combine:
    - [expr_result_in_world_let_intro]/[_elim] for operational composition;
    - [choice_typing_wf_result_closed_in_ctx] for closed intermediate values;
    - the body entailment under [CtxComma Γ (CtxBind x τ1)].

    Keeping this theorem separate prevents the fundamental theorem case from
    doing any recursion on [τ2]. *)
