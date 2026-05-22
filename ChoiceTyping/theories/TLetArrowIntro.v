(** * ChoiceTyping.TLetArrowIntro

    A narrow proof workbench for the [CTArrow] case of the one-way [tlet]
    denotation intro lemma.

    The proof below deliberately keeps the Arrow formula inline.  The temporary
    holes are stated as reusable LN / environment / model-transport lemmas, not
    as lemmas about the particular shape of the Arrow body. *)

From Stdlib Require Import Logic.PropExtensionality
  Logic.FunctionalExtensionality.
From CoreLang Require Import Instantiation InstantiationProps BasicTypingProps
  Sugar.
From ChoiceLogic Require Import FormulaDerived FormulaWorldExtension.
From ChoiceTyping Require Import Auxiliary ResultWorldExtension.
From ChoiceType Require Import BasicStore BasicTyping DenotationNotation
  LocallyNamelessProps TypeDenotation.Denotation TypeDenotation.FormulaEquiv.

Import Tactics.

Local Definition tlet_intro_ih_sigma
    (gas : nat) (τ : choice_ty) : Prop :=
  ∀ (Δ : gmap atom ty) (T1 : ty) (e1 e2 : tm)
    (m mx : WfWorld) Fx (x : atom),
    result_extends e1 x m Fx mx ->
    Δ ⊢ₑ e1 ⋮ T1 ->
    world_dom (m : World) = dom Δ ->
    world_closed_on (dom Δ) m ->
    x ∉ dom Δ ->
    basic_choice_ty (dom Δ) τ ->
    cty_parametric τ ->
    Δ ⊢ₑ tlete e1 e2 ⋮ erase_ty τ ->
    mx ⊨ denot_ty_lvar_gas gas
      (atom_env_to_lty_env (<[x := T1]> Δ)) τ (e2 ^^ x) ->
    m ⊨ denot_ty_lvar_gas gas
      (atom_env_to_lty_env Δ) τ (tlete e1 e2) ∧
    expr_total_on (tlete e1 e2) m.

(** The Arrow body transport: [m #> Fx ~~> mx] plus the source forall on [mx]
    gives the target forall on [m]. *)
Local Lemma tlet_arrow_forall_intro_sigma
    (gas : nat) (Δ : gmap atom ty) (T1 : ty)
    (e1 e2 : tm) (m mx : WfWorld) Fx
    (x : atom) (τx τ : choice_ty) :
  (∀ τ, tlet_intro_ih_sigma gas τ) ->
  result_extends e1 x m Fx mx ->
  Δ ⊢ₑ e1 ⋮ T1 ->
  world_dom (m : World) = dom Δ ->
  world_closed_on (dom Δ) m ->
  expr_total_on (tlete e1 e2) m ->
  x ∉ dom Δ ->
  basic_choice_ty (dom Δ) (CTArrow τx τ) ->
  cty_parametric (CTArrow τx τ) ->
  Δ ⊢ₑ tlete e1 e2 ⋮ erase_ty (CTArrow τx τ) ->
  mx ⊨ FForallTypedBind
    (atom_env_to_lty_env (<[x := T1]> Δ)) (erase_ty τx)
    (fun Σx =>
      FImpl
        (denot_ty_lvar_gas gas Σx (↑[0] τx) (tret (vbvar 0)))
        (denot_ty_lvar_gas gas Σx τ
          (tapp_tm (↑[0] (e2 ^^ x)) (vbvar 0)))) ->
  m ⊨ FForallTypedBind
    (atom_env_to_lty_env Δ) (erase_ty τx)
    (fun Σx =>
      FImpl
        (denot_ty_lvar_gas gas Σx (↑[0] τx) (tret (vbvar 0)))
        (denot_ty_lvar_gas gas Σx τ
          (tapp_tm (↑[0] (tlete e1 e2)) (vbvar 0)))).
Proof.
  intros IHgas Hext He1 Hdom Hclosed Htotal Hx Hbasic Hparam Hlet Hsource.
  destruct Hparam as [Hparamτx Hparamτ].
  set (L0 := world_dom (mx : World) ∪ dom Δ ∪ {[x]}
      ∪ fv_tm e1 ∪ fv_tm e2 ∪ fv_cty τx ∪ fv_cty τ).
  destruct (basic_choice_ty_open_arrow_body_cofinite
    Δ τx τ L0 Hbasic) as [Lbody [HL0 Hbody_basic]].
  unfold FForallTypedBind in Hsource |- *.
  eapply (res_models_forall_extend_input_widen m mx Fx
    (FForallTypedBody (atom_env_to_lty_env Δ) (erase_ty τx)
      (fun Σy =>
        FImpl
          (denot_ty_lvar_gas gas Σy (↑[0] τx) (tret (vbvar 0)))
          (denot_ty_lvar_gas gas Σy τ
            (tapp_tm (↑[0] (tlete e1 e2)) (vbvar 0)))))
    (FForallTypedBody (atom_env_to_lty_env (<[x := T1]> Δ)) (erase_ty τx)
      (fun Σy =>
        FImpl
          (denot_ty_lvar_gas gas Σy (↑[0] τx) (tret (vbvar 0)))
          (denot_ty_lvar_gas gas Σy τ
            (tapp_tm (↑[0] (e2 ^^ x)) (vbvar 0)))))).
  - apply formula_scoped_in_world_from_formula_fv.
    pose proof (basic_choice_ty_fv_subset _ _ Hbasic) as Hfv.
    inversion Hbasic; subst.
    pose proof (tlet_arrow_inline_forall_body_fv_subset
      gas Δ τx τ (tlete e1 e2) ltac:(eauto) ltac:(set_solver)) as Hbody_fv.
    rewrite Hdom. exact Hbody_fv.
  - exact (result_extends_by _ _ _ _ _ Hext).
  - exact Hsource.
  - exists Lbody.
    split; [set_solver |].
    intros y Fy my ny Hy HShapeFy HmFy HmyFx Hsource_open.
    assert (Hy0 : y ∉ L0) by set_solver.
    subst L0.
    rewrite !not_elem_of_union in Hy0.
    destruct Hy0 as [[[[[[Hy_mx HyΔ] Hyx] Hye1] Hye2] Hyτx] Hyτ].
    assert (Hy_ne_x : x <> y).
    { intros ->. apply Hyx. set_solver. }
    assert (Hext_y : ∃ Fx', result_extends e1 x my Fx' ny).
    {
      eapply result_extends_widen_after_forall; eauto.
      eapply basic_typing_contains_fv_tm. exact He1.
    }
    destruct Hext_y as [Fx_y Hext_y].
    unfold FForallTypedBody in Hsource_open |- *.
    rewrite !formula_open_impl in Hsource_open |- *.
    eapply res_models_impl_intro.
    + apply formula_scoped_in_world_from_formula_fv.
      cbn [formula_fv].
      pose proof (formula_fv_open_FClosedResourceIn_typed_bind_atom_env
        Δ (erase_ty τx) y HyΔ) as Hclosed_fv.
      rewrite Hclosed_fv.
      pose proof (basic_choice_ty_fv_subset _ _ Hbasic) as Hfv.
      inversion Hbasic; subst.
      pose proof (tlet_arrow_inline_impl_fv_subset
        gas Δ τx τ (tlete e1 e2) ltac:(eauto) ltac:(set_solver))
        as Himpl_fv.
      pose proof (formula_open_fv_subset_env 0 y
        (FImpl
          (denot_ty_lvar_gas gas
            (typed_lty_env_bind (atom_env_to_lty_env Δ) (erase_ty τx))
            (↑[0] τx) (tret (vbvar 0)))
          (denot_ty_lvar_gas gas
            (typed_lty_env_bind (atom_env_to_lty_env Δ) (erase_ty τx))
            τ (tapp_tm (↑[0] (tlete e1 e2)) (vbvar 0))))
        (dom Δ) Himpl_fv) as Hopen_impl_fv.
      pose proof (world_dom_forall_extension
        Δ (erase_ty τx) y m my Fy HyΔ HShapeFy HmFy Hdom) as Hdom_my.
      rewrite Hdom_my, dom_insert_L.
      clear - Hopen_impl_fv. set_solver.
    + intros Hclosed_target.
      assert (Hclosed_source :
        ny ⊨ formula_open 0 y
          (FClosedResourceIn
            (typed_lty_env_bind
              (atom_env_to_lty_env (<[x := T1]> Δ)) (erase_ty τx)))).
      {
        assert (Hdom_my :
          world_dom (my : World) = dom (<[y := erase_ty τx]> Δ)).
        { eapply world_dom_forall_extension; eauto. }
        assert (Hclosed_my :
          world_closed_on (dom (<[y := erase_ty τx]> Δ)) my).
        { eapply world_closed_on_forall_extension; eauto. }
        assert (Hlet_y :
          (<[y := erase_ty τx]> Δ) ⊢ₑ
            tlete e1 (tapp_tm e2 (vfvar y)) ⋮ erase_ty ({0 ~> y} τ)).
        { eapply basic_typing_tlet_tapp_fvar_open_arrow_body; eauto. }
        assert (Htotal_e1_m : expr_total_on e1 m).
        {
          eapply (expr_total_on_tlete_elim_e1_strong (dom Δ)); eauto.
          - eapply basic_typing_contains_fv_tm. exact Hlet.
        }
        assert (Htotal_e1_my : expr_total_on e1 my).
        {
          destruct Htotal_e1_m as [Hfv_e1 Hsteps_e1].
          split.
          - pose proof (res_extend_by_dom _ _ _ HmFy) as Hdom_my_ext.
            rewrite Hdom_my_ext.
            destruct HShapeFy as [_ HFy_out_tmp].
            rewrite HFy_out_tmp.
            rewrite Hdom.
            set_solver.
          - eapply result_witness_lift_extend; eauto.
        }
        eapply (closed_resource_typed_bind_insert_result_atom_env
          Δ e1 x y T1 (erase_ty τx) my ny Fx_y).
        - exact Hy_ne_x.
        - exact Hx.
        - exact HyΔ.
        - exact Hext_y.
        - eapply basic_typing_weaken_insert_tm; eauto.
        - exact Hdom_my.
        - exact Hclosed_my.
        - exact Htotal_e1_my.
      }
      assert (Hsource_inner :
        ny ⊨ formula_open 0 y
          (FImpl
            (denot_ty_lvar_gas gas
              (typed_lty_env_bind
                (atom_env_to_lty_env (<[x := T1]> Δ)) (erase_ty τx))
              (↑[0] τx) (tret (vbvar 0)))
            (denot_ty_lvar_gas gas
              (typed_lty_env_bind
                (atom_env_to_lty_env (<[x := T1]> Δ)) (erase_ty τx))
              τ (tapp_tm (↑[0] (e2 ^^ x)) (vbvar 0))))).
      {
        eapply res_models_impl_elim; eauto.
      }
      eapply res_models_impl_intro.
      * apply formula_scoped_in_world_from_formula_fv.
        pose proof (basic_choice_ty_fv_subset _ _ Hbasic) as Hfv.
        inversion Hbasic; subst.
        pose proof (tlet_arrow_inline_impl_fv_subset
          gas Δ τx τ (tlete e1 e2) ltac:(eauto) ltac:(set_solver))
          as Himpl_fv.
        pose proof (formula_open_fv_subset_env 0 y
          (FImpl
            (denot_ty_lvar_gas gas
              (typed_lty_env_bind (atom_env_to_lty_env Δ) (erase_ty τx))
              (↑[0] τx) (tret (vbvar 0)))
            (denot_ty_lvar_gas gas
              (typed_lty_env_bind (atom_env_to_lty_env Δ) (erase_ty τx))
              τ (tapp_tm (↑[0] (tlete e1 e2)) (vbvar 0))))
          (dom Δ) Himpl_fv) as Hopen_fv.
        pose proof (world_dom_forall_extension
          Δ (erase_ty τx) y m my Fy HyΔ HShapeFy HmFy Hdom) as Hdom_my.
        rewrite Hdom_my, dom_insert_L.
        clear - Hopen_fv. set_solver.
      * intros Harg_target.
        assert (Harg_target_ny :
          ny ⊨ formula_open 0 y
            (denot_ty_lvar_gas gas
              (typed_lty_env_bind (atom_env_to_lty_env Δ) (erase_ty τx))
              (↑[0] τx) (tret (vbvar 0)))).
        {
          eapply res_models_kripke.
          - eapply res_extend_by_le_base. exact HmyFx.
          - exact Harg_target.
        }
        assert (Harg_atom_target :
          ny ⊨ denot_ty_lvar_gas gas
            (atom_env_to_lty_env (<[y := erase_ty τx]> Δ))
            τx (tret (vfvar y))).
        {
          eapply denot_ty_lvar_gas_opened_arrow_arg_to_atom_env; eauto.
          inversion Hbasic; subst; eauto.
        }
        assert (Harg_atom_source :
          ny ⊨ denot_ty_lvar_gas gas
            (atom_env_to_lty_env (<[x := T1]> (<[y := erase_ty τx]> Δ)))
            τx (tret (vfvar y))).
        {
          eapply denot_ty_lvar_gas_insert_fresh_atom_env; eauto.
          - pose proof (basic_choice_ty_fv_subset _ _ Hbasic) as Hfv.
            cbn [fv_cty fv_tm fv_value] in Hfv |- *.
            rewrite dom_insert_L. set_solver.
          - rewrite formula_open_FClosedResourceIn in Hclosed_source.
            rewrite lty_env_open_typed_bind_atom_env in Hclosed_source.
            2:{ rewrite dom_insert_L. set_solver. }
            assert (<[y := erase_ty τx]> (<[x := T1]> Δ) =
                    <[x := T1]> (<[y := erase_ty τx]> Δ)) as Hperm_xy.
            {
              apply map_eq. intros z.
              rewrite !lookup_insert.
              repeat case_decide; subst; try congruence; reflexivity.
            }
            rewrite <- Hperm_xy.
            exact Hclosed_source.
        }
        assert (Harg_atom_source_commuted :
          ny ⊨ denot_ty_lvar_gas gas
            (atom_env_to_lty_env (<[y := erase_ty τx]> (<[x := T1]> Δ)))
            τx (tret (vfvar y))).
        {
          eapply denot_ty_lvar_gas_atom_env_permute; eauto.
        }
        assert (Harg_source :
          ny ⊨ formula_open 0 y
            (denot_ty_lvar_gas gas
              (typed_lty_env_bind
                (atom_env_to_lty_env (<[x := T1]> Δ)) (erase_ty τx))
              (↑[0] τx) (tret (vbvar 0)))).
        {
          eapply denot_ty_lvar_gas_atom_env_to_opened_arrow_arg; eauto.
          - set_solver.
          - (* [τx] remains basic after adding the fresh [x] binding. *)
            inversion Hbasic; subst.
            eapply basic_choice_ty_mono; [| eauto].
            rewrite dom_insert_L. set_solver.
        }
        assert (Hconseq_source_open :
          ny ⊨ formula_open 0 y
            (denot_ty_lvar_gas gas
              (typed_lty_env_bind
                (atom_env_to_lty_env (<[x := T1]> Δ)) (erase_ty τx))
              τ (tapp_tm (↑[0] (e2 ^^ x)) (vbvar 0)))).
        {
          eapply res_models_impl_elim; eauto.
        }
        assert (Hconseq_source_atom :
          ny ⊨ denot_ty_lvar_gas gas
            (atom_env_to_lty_env (<[y := erase_ty τx]> (<[x := T1]> Δ)))
            ({0 ~> y} τ) (tapp_tm (e2 ^^ x) (vfvar y))).
        {
          eapply denot_ty_lvar_gas_opened_arrow_conseq_to_atom_env; eauto.
          - set_solver.
          - (* [e2 ^^ x] is lc from the typing of [tlete e1 e2]. *)
            pose proof (typing_tm_lc _ _ _ Hlet) as Hlc_let.
            apply lc_lete_iff_body in Hlc_let as [_ Hbody].
            apply body_open_tm; [exact Hbody | constructor].
        }
        assert (Hconseq_source_for_ih :
          ny ⊨ denot_ty_lvar_gas gas
            (atom_env_to_lty_env (<[x := T1]> (<[y := erase_ty τx]> Δ)))
            ({0 ~> y} τ) ((tapp_tm e2 (vfvar y)) ^^ x)).
        {
          rewrite open_tapp_tm_fvar.
          eapply denot_ty_lvar_gas_atom_env_permute; eauto.
        }
        assert (Hconseq_target_atom :
          my ⊨ denot_ty_lvar_gas gas
            (atom_env_to_lty_env (<[y := erase_ty τx]> Δ))
            ({0 ~> y} τ) (tapp_tm (tlete e1 e2) (vfvar y))).
        {
          pose proof (IHgas ({0 ~> y} τ)) as IHτy.
          rewrite tapp_tm_tlete_fvar.
          assert (Hih_model :
            my ⊨ denot_ty_lvar_gas gas
              (atom_env_to_lty_env (<[y := erase_ty τx]> Δ))
              ({0 ~> y} τ)
              (tlete e1 (tapp_tm e2 (vfvar y))) ∧
            expr_total_on (tlete e1 (tapp_tm e2 (vfvar y))) my).
          {
            eapply (IHτy (<[y := erase_ty τx]> Δ) T1 e1
              (tapp_tm e2 (vfvar y)) my ny Fx_y x).
            - exact Hext_y.
            - eapply basic_typing_weaken_insert_tm; eauto.
            - eapply world_dom_forall_extension; eauto.
            - eapply world_closed_on_forall_extension; eauto.
            - apply not_elem_of_dom.
              rewrite lookup_insert_ne by congruence.
              apply not_elem_of_dom. exact Hx.
            - apply Hbody_basic. exact Hy.
            - apply cty_parametric_open. exact Hparamτ.
            - eapply basic_typing_tlet_tapp_fvar_open_arrow_body; eauto.
            - exact Hconseq_source_for_ih.
          }
          exact (proj1 Hih_model).
        }
        eapply denot_ty_lvar_gas_atom_env_to_opened_arrow_conseq; eauto.
        (* [tlete e1 e2] is lc from [Hlet]. *)
        eapply typing_tm_lc. exact Hlet.
Qed.

Lemma denot_ty_tlet_intro_on_ext_arrow_case
    (Δ : gmap atom ty) (T1 : ty) (e1 e2 : tm)
    (m mx : WfWorld) Fx (x : atom) (τx τ : choice_ty) :
  (∀ τ0, tlet_intro_ih_sigma
    (Nat.max (cty_depth τx) (cty_depth τ)) τ0) ->
  result_extends e1 x m Fx mx ->
  Δ ⊢ₑ e1 ⋮ T1 ->
  world_dom (m : World) = dom Δ ->
  world_closed_on (dom Δ) m ->
  expr_total_on (tlete e1 e2) m ->
  x ∉ dom Δ ->
  basic_choice_ty (dom Δ) (CTArrow τx τ) ->
  cty_parametric (CTArrow τx τ) ->
  Δ ⊢ₑ tlete e1 e2 ⋮ erase_ty (CTArrow τx τ) ->
  mx ⊨ denot_ty_on (<[x := T1]> Δ) (CTArrow τx τ) (e2 ^^ x) ->
  m ⊨ denot_ty_on Δ (CTArrow τx τ) (tlete e1 e2).
Proof.
  intros IHgas Hext He1 Hdom Hclosed Htotal Hx Hbasic Hparam Hlet Hsource.
  unfold denot_ty_on, denot_ty_lvar in *.
  cbn [cty_depth denot_ty_lvar_gas] in *.
  apply res_models_and_intro_from_models.
  - eapply FDenotObligationIn_intro_atom_env; eauto.
  - unfold tlet_intro_ih_sigma in *.
    eapply tlet_arrow_forall_intro_sigma; eauto.
    eapply res_models_and_elim_r. exact Hsource.
Qed.
