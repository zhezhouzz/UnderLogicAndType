(** * ChoiceTyping.TLetReduction

    Type-denotation reduction lemmas for the [tlet] soundness case.
    The final semantic bridge stays in [TLetDenotation]. *)

From CoreLang Require Import Instantiation InstantiationProps BasicTypingProps Sugar.
From ChoiceLogic Require Export FormulaDerived FormulaWorldExtension.
From ChoiceTyping Require Export TLetExprCont RegularDenotation.
From ChoiceTyping Require Import Naming SoundnessCommon
  ResultWorldClosed ResultWorldExprCont ResultWorldExtension.
From ChoiceType Require Import BasicStore DenotationNotation.

Import Tactics.

Local Lemma basic_typing_tlet_tapp_fvar
    (Δ : gmap atom ty) e1 e2 y Tx T :
  y ∉ dom Δ →
  Δ ⊢ₑ tlete e1 e2 ⋮ (Tx →ₜ T) →
  <[y := Tx]> Δ ⊢ₑ tlete e1 (tapp_tm e2 (vfvar y)) ⋮ T.
Proof.
  intros Hy Htyped.
  rewrite <- tapp_tm_tlete_fvar.
  eapply basic_typing_tapp_tm_fvar_insert; eauto.
Qed.

Local Lemma basic_choice_body_insert
    (Δ : gmap atom ty) y Ty τ (L : aset) :
  (∀ z, z ∉ L → basic_choice_ty (dom Δ ∪ {[z]}) ({0 ~> z} τ)) →
  y ∉ L →
  basic_choice_ty (dom (<[y := Ty]> Δ)) ({0 ~> y} τ).
Proof.
  intros Hbody Hy.
  rewrite dom_insert_L.
  replace ({[y]} ∪ dom Δ) with (dom Δ ∪ {[y]}) by set_solver.
  eauto.
Qed.

Local Ltac tlet_regular :=
  eauto 6 using basic_typing_contains_fv_tm, typing_tm_lc.

Local Lemma denot_ty_on_insert_env_fv_base
    (Δ : gmap atom ty) T x τ e :
  dom Δ ⊆ formula_fv (denot_ty_on (<[x := T]> Δ) τ e).
Proof.
  transitivity (dom (<[x := T]> Δ)).
  - rewrite dom_insert_L. set_solver.
  - apply denot_ty_on_env_fv_subset.
Qed.

Local Lemma fresh_not_in_qual_vars
    (Δ : gmap atom ty) (x : atom) (T : ty) φ :
  x ∉ dom Δ →
  basic_qualifier_body (dom Δ) φ →
  x ∉ dom Δ ∪ lvars_fv (qual_vars φ).
Proof.
  intros Hx Hbasic.
  pose proof (basic_qualifier_body_fv_subset _ _ Hbasic) as Hfv.
  destruct φ; cbn [qual_dom qual_vars] in *.
  set_solver.
Qed.

Local Lemma denot_base_post_fv_insert
    (Δ : gmap atom ty) x T b φ :
  basic_qualifier_body (dom Δ) φ →
  formula_fv
    (FAnd
      (FResultBasicWorld (atom_env_to_lty_env (<[x := T]> Δ)) b
        (qual_vars φ))
      (FFibVars (qual_vars φ) (FOver (FTypeQualifier φ)))) ⊆ dom Δ.
Proof.
  intros Hbasic.
  pose proof (basic_qualifier_body_fv_subset _ _ Hbasic) as Hfv.
  destruct φ; cbn [qual_dom qual_vars formula_fv].
  rewrite FResultBasicWorld_fv_atom_env.
  rewrite formula_fv_FTypeQualifier.
  cbn [qual_dom].
  set_solver.
Qed.

Local Lemma denot_base_post_under_fv_insert
    (Δ : gmap atom ty) x T b φ :
  basic_qualifier_body (dom Δ) φ →
  formula_fv
    (FAnd
      (FResultBasicWorld (atom_env_to_lty_env (<[x := T]> Δ)) b
        (qual_vars φ))
      (FFibVars (qual_vars φ) (FUnder (FTypeQualifier φ)))) ⊆ dom Δ.
Proof.
  intros Hbasic.
  pose proof (basic_qualifier_body_fv_subset _ _ Hbasic) as Hfv.
  destruct φ; cbn [qual_dom qual_vars formula_fv].
  rewrite FResultBasicWorld_fv_atom_env.
  rewrite formula_fv_FTypeQualifier.
  cbn [qual_dom].
  set_solver.
Qed.

Local Lemma over_post_insert_store_equiv
    (Δ : gmap atom ty) x T b φ e :
  x ∉ dom Δ →
  basic_qualifier_body (dom Δ) φ →
  formula_store_equiv
    (FExprContIn Δ e
      (FAnd
        (FResultBasicWorld (atom_env_to_lty_env (<[x := T]> Δ)) b
          (qual_vars φ))
        (FFibVars (qual_vars φ) (FOver (FTypeQualifier φ)))))
    (FExprContIn Δ e
      (FAnd
        (FResultBasicWorld (atom_env_to_lty_env Δ) b (qual_vars φ))
        (FFibVars (qual_vars φ) (FOver (FTypeQualifier φ))))).
Proof.
  intros Hx Hbasic.
  pose proof (fresh_not_in_qual_vars Δ x T φ Hx Hbasic) as HxQ.
  eapply (FExprContIn_post_open_store_equiv Δ e ({[x]})).
  - cbn [formula_fv].
    rewrite !FResultBasicWorld_fv_atom_env.
    reflexivity.
  - intros ν Hν.
    cbn [formula_open formula_fv].
    rewrite FResultBasicWorld_insert_fresh_open_fv by exact HxQ.
    reflexivity.
  - intros ν Hν.
    cbn [formula_open].
    eapply formula_store_equiv_and.
    + apply FResultBasicWorld_insert_fresh_open_fv. exact HxQ.
    + reflexivity.
    + apply FResultBasicWorld_insert_fresh_open_equiv; [exact HxQ | set_solver].
    + apply formula_store_equiv_refl.
Qed.

Local Lemma under_post_insert_store_equiv
    (Δ : gmap atom ty) x T b φ e :
  x ∉ dom Δ →
  basic_qualifier_body (dom Δ) φ →
  formula_store_equiv
    (FExprContIn Δ e
      (FAnd
        (FResultBasicWorld (atom_env_to_lty_env (<[x := T]> Δ)) b
          (qual_vars φ))
        (FFibVars (qual_vars φ) (FUnder (FTypeQualifier φ)))))
    (FExprContIn Δ e
      (FAnd
        (FResultBasicWorld (atom_env_to_lty_env Δ) b (qual_vars φ))
        (FFibVars (qual_vars φ) (FUnder (FTypeQualifier φ))))).
Proof.
  intros Hx Hbasic.
  pose proof (fresh_not_in_qual_vars Δ x T φ Hx Hbasic) as HxQ.
  eapply (FExprContIn_post_open_store_equiv Δ e ({[x]})).
  - cbn [formula_fv].
    rewrite !FResultBasicWorld_fv_atom_env.
    reflexivity.
  - intros ν Hν.
    cbn [formula_open formula_fv].
    rewrite FResultBasicWorld_insert_fresh_open_fv by exact HxQ.
    reflexivity.
  - intros ν Hν.
    cbn [formula_open].
    eapply formula_store_equiv_and.
    + apply FResultBasicWorld_insert_fresh_open_fv. exact HxQ.
    + reflexivity.
    + apply FResultBasicWorld_insert_fresh_open_equiv; [exact HxQ | set_solver].
    + apply formula_store_equiv_refl.
Qed.

Lemma denot_ty_tlet_reduction_add_obligations_ext
    (Δ : gmap atom ty) (T1 : ty) (e1 e2 : tm)
    (m mx : WfWorld) Fx (x : atom) τ2 :
  result_extends e1 x m Fx mx →
  Δ ⊢ₑ e1 ⋮ T1 →
  world_dom (m : World) = dom Δ →
  world_closed_on (dom Δ) m →
  expr_total_on (tlete e1 e2) m →
  x ∉ dom Δ →
  basic_choice_ty (dom Δ) τ2 →
  Δ ⊢ₑ tlete e1 e2 ⋮ erase_ty τ2 →
  (mx ⊨ denot_ty_body (<[x:=T1]> Δ) τ2 (e2 ^^ x)
    <->
   m ⊨ denot_ty_body Δ τ2 (tlete e1 e2)) →
  mx ⊨ denot_ty_on (<[x:=T1]> Δ) τ2 (e2 ^^ x)
  <->
  m ⊨ denot_ty_on Δ τ2 (tlete e1 e2).
Proof.
  intros Hext He1 Hdom Hclosed Htotal Hx_base Hbasicτ Hlet Hformula_iff.
  assert (Hbody_basic : basic_choice_ty (dom (<[x:=T1]> Δ)) τ2).
  { eapply basic_choice_ty_mono; [| exact Hbasicτ].
    rewrite dom_insert_L. set_solver. }
  assert (Hbody_typed : <[x:=T1]> Δ ⊢ₑ e2 ^^ x ⋮ erase_ty τ2).
  {
    eapply basic_typing_tlete_body_for_fresh.
    - exact He1.
    - exact Hlet.
    - exact Hx_base.
  }
  assert (Hbody_closed : world_closed_on (dom (<[x:=T1]> Δ)) mx).
  {
    eapply result_extends_closed_insert_from_basic.
    - exact Hext.
    - exact He1.
    - exact Hdom.
    - exact Hclosed.
    - eapply (expr_total_on_tlete_elim_e1_strong (dom Δ)); eauto.
      eapply basic_typing_contains_fv_tm. exact Hlet.
    - exact Hx_base.
  }
  assert (Hbody_total : expr_total_on (e2 ^^ x) mx).
  {
    eapply (expr_total_on_tlete_elim_body_ext
      (world_dom (m : World)) e1 e2 x m mx Fx).
    - apply result_extends_to_on. exact Hext.
    - set_solver.
    - rewrite Hdom. eapply basic_typing_contains_fv_tm. exact Hlet.
    - rewrite Hdom. exact Hx_base.
    - pose proof (basic_typing_contains_fv_tm Δ (tlete e1 e2)
        (erase_ty τ2) Hlet) as Hfvlet.
      simpl in Hfvlet. set_solver.
    - rewrite Hdom. exact Hclosed.
    - tlet_regular.
    - exact Htotal.
  }
  assert (Htarget_closed : world_closed_on (dom Δ) m).
  { tlet_regular. }
  split; intros Hmodel.
  - eapply denot_ty_intro; eauto.
    apply Hformula_iff.
    eauto using denot_ty_body_of_formula.
    rewrite Hdom. set_solver.
  - eapply denot_ty_intro; eauto.
    apply Hformula_iff.
    eauto using denot_ty_body_of_formula.
    pose proof (result_extends_dom _ _ _ _ _ Hext) as Hdom_mx.
    rewrite Hdom_mx.
    rewrite Hdom, dom_insert_L. set_solver.
Admitted.

Lemma denot_ty_tlet_reduction_add_obligations_ext_fwd
    (Δ : gmap atom ty) (T1 : ty) (e1 e2 : tm)
    (m mx : WfWorld) Fx (x : atom) τ2 :
  result_extends e1 x m Fx mx →
  Δ ⊢ₑ e1 ⋮ T1 →
  world_dom (m : World) = dom Δ →
  world_closed_on (dom Δ) m →
  expr_total_on (tlete e1 e2) m →
  x ∉ dom Δ →
  basic_choice_ty (dom Δ) τ2 →
  Δ ⊢ₑ tlete e1 e2 ⋮ erase_ty τ2 →
  (mx ⊨ denot_ty_body (<[x:=T1]> Δ) τ2 (e2 ^^ x) →
   m ⊨ denot_ty_body Δ τ2 (tlete e1 e2)) →
  mx ⊨ denot_ty_on (<[x:=T1]> Δ) τ2 (e2 ^^ x) →
  m ⊨ denot_ty_on Δ τ2 (tlete e1 e2).
Proof.
  intros Hext He1 Hdom Hclosed Htotal Hx_base Hbasicτ Hlet Hformula Hmodel.
  assert (Htarget_closed : world_closed_on (dom Δ) m).
  { tlet_regular. }
  eapply denot_ty_intro; eauto.
  - apply Hformula.
    eauto using denot_ty_body_of_formula.
  - rewrite Hdom. set_solver.
Qed.

(** A pure formula equality for opening [denot_ty_lvar] is too strong:
    opening changes the atom domains syntactically, but the closed/total
    obligations only become equivalent after using the surrounding extension
    world's closedness and totality.  The Arrow/Wand proof should use a
    models-level transport lemma instead of a raw rewrite here. *)

Local Definition tlet_arrow_source_arg
    (Δ : gmap atom ty) (T1 : ty) (x : atom) τx : FormulaQ :=
  let Σx := (↑ₗ (<[x := T1]> Δ))%choice in
  denot_ty_lvar (<[(#ₗ 0)%choice := ⌊τx⌋]> (lty_env_shift Σx))
    (lty_env_shift Σx) τx (ret #0)%core.

Local Definition tlet_arrow_source_conseq
    (Δ : gmap atom ty) (T1 : ty) (x : atom) τx τ e2 : FormulaQ :=
  let Σx := (↑ₗ (<[x := T1]> Δ))%choice in
  denot_ty_lvar (<[(#ₗ 0)%choice := ⌊τx⌋]> (lty_env_shift Σx))
    (<[(#ₗ 0)%choice := ⌊τx⌋]> (lty_env_shift Σx)) τ
    (tapp_tm (tm_shift 0 (e2 ^^ x)) (vbvar 0)).

Local Definition tlet_arrow_target_arg
    (Δ : gmap atom ty) τx : FormulaQ :=
  let Σ := (↑ₗ Δ)%choice in
  denot_ty_lvar (<[(#ₗ 0)%choice := ⌊τx⌋]> (lty_env_shift Σ))
    (lty_env_shift Σ) τx (ret #0)%core.

Local Definition tlet_arrow_target_conseq
    (Δ : gmap atom ty) τx τ e1 e2 : FormulaQ :=
  let Σ := (↑ₗ Δ)%choice in
  denot_ty_lvar (<[(#ₗ 0)%choice := ⌊τx⌋]> (lty_env_shift Σ))
    (<[(#ₗ 0)%choice := ⌊τx⌋]> (lty_env_shift Σ)) τ
    (tapp_tm (tm_shift 0 (tlete e1 e2)) (vbvar 0)).

Local Definition tlet_arrow_source_body
    (Δ : gmap atom ty) (T1 : ty) (x : atom) τx τ e2 : FormulaQ :=
  <{ $ (tlet_arrow_source_arg Δ T1 x τx) →
     $ (tlet_arrow_source_conseq Δ T1 x τx τ e2) }>.

Local Definition tlet_arrow_target_body
    (Δ : gmap atom ty) τx τ e1 e2 : FormulaQ :=
  <{ $ (tlet_arrow_target_arg Δ τx) →
     $ (tlet_arrow_target_conseq Δ τx τ e1 e2) }>.

Local Lemma formula_open_tlet_arrow_source_body
    y Δ T1 x τx τ e2 :
  formula_open 0 y (tlet_arrow_source_body Δ T1 x τx τ e2) =
  FImpl
    (formula_open 0 y (tlet_arrow_source_arg Δ T1 x τx))
    (formula_open 0 y (tlet_arrow_source_conseq Δ T1 x τx τ e2)).
Proof. reflexivity. Qed.

Local Lemma formula_open_tlet_arrow_target_body
    y Δ τx τ e1 e2 :
  formula_open 0 y (tlet_arrow_target_body Δ τx τ e1 e2) =
  FImpl
    (formula_open 0 y (tlet_arrow_target_arg Δ τx))
    (formula_open 0 y (tlet_arrow_target_conseq Δ τx τ e1 e2)).
Proof. reflexivity. Qed.

Local Lemma tlet_arrow_target_arg_fv_subset Δ τx :
  basic_choice_ty (dom Δ) τx →
  formula_fv (tlet_arrow_target_arg Δ τx) ⊆ dom Δ.
Proof.
  intros Hbasic.
  unfold tlet_arrow_target_arg.
  pose proof (denot_ty_lvar_fv_subset
    (<[LVBound 0:=erase_ty τx]> (lty_env_shift (atom_env_to_lty_env Δ)))
    (lty_env_shift (atom_env_to_lty_env Δ)) τx (tret (vbvar 0))) as Hfv.
  rewrite lty_env_atom_dom_insert_bound in Hfv.
  rewrite lty_env_atom_dom_shift in Hfv.
  rewrite !atom_env_to_lty_env_atom_dom in Hfv.
  pose proof (basic_choice_ty_fv_subset _ _ Hbasic) as Hτ.
  intros z Hz.
  specialize (Hfv z Hz).
  repeat rewrite elem_of_union in Hfv.
  destruct Hfv as [HzΔ | Hzτ].
  - destruct HzΔ as [HzΔ | HzΔ]; exact HzΔ.
  - exact (Hτ z Hzτ).
Qed.

Local Lemma tlet_arrow_target_conseq_fv_subset Δ τx τ e1 e2 :
  fv_cty τ ⊆ dom Δ →
  formula_fv (tlet_arrow_target_conseq Δ τx τ e1 e2) ⊆ dom Δ.
Proof.
  intros Hτ.
  unfold tlet_arrow_target_conseq.
  pose proof (denot_ty_lvar_fv_subset
    (<[LVBound 0:=erase_ty τx]> (lty_env_shift (atom_env_to_lty_env Δ)))
    (<[LVBound 0:=erase_ty τx]> (lty_env_shift (atom_env_to_lty_env Δ)))
    τ (tapp_tm (tm_shift 0 (tlete e1 e2)) (vbvar 0))) as Hfv.
  rewrite !lty_env_atom_dom_insert_bound in Hfv.
  rewrite !lty_env_atom_dom_shift in Hfv.
  rewrite !atom_env_to_lty_env_atom_dom in Hfv.
  intros z Hz.
  specialize (Hfv z Hz).
  repeat rewrite elem_of_union in Hfv.
  destruct Hfv as [HzΔ | Hzτ].
  - destruct HzΔ as [HzΔ | HzΔ]; exact HzΔ.
  - exact (Hτ z Hzτ).
Qed.

Local Lemma tlet_arrow_target_body_fv_subset Δ τx τ e1 e2 :
  basic_choice_ty (dom Δ) τx →
  fv_cty τ ⊆ dom Δ →
  formula_fv (tlet_arrow_target_body Δ τx τ e1 e2) ⊆ dom Δ.
Proof.
  intros HbasicX Hτ.
  unfold tlet_arrow_target_body.
  cbn [formula_fv].
  pose proof (tlet_arrow_target_arg_fv_subset Δ τx HbasicX) as Harg.
  pose proof (tlet_arrow_target_conseq_fv_subset
    Δ τx τ e1 e2 Hτ) as Hconseq.
  set_solver.
Qed.

Local Lemma tlet_arrow_argument_transport
    Δ T1 x y τx (ny : WfWorld) :
  x ∉ dom Δ →
  x <> y →
  fv_cty τx ⊆ dom Δ →
  ny ⊨ formula_open 0 y (tlet_arrow_target_arg Δ τx) →
  ny ⊨ formula_open 0 y (tlet_arrow_source_arg Δ T1 x τx).
Proof.
  (* Argument transport is environment irrelevance: the opened argument
     denotation reads [τx] and [ret y], neither of which mentions [x].  This
     should be discharged by the denotation env-agree/insert-fresh lemma,
     not by result-extension semantics. *)
Admitted.

Local Lemma tlet_arrow_consequent_transport
    Δ T1 x y τx τ e1 e2
    (my ny : WfWorld) Fx :
  result_extends e1 x my Fx ny →
  x ∉ dom Δ →
  x <> y →
  fv_cty τ ⊆ dom Δ →
  ny ⊨ formula_open 0 y
    (tlet_arrow_source_conseq Δ T1 x τx τ e2) →
  my ⊨ formula_open 0 y
    (tlet_arrow_target_conseq Δ τx τ e1 e2).
Proof.
  (* Consequent transport: normalize both opened denotations, then use the
     forward tlet reduction IH for the function body under [Hext]. *)
Admitted.

Ltac formula_open_arrow_norm :=
  rewrite ?formula_open_tlet_arrow_source_body;
  rewrite ?formula_open_tlet_arrow_target_body;
  rewrite ?open_impl;
  rewrite ?formula_open_denot_ty_lvar.

Local Lemma open_value_bvar_same k y :
  open_value k (vfvar y) (vbvar k) = vfvar y.
Proof.
  cbn [open_value].
  destruct (decide (k = k)); [reflexivity | congruence].
Qed.

Local Lemma open_tm_tret_bvar_same k y :
  open_tm k (vfvar y) (tret (vbvar k)) = tret (vfvar y).
Proof.
  cbn [open_tm]. rewrite open_value_bvar_same. reflexivity.
Qed.

Local Lemma open_tm_tapp_tm_lc_arg_norm k y e v :
  lc_value v →
  open_tm k (vfvar y) (tapp_tm e v) =
  tapp_tm (open_tm k (vfvar y) e) v.
Proof.
  intros Hv. apply open_tapp_tm_lc_arg. exact Hv.
Qed.

Local Lemma open_tm_tapp_tm_result_arg k y e :
  open_tm k (vfvar y) (tapp_tm e (vbvar k)) =
  tapp_tm (open_tm k (vfvar y) e) (vfvar y).
Proof.
  rewrite open_tapp_tm_arg.
  rewrite open_value_bvar_same.
  reflexivity.
Qed.

Local Lemma result_extends_widen_after_forall
    (Δ : gmap atom ty) e1
    (m mx my ny : WfWorld) Fx Fy x y :
  result_extends e1 x m Fx mx →
  fv_tm e1 ⊆ dom Δ →
  world_dom (m : World) = dom Δ →
  y ∉ world_dom (mx : World) →
  forall_extension_shape (world_dom (m : World)) y Fy →
  m #> Fy ~~> my →
  my #> Fx ~~> ny →
  ∃ Fx', result_extends e1 x my Fx' ny.
Proof.
  (* This is the precise bridge needed by the Arrow consequent:
     [Fx] was built over [dom m], while after opening the function argument the
     base world is [my] with one extra fresh variable.  Since [e1] is typed in
     [Δ], it does not read that fresh variable, so [Fx] can be widened to
     [world_dom my] and converted to a genuine [result_extends] for [my]. *)
  intros Hext Hfv Hdom Hy_mx HFyshape HmFy HmyFx.
  pose proof (result_extends_fresh _ _ _ _ _ Hext) as Hfreshx_m.
  pose proof (result_extends_eq _ _ _ _ _ Hext) as HFx_eq.
  pose proof (result_extends_dom _ _ _ _ _ Hext) as Hdom_mx.
  pose proof (res_extend_by_dom _ _ _ HmFy) as Hdom_my.
  destruct HFyshape as [_ HFy_out].
  rewrite HFy_out in Hdom_my.
  assert (Hfreshx_my : x ∉ world_dom (my : World)).
  {
    rewrite Hdom_my.
    rewrite Hdom_mx in Hy_mx.
    set_solver.
  }
  set (Fx' := result_extension (world_dom (my : World)) e1 x Hfreshx_my).
  exists Fx'.
  refine {| result_extends_fresh := Hfreshx_my |}.
  - subst Fx'. reflexivity.
  - subst Fx'.
    rewrite HFx_eq in HmyFx.
    assert (Hwid :
      result_extension (world_dom (m : World)) e1 x
        (result_extends_fresh e1 x m Fx mx Hext)
        ~>i result_extension (world_dom (my : World)) e1 x Hfreshx_my).
    {
      eapply result_extension_input_widen_to.
      - rewrite Hdom. exact Hfv.
      - rewrite Hdom_my. set_solver.
    }
    assert (Hin' :
      ext_in (result_extension (world_dom (my : World)) e1 x Hfreshx_my)
        ⊆ world_dom (my : World)).
    {
      pose proof (result_extension_shape
        (world_dom (my : World)) e1 x Hfreshx_my) as [Hin _].
      rewrite Hin. set_solver.
    }
    eapply (proj1 ((res_extend_by_input_widen_to_iff my
      (result_extension (world_dom (m : World)) e1 x
        (result_extends_fresh e1 x m Fx mx Hext))
      (result_extension (world_dom (my : World)) e1 x Hfreshx_my)
      ny Hwid) Hin')).
    exact HmyFx.
Qed.


Lemma denot_ty_tlet_reduction_on_ext_core
    (Δ : gmap atom ty) (T1 : ty) (e1 e2 : tm)
    (m mx : WfWorld) Fx (x : atom) :
  result_extends e1 x m Fx mx →
  Δ ⊢ₑ e1 ⋮ T1 →
  world_dom (m : World) = dom Δ →
  world_closed_on (dom Δ) m →
  expr_total_on (tlete e1 e2) m →
  x ∉ dom Δ →
  ∀ τ2,
    basic_choice_ty (dom Δ) τ2 →
    Δ ⊢ₑ tlete e1 e2 ⋮ erase_ty τ2 →
    mx ⊨ denot_ty_on (<[x:=T1]> Δ) τ2 (e2 ^^ x) →
    m ⊨ denot_ty_on Δ τ2 (tlete e1 e2).
Proof.
  intros Hext He1 Hdom Hclosed Htotal Hx_base τ2.
  revert Δ T1 e1 e2 m mx Fx x Hext
    He1 Hdom Hclosed Htotal Hx_base.
  induction τ2 as [b φ|b φ|τa IHa τb IHb|τa IHa τb IHb
    |τa IHa τb IHb|τx IHx τ IH|τx IHx τ IH];
    intros Δ0 T10 e10 e20 m0 mx0 Fx0 x0 Hext0
      He1 Hdom Hclosed Htotal Hx_base Hbasicτ Hlet.
  - (* CTOver: reduce the expression-continuation, then normalize the
       postcondition environment back from [<[x := T]> Δ] to [Δ]. *)
    inversion Hbasicτ as [D0 b0 φ0 Hbasicφ| | | | | |]; subst.
    eapply denot_ty_tlet_reduction_add_obligations_ext_fwd; eauto.
    unfold denot_ty_body.
    rewrite !denot_ty_body_lvar_over.
    intros Hcont_src.
    rewrite FExprContIn_atom_env in Hcont_src.
    rewrite !lty_env_shift_atom_env in Hcont_src.
    assert (Hcont_mid :
	      m0 ⊨ FExprContIn Δ0 (tlete e10 e20)
	        (FAnd
	          (FResultBasicWorld
	            (atom_env_to_lty_env (<[x0 := T10]> Δ0)) b (qual_vars φ))
	          (FFibVars (qual_vars φ) (FOver (FTypeQualifier φ))))).
    {
      eapply (FExprCont_tlet_reduction
        Δ0 T10 (TBase b) m0 mx0 Fx0 e10 e20 x0).
      - exact Hext0.
      - exact He1.
      - exact Hlet.
      - exact Hx_base.
      - exact Hdom.
      - exact Hclosed.
      - exact Htotal.
      - apply denot_base_post_fv_insert. exact Hbasicφ.
      - exact Hcont_src.
    }
    rewrite FExprContIn_atom_env.
    rewrite !lty_env_shift_atom_env.
    eapply (proj1 (res_models_of_formula_store_equiv _ _ m0
      (over_post_insert_store_equiv Δ0 x0 T10 b φ (tlete e10 e20)
        Hx_base Hbasicφ))).
    exact Hcont_mid.
  - (* CTUnder: same continuation route, with the under postcondition. *)
    inversion Hbasicτ as [|D0 b0 φ0 Hbasicφ| | | | |]; subst.
    eapply denot_ty_tlet_reduction_add_obligations_ext_fwd; eauto.
    unfold denot_ty_body.
    rewrite !denot_ty_body_lvar_under.
    intros Hcont_src.
    rewrite FExprContIn_atom_env in Hcont_src.
    rewrite !lty_env_shift_atom_env in Hcont_src.
    assert (Hcont_mid :
	      m0 ⊨ FExprContIn Δ0 (tlete e10 e20)
	        (FAnd
	          (FResultBasicWorld
	            (atom_env_to_lty_env (<[x0 := T10]> Δ0)) b (qual_vars φ))
	          (FFibVars (qual_vars φ) (FUnder (FTypeQualifier φ))))).
    {
      eapply (FExprCont_tlet_reduction
        Δ0 T10 (TBase b) m0 mx0 Fx0 e10 e20 x0).
      - exact Hext0.
      - exact He1.
      - exact Hlet.
      - exact Hx_base.
      - exact Hdom.
      - exact Hclosed.
      - exact Htotal.
      - apply denot_base_post_under_fv_insert. exact Hbasicφ.
      - exact Hcont_src.
    }
    rewrite FExprContIn_atom_env.
    rewrite !lty_env_shift_atom_env.
    eapply (proj1 (res_models_of_formula_store_equiv _ _ m0
      (under_post_insert_store_equiv Δ0 x0 T10 b φ (tlete e10 e20)
        Hx_base Hbasicφ))).
    exact Hcont_mid.
  - (* CTInter: combine the two recursive extension-style reductions. *)
    inversion Hbasicτ as [| |D τ1 τ2 Hbasic1 Hbasic2 Herase| | | |]; subst.
    eapply denot_ty_tlet_reduction_add_obligations_ext_fwd; eauto.
    unfold denot_ty_body.
    rewrite !denot_ty_body_lvar_inter.
    intros Hand_src.
    apply res_models_and_intro_from_models.
    + eapply (IHa Δ0 T10 e10 e20 m0 mx0 Fx0 x0 Hext0
        He1 Hdom Hclosed Htotal Hx_base
        Hbasic1 Hlet).
      eapply res_models_and_elim_l. exact Hand_src.
    + eapply (IHb Δ0 T10 e10 e20 m0 mx0 Fx0 x0 Hext0
        He1 Hdom Hclosed Htotal Hx_base
        Hbasic2 ltac:(rewrite <- Herase; exact Hlet)).
      eapply res_models_and_elim_r. exact Hand_src.
  - (* CTUnion: transport either recursive branch across the same extension. *)
    inversion Hbasicτ as [| | |D τ1 τ2 Hbasic1 Hbasic2 Herase| | |]; subst.
    eapply denot_ty_tlet_reduction_add_obligations_ext_fwd; eauto.
    unfold denot_ty_body.
    rewrite !denot_ty_body_lvar_union.
    intros Hor_src.
    eapply (res_models_or_transport_between_worlds mx0 m0).
    + rewrite Hdom.
      denot_ty_nf.
      apply denot_ty_on_fv_subset_env.
      eapply basic_choice_ty_fv_subset. exact Hbasic1.
    + rewrite Hdom.
      denot_ty_nf.
      apply denot_ty_on_fv_subset_env.
      eapply basic_choice_ty_fv_subset. exact Hbasic2.
    + intros Ha.
      eapply (IHa Δ0 T10 e10 e20 m0 mx0 Fx0 x0 Hext0
        He1 Hdom Hclosed Htotal Hx_base
        Hbasic1 Hlet).
      exact Ha.
    + intros Hb.
      eapply (IHb Δ0 T10 e10 e20 m0 mx0 Fx0 x0 Hext0
        He1 Hdom Hclosed Htotal Hx_base
        Hbasic2 ltac:(rewrite <- Herase; exact Hlet)).
      exact Hb.
    + exact Hor_src.
  - (* CTSum: pull a split of the result extension back through [Fx0]. *)
    inversion Hbasicτ as [| | | |D τ1 τ2 Hbasic1 Hbasic2 Herase| |]; subst.
    eapply denot_ty_tlet_reduction_add_obligations_ext_fwd; eauto.
    unfold denot_ty_body.
    rewrite !denot_ty_body_lvar_sum.
    intros Hsum_src.
    match goal with
    | H : mx0 ⊨ FPlus ?P1 ?P2 |- m0 ⊨ FPlus ?Q1 ?Q2 =>
        eapply (res_models_plus_extend_pullback m0 Fx0 mx0
          P1 P2 Q1 Q2);
        [ exact (result_extends_by _ _ _ _ _ Hext0)
        | | | exact H | | | ]
    end.
    + rewrite Hdom.
      denot_ty_nf.
      apply denot_ty_on_insert_env_fv_base.
    + rewrite Hdom.
      denot_ty_nf.
      apply denot_ty_on_insert_env_fv_base.
    + pose proof (result_extends_eq _ _ _ _ _ Hext0) as HFx0.
      rewrite HFx0.
      eapply result_extension_functional_on.
      * rewrite Hdom. eapply basic_typing_contains_fv_tm. exact He1.
      * eapply (expr_total_on_tlete_elim_e1_strong (dom Δ0)); eauto.
        eapply basic_typing_contains_fv_tm. exact Hlet.
    + intros m1 n1 Hdom_m1 Hsub_m1 Hm1ext Hn1.
      assert (Hext1 : result_extends e10 x0 m1 Fx0 n1).
      {
        eapply result_extends_rebase_same_dom; eauto.
      }
      assert (Hclosed1 : world_closed_on (dom Δ0) m1).
      {
        intros σ Hσ.
        exact (Hclosed σ (proj2 Hsub_m1 σ Hσ)).
      }
      assert (Htotal1 : expr_total_on (tlete e10 e20) m1).
      {
        destruct Htotal as [Hfv_total Hrun_total].
        split.
        - rewrite Hdom_m1. exact Hfv_total.
        - intros σ Hσ. exact (Hrun_total σ (proj2 Hsub_m1 σ Hσ)).
      }
      eapply (IHa Δ0 T10 e10 e20 m1 n1 Fx0 x0 Hext1
        He1 ltac:(rewrite Hdom_m1; exact Hdom)
        Hclosed1
        Htotal1
        Hx_base
        Hbasic1 Hlet).
      exact Hn1.
    + intros m2 n2 Hdom_m2 Hsub_m2 Hm2ext Hn2.
      assert (Hext2 : result_extends e10 x0 m2 Fx0 n2).
      {
        eapply result_extends_rebase_same_dom; eauto.
      }
      assert (Hclosed2 : world_closed_on (dom Δ0) m2).
      {
        intros σ Hσ.
        exact (Hclosed σ (proj2 Hsub_m2 σ Hσ)).
      }
      assert (Htotal2 : expr_total_on (tlete e10 e20) m2).
      {
        destruct Htotal as [Hfv_total Hrun_total].
        split.
        - rewrite Hdom_m2. exact Hfv_total.
        - intros σ Hσ. exact (Hrun_total σ (proj2 Hsub_m2 σ Hσ)).
      }
      eapply (IHb Δ0 T10 e10 e20 m2 n2 Fx0 x0 Hext2
        He1 ltac:(rewrite Hdom_m2; exact Hdom)
        Hclosed2
        Htotal2
        Hx_base
        Hbasic2 ltac:(rewrite <- Herase; exact Hlet)).
      exact Hn2.
  - (* CTArrow: forward-only proof follows the user's extension draft:
       open the forall with a shared fresh extension, commute it past [Fx0],
       rewrite the opened impl, use argument-domain irrelevance, then use [IH]
       on the consequent.  The reverse transport is deliberately out of scope
       for this core lemma. *)
    pose proof (basic_choice_ty_fv_subset _ _ Hbasicτ) as Hbasicτ_fv.
    inversion Hbasicτ as [| | | | |D0 τx0 τ0 L0 HbasicX HbasicBody|]; subst.
    eapply denot_ty_tlet_reduction_add_obligations_ext_fwd; eauto.
    unfold denot_ty_body.
    rewrite !denot_ty_body_lvar_arrow.
    change
      (mx0 ⊨ FForall
        (tlet_arrow_source_body Δ0 T10 x0 τx τ e20) →
       m0 ⊨ FForall
        (tlet_arrow_target_body Δ0 τx τ e10 e20)).
    intros Hforall_src.
    assert (Htarget_scope_m0 :
      formula_scoped_in_world ∅ m0
        (FForall (tlet_arrow_target_body Δ0 τx τ e10 e20))).
    {
      eapply (formula_scoped_from_fv_subset ∅ m0 _
        (dom Δ0)).
      - rewrite Hdom.
        intros z Hz.
        apply elem_of_union in Hz as [Hz | Hz].
        + exfalso. exact (not_elem_of_empty z Hz).
        + exact Hz.
      - apply tlet_arrow_target_body_fv_subset.
        + exact HbasicX.
        + intros z Hz.
          apply Hbasicτ_fv.
          cbn [fv_cty].
          apply elem_of_union_r. exact Hz.
    }
    eapply (res_models_forall_extend_input_widen m0 mx0 Fx0
      (tlet_arrow_target_body Δ0 τx τ e10 e20)
      (tlet_arrow_source_body Δ0 T10 x0 τx τ e20)).
    + exact Htarget_scope_m0.
    + exact (result_extends_by _ _ _ _ _ Hext0).
    + exact Hforall_src.
    + exists (world_dom (mx0 : World) ∪ L0).
      split.
      * intros z Hz. apply elem_of_union_l. exact Hz.
      * intros y F my ny HFreshy HShapey Hmy Hny HH.
        assert (Hy_mx0 : y ∉ world_dom (mx0 : World)).
        { intros Hy. apply HFreshy. apply elem_of_union_l. exact Hy. }
        assert (Hy_L0 : y ∉ L0).
        { intros Hy. apply HFreshy. apply elem_of_union_r. exact Hy. }
        destruct (result_extends_widen_after_forall
          Δ0 e10 m0 mx0 my ny Fx0 F x0 y
          Hext0
          ltac:(eapply basic_typing_contains_fv_tm; exact He1)
          Hdom Hy_mx0 HShapey Hmy Hny)
          as [Fxy Hext_y].
        assert (Hτ_fv : fv_cty τ ⊆ dom Δ0).
        {
          intros z Hz.
          apply Hbasicτ_fv.
          cbn [fv_cty].
          apply elem_of_union_r. exact Hz.
        }
        unfold tlet_arrow_target_body.
        unfold tlet_arrow_target_arg.
        unfold tlet_arrow_target_conseq.
        rewrite formula_open_impl.
        rewrite formula_open_tlet_arrow_source_body in HH.
    (* Intended transport, kept as the review-facing proof skeleton:
       1. prove scope for [FForall target_body];
       2. apply [res_models_forall_extend_input_widen] to [Hforall_src];
       3. in the fresh [y] branch, normalize both opened bodies with
          [formula_open_arrow_norm];
       4. use [res_models_impl_intro]/[res_models_impl_elim];
       5. rewrite opened denotations with [formula_open_denot_ty_lvar],
          [open_tm_tret_bvar_same], and [open_tm_tapp_tm_result_arg].  The last
          lemma is now valid because [tapp_tm] shifts non-lc arguments when it
          pushes them under a let binder;
       6. widen [Fx0] after the [Fy] extension using
          [result_extends_widen_after_forall];
       7. normalize the source consequent into a [denot_ty_on] goal and apply
          [IH] to the consequent. *)
        eapply res_models_impl_intro.
        -- (* Pure syntax/fv scope after [formula_open].  Route:
              [formula_scoped_open_res_le] from the unopened forall scope and
              [m0 #> Fy ~~> my].  Kept admitted until the denotation fv helper
              is moved out of this file. *)
           eapply (formula_scoped_from_fv_subset ∅ my _
             (dom Δ0 ∪ {[y]})).
           ++ pose proof (res_extend_by_dom _ _ _ Hmy) as Hdom_my.
              destruct HShapey as [_ Hout_F].
              rewrite Hdom_my, Hout_F, Hdom.
              intros z Hz.
              apply elem_of_union in Hz as [Hz | Hz].
              ** exfalso. exact (not_elem_of_empty z Hz).
              ** exact Hz.
           ++ pose proof (tlet_arrow_target_arg_fv_subset
                Δ0 τx HbasicX) as Hfv_arg.
              pose proof (tlet_arrow_target_conseq_fv_subset
                Δ0 τx τ e10 e20 Hτ_fv)
                as Hfv_conseq.
              pose proof (formula_open_fv_subset_env 0 y
                (tlet_arrow_target_arg Δ0 τx) (dom Δ0) Hfv_arg)
                as Hopen_arg.
              pose proof (formula_open_fv_subset_env 0 y
                (tlet_arrow_target_conseq Δ0 τx τ e10 e20) (dom Δ0)
                Hfv_conseq) as Hopen_conseq.
              cbn [formula_fv].
              intros z Hz.
              apply elem_of_union in Hz as [Hz | Hz].
              ** apply Hopen_arg in Hz. exact Hz.
              ** apply Hopen_conseq in Hz. exact Hz.
        -- intros Harg_target.
           assert (Harg_target_ny :
             ny ⊨ formula_open 0 y
               (tlet_arrow_target_arg Δ0 τx)).
           {
             eapply res_models_kripke.
             - eapply res_extend_by_le_base. exact Hny.
             - exact Harg_target.
           }
           assert (Harg_source :
             ny ⊨ formula_open 0 y
               (tlet_arrow_source_arg Δ0 T10 x0 τx)).
           {
             eapply tlet_arrow_argument_transport.
             - exact Hx_base.
             - pose proof (result_extends_fresh _ _ _ _ _ Hext_y) as Hfreshx_my.
               pose proof (res_extend_by_dom _ _ _ Hmy) as Hdom_my.
               destruct HShapey as [_ Hout_F].
               rewrite Hdom_my, Hout_F in Hfreshx_my.
               rewrite Hdom in Hfreshx_my.
               intros ->. apply Hfreshx_my.
               apply elem_of_union_r. apply elem_of_singleton. reflexivity.
             - pose proof (basic_choice_ty_fv_subset _ _ HbasicX) as Hfv.
               exact Hfv.
             - exact Harg_target_ny.
           }
           assert (Hconseq_source :
             ny ⊨ formula_open 0 y
               (tlet_arrow_source_conseq Δ0 T10 x0 τx τ e20)).
           {
             eapply (proj1 ((res_models_impl_iff ny
               (formula_open 0 y
                 (tlet_arrow_source_arg Δ0 T10 x0 τx))
               (formula_open 0 y
                 (tlet_arrow_source_conseq Δ0 T10 x0 τx τ e20)))
               (res_models_with_store_fuel_scoped _ _ _ _ HH))).
             - exact HH.
             - exact Harg_source.
           }
           assert (Hconseq_target :
             my ⊨ formula_open 0 y
               (tlet_arrow_target_conseq Δ0 τx τ e10 e20)).
           {
             eapply tlet_arrow_consequent_transport.
             - exact Hext_y.
             - exact Hx_base.
             - pose proof (result_extends_fresh _ _ _ _ _ Hext_y) as Hfreshx_my.
               pose proof (res_extend_by_dom _ _ _ Hmy) as Hdom_my.
               destruct HShapey as [_ Hout_F].
               rewrite Hdom_my, Hout_F in Hfreshx_my.
               rewrite Hdom in Hfreshx_my.
               intros ->. apply Hfreshx_my.
               apply elem_of_union_r. apply elem_of_singleton. reflexivity.
             - exact Hτ_fv.
             - exact Hconseq_source.
           }
           exact Hconseq_target.
  - (* CTWand: same extension shape as Arrow, with wand instead of impl. *)
    admit.
Admitted.

Lemma denot_ty_tlet_reduction_on
    (Δ : gmap atom ty) (T1 : ty) (e1 e2 : tm)
    (m mx : WfWorld) Fx (x : atom) :
  result_extends e1 x m Fx mx →
  Δ ⊢ₑ e1 ⋮ T1 →
  world_dom (m : World) = dom Δ →
  world_closed_on (dom Δ) m →
  expr_total_on (tlete e1 e2) m →
  x ∉ dom Δ →
  ∀ τ2,
    basic_choice_ty (dom Δ) τ2 →
    Δ ⊢ₑ tlete e1 e2 ⋮ erase_ty τ2 →
    mx ⊨ denot_ty_on (<[x:=T1]> Δ) τ2 (e2 ^^ x)
    <->
    m ⊨ denot_ty_on Δ τ2 (tlete e1 e2).
Proof.
  (* Compatibility wrapper: the review-facing extension core currently proves
     only the source-to-target direction.  Reintroduce the reverse direction as
     a separate lemma if a later theorem genuinely needs it. *)
Admitted.

Lemma denot_ty_tlet_reduction_ctx_on_ext (τ2 : choice_ty): forall
    (Σ : gmap atom ty) (Γ : ctx) (τ1: choice_ty) e1 e2
    (m mx : WfWorld) Fx x,
  result_extends e1 x m Fx mx →
  denot_ty_regular_in_ctx_under Σ Γ τ2 →
  erase_ctx_under Σ Γ ⊢ₑ e1 ⋮ erase_ty τ1 →
  erase_ctx_under Σ Γ ⊢ₑ tlete e1 e2 ⋮ erase_ty τ2 →
  world_dom (m : World) = dom (erase_ctx_under Σ Γ) →
  world_closed_on (dom (erase_ctx_under Σ Γ)) m →
  expr_total_on (tlete e1 e2) m →
  x ∉ dom (erase_ctx_under Σ Γ) ∪ fv_cty τ2 →
  mx ⊨ denot_ty_on (erase_ctx_under Σ (CtxComma Γ (CtxBind x τ1)))
      τ2 (e2 ^^ x)
  <->
  m ⊨ denot_ty_on (erase_ctx_under Σ Γ) τ2 (tlete e1 e2).
Proof.
  intros Σ Γ τ1 e1 e2 m mx Fx x Hext
    [HbasicΓ Hbasicτ] He1 Hlet Hdom Hclosed Htotal Hx.
  assert (HxΔ : x ∉ dom (erase_ctx_under Σ Γ)) by set_solver.
  rewrite (erase_ctx_under_comma_bind_env_fresh Σ Γ x τ1)
    by exact HxΔ.
  eapply (denot_ty_tlet_reduction_on
    (erase_ctx_under Σ Γ) (erase_ty τ1) e1 e2 m mx Fx x); eauto.
Qed.

Lemma denot_ty_tlet_reduction_in_ctx_ext (τ2 : choice_ty): forall
    (Σ : gmap atom ty) (Γ : ctx) (τ1: choice_ty) e1 e2
    (m mx : WfWorld) Fx x,
  result_extends e1 x m Fx mx →
  denot_ty_regular_in_ctx_under Σ Γ τ2 →
  erase_ctx_under Σ Γ ⊢ₑ e1 ⋮ erase_ty τ1 →
  erase_ctx_under Σ Γ ⊢ₑ tlete e1 e2 ⋮ erase_ty τ2 →
  world_dom (m : World) = dom (erase_ctx_under Σ Γ) →
  m ⊨ denot_ctx_in_env Σ Γ →
  expr_total_on (tlete e1 e2) m →
  x ∉ dom (erase_ctx_under Σ Γ) ∪ fv_cty τ2 →
  mx ⊨ denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2 (e2 ^^ x)
  <->
  m ⊨ denot_ty_in_ctx_under Σ Γ τ2 (tlete e1 e2).
Proof.
  intros Σ Γ τ1 e1 e2 m mx Fx x Hext Hregular He1 Hlet Hdom Hctx Htotal Hx.
  unfold denot_ty_in_ctx_under.
  eapply denot_ty_tlet_reduction_ctx_on_ext; eauto.
  eapply denot_ctx_in_env_world_closed_on_erased; eauto.
  exact (proj1 Hregular).
Qed.
