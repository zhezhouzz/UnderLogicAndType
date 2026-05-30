(** * Denotation.Context

    Denotation of type contexts, expressed directly with the new recursive
    context-type denotation. *)

From Denotation Require Export Notation.
From Denotation Require Import ContextTypeDenotationSaturate.

Section ContextDenotation.

Definition erase_ctx_under (Σ : gmap atom ty) (Γ : ctx) : gmap atom ty :=
  Σ ∪ erase_ctx Γ.

Fixpoint denot_ctx_under (Σ : gmap atom ty) (Γ : ctx) : FormulaT :=
  FAnd (basic_world_formula (atom_env_to_lty_env (erase_ctx_under Σ Γ)))
    (match Γ with
    | CtxEmpty =>
        FTrue
    | CtxBind x τ =>
        denot_ty (<[x := erase_ty τ]> Σ) τ (tret (vfvar x))
    | CtxComma Γ1 Γ2 =>
        FAnd
          (denot_ctx_under Σ Γ1)
          (denot_ctx_under (Σ ∪ erase_ctx Γ1) Γ2)
    | CtxStar Γ1 Γ2 =>
        FStar (denot_ctx_under Σ Γ1) (denot_ctx_under Σ Γ2)
    | CtxSum Γ1 Γ2 =>
        FPlus (denot_ctx_under Σ Γ1) (denot_ctx_under Σ Γ2)
    end).

Definition denot_ctx (Γ : ctx) : FormulaT :=
  denot_ctx_under (erase_ctx Γ) Γ.

Definition denot_ty_under
    (Σ : gmap atom ty) (τ : context_ty) (e : tm) : FormulaT :=
  denot_ty Σ τ e.

Definition denot_ty_in_ctx (Γ : ctx) (τ : context_ty) (e : tm) : FormulaT :=
  denot_ty (erase_ctx Γ) τ e.

Definition denot_ty_in_ctx_under
    (Σ : gmap atom ty) (Γ : ctx) (τ : context_ty) (e : tm) : FormulaT :=
  denot_ty (erase_ctx_under Σ Γ) τ e.

Definition denot_ty_total_in_ctx_under
    (Σ : gmap atom ty) (Γ : ctx) (τ : context_ty) (e : tm)
    (m : WfWorldT) : Prop :=
  m ⊨ denot_ty_in_ctx_under Σ Γ τ e ∧
  m ⊨ expr_total_formula e.

Definition entails_total (φ : FormulaT) (P : WfWorldT -> Prop) : Prop :=
  forall m, m ⊨ φ -> P m.

Definition ty_env_agree_on (X : aset) (Σ1 Σ2 : gmap atom ty) : Prop :=
  forall x, x ∈ X -> Σ1 !! x = Σ2 !! x.

(** ** Context bridge lemmas for the Fundamental proof

    These statements are semantic context-denotation facts.  They live below
    [ContextTyping] so the Fundamental proof only instantiates induction
    hypotheses and calls the appropriate bridge. *)

Lemma denot_ctx_under_basic_world
    (Σ : gmap atom ty) (Γ : ctx) (m : WfWorldT) :
  m ⊨ denot_ctx_under Σ Γ ->
  m ⊨ basic_world_formula (atom_env_to_lty_env (erase_ctx_under Σ Γ)).
Proof.
  destruct Γ; cbn [denot_ctx_under]; rewrite res_models_and_iff; tauto.
Qed.

Lemma denot_ctx_under_bind_inv
    (Σ : gmap atom ty) x τ (m : WfWorldT) :
  m ⊨ denot_ctx_under Σ (CtxBind x τ) ->
  m ⊨ denot_ty (<[x := erase_ty τ]> Σ) τ (tret (vfvar x)).
Proof.
  cbn [denot_ctx_under].
  rewrite res_models_and_iff. tauto.
Qed.

Lemma denot_ctx_under_comma_inv
    (Σ : gmap atom ty) Γ1 Γ2 (m : WfWorldT) :
  m ⊨ denot_ctx_under Σ (CtxComma Γ1 Γ2) ->
  m ⊨ denot_ctx_under Σ Γ1 /\
  m ⊨ denot_ctx_under (Σ ∪ erase_ctx Γ1) Γ2.
Proof.
  cbn [denot_ctx_under].
  rewrite res_models_and_iff.
  intros [_ Hcomma].
  rewrite res_models_and_iff in Hcomma.
  exact Hcomma.
Qed.

Lemma denot_ctx_under_relevant_basic_world
    (Σ : gmap atom ty) (Γ : ctx) τ e (m : WfWorldT) :
  m ⊨ denot_ctx_under Σ Γ ->
  m ⊨ basic_world_formula
    (denot_relevant_env (atom_env_to_lty_env (erase_ctx_under Σ Γ)) τ e).
Proof.
  intros Hctx.
  pose proof (denot_ctx_under_basic_world Σ Γ m Hctx) as Hworld.
  eapply basic_world_formula_subenv.
  - intros v T Hv.
    eapply storeA_restrict_lookup_some in Hv as [_ Hv].
    exact Hv.
  - exact Hworld.
Qed.

Ltac destruct_basic_world_formula_hyps :=
  repeat match goal with
  | H : res_models _ (FAnd _ _) |- _ =>
      rewrite res_models_and_iff in H; destruct H
  | H : _ /\ _ |- _ =>
      destruct H
  end.

Ltac solve_basic_world_formula :=
  destruct_basic_world_formula_hyps;
  first
    [ assumption
    | eassumption
    | match goal with
      | Hctx : ?m ⊨ denot_ctx_under ?Σ ?Γ
        |- ?m ⊨ basic_world_formula
             (atom_env_to_lty_env (erase_ctx_under ?Σ ?Γ)) =>
          exact (denot_ctx_under_basic_world Σ Γ m Hctx)
      | Hctx : ?m ⊨ denot_ctx_under ?Σ ?Γ
        |- ?m ⊨ basic_world_formula
             (denot_relevant_env
                (atom_env_to_lty_env (erase_ctx_under ?Σ ?Γ)) ?τ ?e) =>
          exact (denot_ctx_under_relevant_basic_world Σ Γ τ e m Hctx)
      end
    | eauto ].

Lemma erase_ctx_under_comma_bind_env_fresh Σ Γ x τ :
  x ∉ dom (erase_ctx_under Σ Γ) →
  erase_ctx_under Σ (CtxComma Γ (CtxBind x τ)) =
  <[x := erase_ty τ]> (erase_ctx_under Σ Γ).
Proof.
  intros Hfresh.
  unfold erase_ctx_under in *.
  cbn [erase_ctx] in *.
  assert (HxΣ : x ∉ dom Σ) by better_set_solver.
  assert (HxΓ : x ∉ dom (erase_ctx Γ)) by better_set_solver.
  change (Σ ∪ ((erase_ctx Γ : gmap atom ty) ∪
      ({[x := erase_ty τ]} : gmap atom ty)) =
    <[x := erase_ty τ]> (Σ ∪ erase_ctx Γ)).
  replace ((erase_ctx Γ : gmap atom ty) ∪
      ({[x := erase_ty τ]} : gmap atom ty))
    with (<[x := erase_ty τ]> (erase_ctx Γ : gmap atom ty)).
  2:{
    symmetry.
    apply (storeA_union_singleton_insert_fresh
      (V := ty) (K := atom) (erase_ctx Γ : gmap atom ty)
      x (erase_ty τ)).
    exact HxΓ.
  }
  change (Σ ∪ (<[x := erase_ty τ]> (erase_ctx Γ : gmap atom ty) :
      gmap atom ty) =
    <[x := erase_ty τ]> (Σ ∪ erase_ctx Γ)).
  apply (storeA_insert_union_r_fresh (V := ty) (K := atom)
    (Σ : gmap atom ty) (erase_ctx Γ : gmap atom ty)
    x (erase_ty τ)).
  exact HxΣ.
Qed.

Lemma erase_ctx_under_star_bind_env_fresh Σ Γ x τ :
  x ∉ dom (erase_ctx_under Σ Γ) →
  erase_ctx_under Σ (CtxStar Γ (CtxBind x τ)) =
  <[x := erase_ty τ]> (erase_ctx_under Σ Γ).
Proof.
  intros Hfresh.
  unfold erase_ctx_under in *.
  cbn [erase_ctx] in *.
  assert (HxΣ : x ∉ dom Σ) by better_set_solver.
  assert (HxΓ : x ∉ dom (erase_ctx Γ)) by better_set_solver.
  change (Σ ∪ ((erase_ctx Γ : gmap atom ty) ∪
      ({[x := erase_ty τ]} : gmap atom ty)) =
    <[x := erase_ty τ]> (Σ ∪ erase_ctx Γ)).
  replace ((erase_ctx Γ : gmap atom ty) ∪
      ({[x := erase_ty τ]} : gmap atom ty))
    with (<[x := erase_ty τ]> (erase_ctx Γ : gmap atom ty)).
  2:{
    symmetry.
    apply (storeA_union_singleton_insert_fresh
      (V := ty) (K := atom) (erase_ctx Γ : gmap atom ty)
      x (erase_ty τ)).
    exact HxΓ.
  }
  change (Σ ∪ (<[x := erase_ty τ]> (erase_ctx Γ : gmap atom ty) :
      gmap atom ty) =
    <[x := erase_ty τ]> (Σ ∪ erase_ctx Γ)).
  apply (storeA_insert_union_r_fresh (V := ty) (K := atom)
    (Σ : gmap atom ty) (erase_ctx Γ : gmap atom ty)
    x (erase_ty τ)).
  exact HxΣ.
Qed.

Lemma denot_ctx_under_comma_bind_from_arg_denotation
    (Σ : gmap atom ty) (Γ : ctx) (τx : context_ty) y
    (m my : WfWorldT) (F : FiberExtensionT) :
  y ∉ dom (erase_ctx_under Σ Γ) ->
  m ⊨ denot_ctx_under Σ Γ ->
  res_extend_by m F my ->
  my ⊨ denot_ty_lvar_gas (cty_depth τx)
    (<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx_under Σ Γ)))
    τx (tret (vfvar y)) ->
  my ⊨ denot_ctx_under Σ (CtxComma Γ (CtxBind y τx)).
Proof.
Admitted.

Lemma denot_ctx_under_star_bind_from_arg_denotation
    (Σ : gmap atom ty) (Γ : ctx) (τx : context_ty) y
    (m marg : WfWorldT) (Hc : world_compat marg m) :
  y ∉ dom (erase_ctx_under Σ Γ) ->
  m ⊨ denot_ctx_under Σ Γ ->
  marg ⊨ denot_ty_lvar_gas (cty_depth τx)
    (<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx_under Σ Γ)))
    τx (tret (vfvar y)) ->
  res_product marg m Hc ⊨ denot_ctx_under Σ (CtxStar Γ (CtxBind y τx)).
Proof.
Admitted.

Lemma denot_ctx_under_star_bind_from_result_extension
    (Σ : gmap atom ty) Γ1 Γ τ1 e1 x
    (m2 m1 mx1 mbody : WfWorldT)
    (Hcbody : world_compat m2 mx1) (Fx : FiberExtensionT) :
  x ∉ dom (erase_ctx_under Σ Γ) ->
  m2 ⊨ denot_ctx_under Σ Γ ->
  m1 ⊨ denot_ty_in_ctx_under Σ Γ1 τ1 e1 ->
  expr_result_extension_witness e1 x Fx ->
  res_extend_by m1 Fx mx1 ->
  res_product m2 mx1 Hcbody ⊑ mbody ->
  mbody ⊨ denot_ctx_under Σ (CtxStar Γ (CtxBind x τ1)).
Proof.
Admitted.

Lemma denot_ty_in_ctx_under_comma_bind_to_lvar_insert
    (Σ : gmap atom ty) Γ τx τ e y (m : WfWorldT) :
  y ∉ dom (erase_ctx_under Σ Γ) ->
  m ⊨ denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind y τx)) τ e ->
  m ⊨ denot_ty_lvar_gas (cty_depth τ)
    (<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx_under Σ Γ)))
    τ e.
Proof.
  intros Hy Hden.
  unfold denot_ty_in_ctx_under, denot_ty in Hden |- *.
  rewrite (erase_ctx_under_comma_bind_env_fresh Σ Γ y τx Hy) in Hden.
  replace (<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx_under Σ Γ)))
    with (atom_env_to_lty_env
      (<[y := erase_ty τx]> (erase_ctx_under Σ Γ))).
  2:{ apply atom_store_to_lvar_store_insert. }
  exact Hden.
Qed.

Lemma denot_ty_in_ctx_under_star_bind_to_lvar_insert
    (Σ : gmap atom ty) Γ τx τ e y (m : WfWorldT) :
  y ∉ dom (erase_ctx_under Σ Γ) ->
  m ⊨ denot_ty_in_ctx_under Σ (CtxStar Γ (CtxBind y τx)) τ e ->
  m ⊨ denot_ty_lvar_gas (cty_depth τ)
    (<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx_under Σ Γ)))
    τ e.
Proof.
  intros Hy Hden.
  unfold denot_ty_in_ctx_under, denot_ty in Hden |- *.
  rewrite (erase_ctx_under_star_bind_env_fresh Σ Γ y τx Hy) in Hden.
  replace (<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx_under Σ Γ)))
    with (atom_env_to_lty_env
      (<[y := erase_ty τx]> (erase_ctx_under Σ Γ))).
  2:{ apply atom_store_to_lvar_store_insert. }
  exact Hden.
Qed.

Lemma denot_ctx_under_star_elim
    (Σ : gmap atom ty) Γ1 Γ2 (m : WfWorldT) :
  m ⊨ denot_ctx_under Σ (CtxStar Γ1 Γ2) ->
  exists (m1 m2 : WfWorldT) (Hc : world_compat m1 m2),
    res_product m1 m2 Hc ⊑ m /\
    m1 ⊨ denot_ctx_under Σ Γ1 /\
    m2 ⊨ denot_ctx_under Σ Γ2.
Proof.
  intros Hctx.
  cbn [denot_ctx_under] in Hctx.
  rewrite res_models_and_iff in Hctx.
  destruct Hctx as [_ Hstar].
  apply res_models_star_iff in Hstar as
    [m1 [m2 [Hc [Hle [HΓ1 HΓ2]]]]].
  exists m1, m2, Hc. repeat split; assumption.
Qed.

Lemma denot_ctx_under_sum_elim
    (Σ : gmap atom ty) Γ1 Γ2 (m : WfWorldT) :
  m ⊨ denot_ctx_under Σ (CtxSum Γ1 Γ2) ->
  exists (m1 m2 : WfWorldT) (Hdef : raw_sum_defined m1 m2),
    res_sum m1 m2 Hdef ⊑ m /\
    m1 ⊨ denot_ctx_under Σ Γ1 /\
    m2 ⊨ denot_ctx_under Σ Γ2.
Proof.
  intros Hctx.
  cbn [denot_ctx_under] in Hctx.
  rewrite res_models_and_iff in Hctx.
  destruct Hctx as [_ Hplus].
  apply res_models_plus_iff in Hplus as
    [m1 [m2 [Hdef [Hle [HΓ1 HΓ2]]]]].
  exists m1, m2, Hdef. repeat split; assumption.
Qed.

Lemma denot_ty_lvar_gas_star_union_to_ctx
    (Σ : gmap atom ty) Γ1 Γ2 τ e (m : WfWorldT) :
  m ⊨ denot_ty_lvar_gas (cty_depth τ)
    (atom_env_to_lty_env (erase_ctx_under Σ Γ1) ∪
     atom_env_to_lty_env (erase_ctx_under Σ Γ2)) τ e ->
  m ⊨ denot_ty_in_ctx_under Σ (CtxStar Γ1 Γ2) τ e.
Proof.
Admitted.

Lemma denot_ty_lvar_gas_sum_left_to_ctx
    (Σ : gmap atom ty) Γ1 Γ2 τ e (m : WfWorldT) :
  m ⊨ denot_ty_lvar_gas (cty_depth τ)
    (atom_env_to_lty_env (erase_ctx_under Σ Γ1)) τ e ->
  m ⊨ denot_ty_lvar_gas (cty_depth τ)
    (atom_env_to_lty_env (erase_ctx_under Σ (CtxSum Γ1 Γ2))) τ e.
Proof.
  unfold erase_ctx_under. cbn [erase_ctx]. auto.
Qed.

Lemma denot_ty_lvar_gas_sum_right_to_ctx
    (Σ : gmap atom ty) Γ1 Γ2 τ e (m : WfWorldT) :
  erase_ctx Γ1 = erase_ctx Γ2 ->
  m ⊨ denot_ty_lvar_gas (cty_depth τ)
    (atom_env_to_lty_env (erase_ctx_under Σ Γ2)) τ e ->
  m ⊨ denot_ty_lvar_gas (cty_depth τ)
    (atom_env_to_lty_env (erase_ctx_under Σ (CtxSum Γ1 Γ2))) τ e.
Proof.
  intros Herase Hden.
  unfold erase_ctx_under. cbn [erase_ctx].
  rewrite Herase.
  exact Hden.
Qed.

Lemma basic_typing_star_union_lty_env
    (Σ : gmap atom ty) Γ1 Γ2 e T :
  erase_ctx_under Σ (CtxStar Γ1 Γ2) ⊢ₑ e ⋮ T ->
  lty_env_to_atom_env
    (atom_env_to_lty_env (erase_ctx_under Σ Γ1) ∪
     atom_env_to_lty_env (erase_ctx_under Σ Γ2)) ⊢ₑ e ⋮ T.
Proof.
Admitted.

Lemma letd_body_world_compat
    e1 x (m1 m2 mx1 : WfWorldT) (Hc : world_compat m1 m2)
    (Fx : FiberExtensionT) :
  expr_result_extension_witness e1 x Fx ->
  x ∉ world_dom (m2 : WorldT) ->
  res_extend_by m1 Fx mx1 ->
  world_compat m2 mx1.
Proof.
  intros HFx Hx Hext.
  assert (Hout : ext_out Fx ## world_dom (m2 : WorldT)).
  {
    destruct HFx as [_ [_ Hout] _].
    unfold ext_out in *. rewrite Hout. set_solver.
  }
  assert (Hc_sym : world_compat m2 m1).
  {
    intros σ2 σ1 Hσ2 Hσ1.
    apply storeA_compat_sym. exact (Hc σ1 σ2 Hσ1 Hσ2).
  }
  pose proof (world_compat_restrict_l_extend_by_fresh
    m2 m1 mx1 Fx (world_dom (m2 : WorldT)) Hout Hext Hc_sym) as Hcompat.
  rewrite (res_restrict_eq_of_le m2 m2 ltac:(reflexivity)) in Hcompat.
  exact Hcompat.
Qed.

End ContextDenotation.

#[global] Instance denot_cty_inst :
    Denotation context_ty (tm -> Formula (V := value)) :=
  fun τ e => denot_ty ∅ τ e.
#[global] Instance denot_ctx_inst :
    Denotation ctx (Formula (V := value)) := denot_ctx.
Arguments denot_cty_inst /.
Arguments denot_ctx_inst /.
