(** * ContextTypeLanguage.Interface

    Public surface for the type-language layer.  Other layers should import
    this file instead of reaching into the implementation files directly. *)

From LocallyNameless Require Import Classes.
From ContextTypeLanguage Require Export WellFormed Tactics.

Definition basic_qualifier (D : aset) (q : type_qualifier) : Prop :=
  lvars_wf_at 0 D (qual_vars q).

Definition basic_qualifier_body (D : aset) (q : type_qualifier) : Prop :=
  lvars_wf_at 1 D (qual_vars q).

Lemma basic_qualifier_lc D q :
  basic_qualifier D q ->
  lc_qualifier q.
Proof.
  intros Hwf [k|x] Hv; cbn [lc_logic_var_key].
  - exfalso.
    specialize (Hwf (LVBound k) Hv). cbn [lvar_wf_at] in Hwf. lia.
  - exact I.
Qed.

Lemma basic_qualifier_body_lc D q :
  basic_qualifier_body D q ->
  body_qualifier q.
Proof.
  intros Hwf.
  exists D. intros x Hx.
  apply basic_qualifier_lc with (D := D ∪ {[x]}).
  unfold basic_qualifier.
  rewrite qual_open_atom_vars.
  apply lvars_wf_at_open_body; assumption.
Qed.

Lemma basic_qualifier_fv_subset D q :
  basic_qualifier D q ->
  qual_dom q ⊆ D.
Proof.
  apply lvars_wf_at_fv_subset.
Qed.

Lemma basic_qualifier_body_fv_subset D q :
  basic_qualifier_body D q ->
  qual_dom q ⊆ D.
Proof.
  apply lvars_wf_at_fv_subset.
Qed.

Lemma basic_qualifier_body_top D :
  basic_qualifier_body D qual_top.
Proof.
  unfold basic_qualifier_body, qual_top. cbn [qual_vars qual_lvars].
  intros v Hv. set_solver.
Qed.

Lemma basic_context_ty_over D b q :
  basic_qualifier_body D q ->
  basic_context_ty D (CTOver b q).
Proof.
  intros Hq.
  apply basic_context_ty_iff_wf_context_ty_at.
  exact Hq.
Qed.

Lemma basic_context_ty_under D b q :
  basic_qualifier_body D q ->
  basic_context_ty D (CTUnder b q).
Proof.
  intros Hq.
  apply basic_context_ty_iff_wf_context_ty_at.
  exact Hq.
Qed.

Lemma basic_context_ty_inter D τ1 τ2 :
  basic_context_ty D τ1 ->
  basic_context_ty D τ2 ->
  erase_ty τ1 = erase_ty τ2 ->
  basic_context_ty D (CTInter τ1 τ2).
Proof.
  intros H1 H2 Herase.
  apply basic_context_ty_iff_wf_context_ty_at.
  cbn [wf_context_ty_at]. repeat split; try assumption;
    apply basic_context_ty_iff_wf_context_ty_at; assumption.
Qed.

Lemma basic_ctx_empty D :
  basic_ctx D CtxEmpty.
Proof.
  exact I.
Qed.

Lemma basic_ctx_bind D x τ :
  x ∉ D ->
  basic_context_ty D τ ->
  basic_ctx D (CtxBind x τ).
Proof.
  intros Hx Hτ. split; assumption.
Qed.

Lemma basic_ctx_star D Γ1 Γ2 :
  basic_ctx D Γ1 ->
  basic_ctx D Γ2 ->
  ctx_dom Γ1 ## ctx_dom Γ2 ->
  basic_ctx D (CtxStar Γ1 Γ2).
Proof.
  intros H1 H2 Hdisj. repeat split; assumption.
Qed.

Lemma basic_ctx_sum D Γ1 Γ2 :
  basic_ctx D Γ1 ->
  basic_ctx D Γ2 ->
  ctx_dom Γ1 = ctx_dom Γ2 ->
  erase_ctx Γ1 = erase_ctx Γ2 ->
  basic_ctx D (CtxSum Γ1 Γ2).
Proof.
  intros H1 H2 Hdom Herase. repeat split; assumption.
Qed.

#[global] Instance OpenFv_qualifier : OpenFv atom type_qualifier.
Proof.
  intros q x k.
  cbn [Stale_atom stale_qualifier].
  intros y Hy.
  pose proof (qual_open_atom_dom_subset k x q y Hy) as Hy'.
  apply elem_of_union in Hy' as [Hyq|Hyx].
  - apply elem_of_union_r. exact Hyq.
  - apply elem_of_union_l. exact Hyx.
Qed.

#[global] Instance OpenFv_cty : OpenFv atom context_ty.
Proof.
  intros τ x k.
  cbn [Stale_atom stale_cty_inst].
  intros y Hy.
  pose proof (cty_open_fv_subset k x τ y Hy) as Hy'.
  apply elem_of_union in Hy' as [Hyτ|Hyx].
  - apply elem_of_union_r. exact Hyτ.
  - apply elem_of_union_l. exact Hyx.
Qed.

#[global] Hint Resolve
  basic_context_ty_lc
  basic_context_ty_fv_subset
  basic_qualifier_lc
  basic_qualifier_body_lc
  basic_qualifier_fv_subset
  basic_qualifier_body_fv_subset
  basic_ctx_dom_fresh
  basic_ctx_empty
  basic_ctx_bind
  basic_ctx_star
  basic_ctx_sum
  : type_lang.
