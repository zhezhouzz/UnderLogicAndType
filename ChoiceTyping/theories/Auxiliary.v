(** * ChoiceTyping.Auxiliary

    Auxiliary judgments for the choice typing rules. *)

From CoreLang Require Import BasicTypingProps Sugar.
From ChoiceTyping Require Export WellFormed.
From ChoiceType Require Import LocallyNamelessProps.

Lemma basic_typing_tlet_tapp_fvar_open_arrow_body
    (Δ : gmap atom ty) y e1 e2 τx τ :
  y ∉ dom Δ ->
  Δ ⊢ₑ tlete e1 e2 ⋮ erase_ty (CTArrow τx τ) ->
  (<[y := erase_ty τx]> Δ) ⊢ₑ
    tlete e1 (tapp_tm e2 (vfvar y)) ⋮ erase_ty ({0 ~> y} τ).
Proof.
  intros Hy Hlet.
  inversion Hlet as [|Γ T1 T2 e1' e2' L He1 Hbody| | |]; subst.
  rewrite cty_open_preserves_erasure.
  eapply TT_Let with (L := L ∪ {[y]}).
  - eapply basic_typing_weaken_insert_tm; eauto.
  - intros z Hz.
    rewrite open_tapp_tm_fvar.
    eapply basic_typing_tapp_tm.
    + assert (<[y := erase_ty τx]> (<[z := T1]> Δ) =
              <[z := T1]> (<[y := erase_ty τx]> Δ)) as Hperm.
      {
        apply map_eq. intros w.
        rewrite !lookup_insert.
        repeat case_decide; subst; try set_solver; reflexivity.
      }
      rewrite <- Hperm.
      eapply basic_typing_weaken_insert_tm.
      * rewrite dom_insert_L. set_solver.
      * apply Hbody. set_solver.
    + apply VT_FVar.
      rewrite lookup_insert_ne by set_solver.
      rewrite lookup_insert.
      destruct (decide (y = y)); [reflexivity | congruence].
Qed.

(** ** Semantic subtyping *)

Definition sub_type_under (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : choice_ty) : Prop :=
  wf_choice_ty_under Σ Γ τ1 ∧
  wf_choice_ty_under Σ Γ τ2 ∧
  erase_ty τ1 = erase_ty τ2 ∧
  ∀ e, fv_tm e ⊆ dom Σ ∪ ctx_dom Γ →
    denot_ctx_in_env Σ Γ ⊫
      FImpl (denot_ty_in_ctx_under Σ Γ τ1 e)
            (denot_ty_in_ctx_under Σ Γ τ2 e).

Definition ctx_sub_under
    (Σ : gmap atom ty) (X : aset) (Γ1 Γ2 : ctx) : Prop :=
  wf_ctx_under Σ Γ1 ∧
  wf_ctx_under Σ Γ2 ∧
  ty_env_agree_on X (erase_ctx_under Σ Γ1) (erase_ctx_under Σ Γ2) ∧
  ∀ r, r ⊨ denot_ctx_in_env Σ Γ1 →
       res_restrict r X ⊨ denot_ctx_in_env Σ Γ2.
