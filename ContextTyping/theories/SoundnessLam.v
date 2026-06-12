(** * ContextTyping.SoundnessLam

    Lam and LamD proof support for the direct Fundamental theorem.
    These lemmas are kept out of [Soundness.v] so the Fundamental dispatch file
    does not re-check the large Arrow/Wand transport proofs on every edit. *)

From CoreLang Require Import BasicTyping BasicTypingProps InstantiationProps
  SmallStep StrongNormalization.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceInterface ResourceExtension.
From ContextBasicDenotation Require Import StoreTyping TermExtension TermTLet Qualifier
  BasicTypingFormula RelevantEnv.
From Denotation Require Import Context
  TypeEquivCore
  TypeEquivTerm
  TypeEquiv
  ConstDenote.
From ContextTyping Require Import Typing.

Local Notation LStoreOnT := (LStoreOn (V := value)) (only parsing).

Lemma context_typing_wf_denot_static_guard_full
    (Σ : gmap atom ty) Γ τ e (m : WfWorldT) :
  context_typing_wf Σ Γ e τ ->
  m ⊨ ctx_denote_under Σ Γ ->
  m ⊨ ty_static_guard_formula
    (atom_env_to_lty_env (erase_ctx Γ))
    τ e.
Proof.
Admitted.

Lemma context_typing_wf_denot_static_guard_comma_bind_insert
    (Σ : gmap atom ty) Γ y τx τ e (m : WfWorldT) :
  y ∉ dom (erase_ctx Γ) ->
  context_typing_wf Σ (CtxComma Γ (CtxBind y τx)) e τ ->
  m ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind y τx)) ->
  m ⊨ ty_static_guard_formula
    (<[LVFree y := erase_ty τx]> (atom_env_to_lty_env (erase_ctx Γ)))
    τ e.
Proof.
Admitted.

Lemma ctx_erasure_under_agree_union_on_ty
    (Σ : gmap atom ty) Γ e τ :
  context_typing_wf Σ Γ e τ ->
  ty_env_agree_on (fv_cty τ) (Σ ∪ erase_ctx Γ) (ctx_erasure_under Σ Γ).
Proof.
Admitted.

Lemma lam_arrow_opened_app_static_guard_full
    (Σ : tyctx) Γ τx τ e
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  my ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind y τx)) ->
  my ⊨ ty_static_guard_formula
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (cty_open 0 y τ)
    (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)).
Proof.
Admitted.

Lemma lam_wand_opened_app_static_guard_full
    (Σ : tyctx) Γ τx τ e
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTWand τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  my ⊨ ctx_denote_under Σ (CtxStar Γ (CtxBind y τx)) ->
  my ⊨ ty_static_guard_formula
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (cty_open 0 y τ)
    (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)).
Proof.
Admitted.

Lemma lam_arrow_open_arg_mid_to_bind_denotation
    (Σ : tyctx) Γ τx τ e
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  my ⊨ ty_denote_gas (cty_depth τx)
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    τx (tret (vfvar y)) ->
  my ⊨ ty_denote_gas (cty_depth τx)
    (atom_env_to_lty_env (<[y:=erase_ty τx]> (ctx_erasure_under Σ Γ)))
    τx (tret (vfvar y)).
Proof.
Admitted.

Lemma lam_arrow_open_arg_normalize
    (Σ : tyctx) Γ τx τ e
    (my : WfWorldT) y :
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  my ⊨ formula_open 0 y
    (ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      (typed_lty_env_bind
        (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTArrow τx τ) (tret (vlam (erase_ty τx) e)))
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0))) ->
  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y)).
Proof.
Admitted.

Lemma lam_arrow_open_arg_to_bind_denotation
    (Σ : tyctx) Γ τx τ e
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      ((<[LVFree y := erase_ty τx]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y)) ->
  my ⊨ ty_denote_gas (cty_depth τx)
    (atom_env_to_lty_env (<[y:=erase_ty τx]> (ctx_erasure_under Σ Γ)))
    τx (tret (vfvar y)).
Proof.
Admitted.

Lemma lam_arrow_open_arg_to_bind_ctx
    (Σ : tyctx) Γ τx τ e
    (m my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  my ⊨ ctx_denote_under Σ Γ ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      ((<[LVFree y := erase_ty τx]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y)) ->
  my ⊨ ctx_denote_under (Σ ∪ erase_ctx Γ) (CtxBind y τx).
Proof.
Admitted.

Lemma lam_arrow_open_arg_to_comma_ctx
    (Σ : tyctx) Γ τx τ e
    (m my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  m ⊨ ctx_denote_under Σ Γ ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      ((<[LVFree y := erase_ty τx]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y)) ->
  my ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind y τx)).
Proof.
Admitted.

Lemma lam_body_to_arrow_result_mid
    (Σ : tyctx) Γ τx τ e
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  my ⊨ ty_denote_under Σ (CtxComma Γ (CtxBind y τx))
    ({0 ~> y} τ) (e ^^ y) ->
  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (cty_open 0 y τ) (e ^^ y).
Proof.
Admitted.

Lemma lam_arrow_result_mid_app_guard
    (Σ : tyctx) Γ τx τ e
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
	  my ⊨ ty_denote_gas 0
	    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
	    (cty_open 0 y τ) (e ^^ y) ->
	  my ⊨ ty_static_guard_formula
	    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
	    (cty_open 0 y τ)
	    (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)) ->
	  my ⊨ ty_guard_formula
    (relevant_env
      ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
      (cty_open 0 y τ)
      (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)))
	    (cty_open 0 y τ)
	    (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)).
		Proof.
Admitted.

Lemma lam_arrow_result_mid_app_denotation
    (Σ : tyctx) Γ τx τ e
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
	  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
	    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
	    (cty_open 0 y τ) (e ^^ y) ->
	  my ⊨ ty_static_guard_formula
	    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
	    (cty_open 0 y τ)
	    (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)) ->
	  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (cty_open 0 y τ)
	    (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)).
Proof.
Admitted.

Lemma lam_arrow_result_mid_to_opened_goal
    (Σ : tyctx) Γ τx τ e
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
	  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
	    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
	    (cty_open 0 y τ) (e ^^ y) ->
	  my ⊨ ty_static_guard_formula
	    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
	    (cty_open 0 y τ)
	    (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)) ->
	  my ⊨ formula_open 0 y
    (ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      (typed_lty_env_bind
        (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTArrow τx τ) (tret (vlam (erase_ty τx) e)))
        (erase_ty τx))
      τ
	      (tapp_tm (tm_shift 0 (tret (vlam (erase_ty τx) e))) (vbvar 0))).
Proof.
Admitted.

Lemma lam_body_to_opened_arrow_result
    (Σ : tyctx) Γ τx τ e
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
	  my ⊨ ty_denote_under Σ (CtxComma Γ (CtxBind y τx))
	    ({0 ~> y} τ) (e ^^ y) ->
	  my ⊨ ty_static_guard_formula
	    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
	    (cty_open 0 y τ)
	    (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)) ->
	  my ⊨ formula_open 0 y
    (ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      (typed_lty_env_bind
        (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTArrow τx τ) (tret (vlam (erase_ty τx) e)))
        (erase_ty τx))
      τ
      (tapp_tm (tm_shift 0 (tret (vlam (erase_ty τx) e))) (vbvar 0))).
Proof.
Admitted.

Lemma lam_opened_arrow_result
    (Σ : tyctx) Γ τx τ e (L : aset)
    (m my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  (forall y, y ∉ L ->
    ctx_denote_under Σ (CtxComma Γ (CtxBind y τx)) ⊫
      ty_denote_under Σ (CtxComma Γ (CtxBind y τx))
        ({0 ~> y} τ) (e ^^ y)) ->
  m ⊨ ctx_denote_under Σ Γ ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  y ∉ L ∪ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
		  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
		      ((<[LVFree y := erase_ty τx]>
            (atom_env_to_lty_env (erase_ctx Γ))))
	      (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y)) ->
	  my ⊨ formula_open 0 y
    (ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      (typed_lty_env_bind
        (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTArrow τx τ) (tret (vlam (erase_ty τx) e)))
        (erase_ty τx))
	      τ
	      (tapp_tm (tm_shift 0 (tret (vlam (erase_ty τx) e))) (vbvar 0))).
Proof.
Admitted.

Lemma lamd_wand_open_arg_to_bind_denotation
    (Σ : tyctx) Γ τx τ e
    (n : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTWand τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  n ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      ((<[LVFree y := erase_ty τx]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y)) ->
  n ⊨ ty_denote_gas (cty_depth τx)
    (atom_env_to_lty_env
      (<[y := erase_ty τx]> (store_restrict Σ (fv_cty τx))))
    τx (tret (vfvar y)).
Proof.
Admitted.

Lemma lamd_wand_open_arg_normalize
    (Σ : tyctx) Γ τx τ e
    (n : WfWorldT) y :
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  n ⊨ formula_open 0 y
    (ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      (typed_lty_env_bind
        (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTWand τx τ) (tret (vlam (erase_ty τx) e)))
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0))) ->
  n ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y)).
Proof.
Admitted.

Lemma lamd_open_arg_to_star_ctx
    (Σ : tyctx) Γ τx τ e
    (m n : WfWorldT) y (Hc : world_compat n m) :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTWand τx τ) ->
  m ⊨ ctx_denote_under Σ Γ ->
  world_dom (res_product n m Hc : WorldT) =
    world_dom (m : WorldT) ∪ ({[y]} : aset) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
	  n ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
	      ((<[LVFree y := erase_ty τx]>
          (atom_env_to_lty_env (erase_ctx Γ))))
	      (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y)) ->
	  res_product n m Hc ⊨ ctx_denote_under Σ (CtxStar Γ (CtxBind y τx)).
	Proof.
Admitted.

Lemma lamd_body_to_wand_result_mid
    (Σ : tyctx) Γ τx τ e
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTWand τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
	  my ⊨ ty_denote_under Σ (CtxStar Γ (CtxBind y τx))
	    ({0 ~> y} τ) (e ^^ y) ->
  my ⊨ ty_static_guard_formula
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (cty_open 0 y τ)
    (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)) ->
  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (cty_open 0 y τ)
    (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)).
Proof.
Admitted.

Lemma lamd_wand_result_mid_to_opened_goal
    (Σ : tyctx) Γ τx τ e
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTWand τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (cty_open 0 y τ)
    (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)) ->
  my ⊨ formula_open 0 y
    (ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      (typed_lty_env_bind
        (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTWand τx τ) (tret (vlam (erase_ty τx) e)))
        (erase_ty τx))
      τ
      (tapp_tm (tm_shift 0 (tret (vlam (erase_ty τx) e))) (vbvar 0))).
Proof.
Admitted.

Lemma lamd_opened_wand_result
    (Σ : tyctx) Γ τx τ e (L : aset)
    (m n : WfWorldT) y (Hc : world_compat n m) :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTWand τx τ) ->
  (forall y, y ∉ L ->
    ctx_denote_under Σ (CtxStar Γ (CtxBind y τx)) ⊫
      ty_denote_under Σ (CtxStar Γ (CtxBind y τx))
        ({0 ~> y} τ) (e ^^ y)) ->
  m ⊨ ctx_denote_under Σ Γ ->
  world_dom (res_product n m Hc : WorldT) =
    world_dom (m : WorldT) ∪ ({[y]} : aset) ->
  y ∉ L ∪ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  n ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      ((<[LVFree y := erase_ty τx]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y)) ->
  res_product n m Hc ⊨ formula_open 0 y
    (ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      (typed_lty_env_bind
        (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTWand τx τ) (tret (vlam (erase_ty τx) e)))
        (erase_ty τx))
      τ
      (tapp_tm (tm_shift 0 (tret (vlam (erase_ty τx) e))) (vbvar 0))).
Proof.
Admitted.
