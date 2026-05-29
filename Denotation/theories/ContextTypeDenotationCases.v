(** * Denotation.ContextTypeDenotationCases

    Direct case-level semantic obligations for the Fundamental theorem.

    These lemmas are deliberately below [ContextTyping]: they mention context
    denotation and erased/basic terms, but not the typing judgment itself.  The
    typing proof should only unpack [context_typing_wf], instantiate induction
    hypotheses, and then call one of these gas-level obligations. *)

From Denotation Require Import Context ContextTypeDenotationSaturate.

Section ContextTypeDenotationCases.

Lemma const_direct_denotation_gas_in_ctx
    gas (Σ : gmap atom ty) c (m : WfWorldT) :
  m ⊨ denot_ctx_in_env Σ CtxEmpty ->
  erase_ctx_under Σ CtxEmpty ⊢ₑ
    tret (vconst c) ⋮ erase_ty (const_precise_ty c) ->
  m ⊨ denot_ty_lvar_gas gas
    (atom_env_to_lty_env (erase_ctx_under Σ CtxEmpty))
    (const_precise_ty c) (tret (vconst c)).
Proof.
Admitted.

Lemma letd_direct_denotation_gas_in_ctx
    gas (Σ : gmap atom ty) Γ1 Γ2 τ1 τ2 e1 e2 (L : aset)
    (m : WfWorldT) :
  m ⊨ denot_ctx_in_env Σ (CtxStar Γ1 Γ2) ->
  erase_ctx_under Σ (CtxStar Γ1 Γ2) ⊢ₑ tlete e1 e2 ⋮ erase_ty τ2 ->
  (denot_ctx_in_env Σ Γ1 ⊫ denot_ty_in_ctx_under Σ Γ1 τ1 e1) ->
  (forall x, x ∉ L ->
    denot_ctx_in_env Σ (CtxStar Γ2 (CtxBind x τ1)) ⊫
      denot_ty_in_ctx_under Σ (CtxStar Γ2 (CtxBind x τ1)) τ2 (e2 ^^ x)) ->
  m ⊨ denot_ty_lvar_gas gas
    (atom_env_to_lty_env (erase_ctx_under Σ (CtxStar Γ1 Γ2)))
    τ2 (tlete e1 e2).
Proof.
Admitted.

Lemma lam_direct_denotation_gas_in_ctx
    gas (Σ : gmap atom ty) Γ τx τ e (L : aset) (m : WfWorldT) :
  m ⊨ denot_ctx_in_env Σ Γ ->
  erase_ctx_under Σ Γ ⊢ₑ
    tret (vlam (erase_ty τx) e) ⋮ erase_ty (CTArrow τx τ) ->
  (forall y, y ∉ L ->
    denot_ctx_in_env Σ (CtxComma Γ (CtxBind y τx)) ⊫
      denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind y τx))
        ({0 ~> y} τ) (e ^^ y)) ->
  m ⊨ denot_ty_lvar_gas gas
    (atom_env_to_lty_env (erase_ctx_under Σ Γ))
    (CTArrow τx τ) (tret (vlam (erase_ty τx) e)).
Proof.
Admitted.

Lemma lamd_direct_denotation_gas_in_ctx
    gas (Σ : gmap atom ty) Γ τx τ e (L : aset) (m : WfWorldT) :
  m ⊨ denot_ctx_in_env Σ Γ ->
  erase_ctx_under Σ Γ ⊢ₑ
    tret (vlam (erase_ty τx) e) ⋮ erase_ty (CTWand τx τ) ->
  (forall y, y ∉ L ->
    denot_ctx_in_env Σ (CtxStar Γ (CtxBind y τx)) ⊫
      denot_ty_in_ctx_under Σ (CtxStar Γ (CtxBind y τx))
        ({0 ~> y} τ) (e ^^ y)) ->
  m ⊨ denot_ty_lvar_gas gas
    (atom_env_to_lty_env (erase_ctx_under Σ Γ))
    (CTWand τx τ) (tret (vlam (erase_ty τx) e)).
Proof.
Admitted.

Lemma app_direct_denotation_gas_in_ctx
    gas (Σ : gmap atom ty) Γ τx τ v1 x (m : WfWorldT) :
  m ⊨ denot_ctx_in_env Σ Γ ->
  erase_ctx_under Σ Γ ⊢ₑ tapp v1 (vfvar x) ⋮ erase_ty ({0 ~> x} τ) ->
  (denot_ctx_in_env Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ (CTArrow τx τ) (tret v1)) ->
  (denot_ctx_in_env Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ τx (tret (vfvar x))) ->
  m ⊨ denot_ty_lvar_gas gas
    (atom_env_to_lty_env (erase_ctx_under Σ Γ))
    ({0 ~> x} τ) (tapp v1 (vfvar x)).
Proof.
Admitted.

Lemma appd_direct_denotation_gas_in_ctx
    gas (Σ : gmap atom ty) Γ1 Γ2 τx τ v1 x (m : WfWorldT) :
  m ⊨ denot_ctx_in_env Σ (CtxStar Γ1 Γ2) ->
  erase_ctx_under Σ (CtxStar Γ1 Γ2) ⊢ₑ
    tapp v1 (vfvar x) ⋮ erase_ty ({0 ~> x} τ) ->
  (denot_ctx_in_env Σ Γ1 ⊫
    denot_ty_in_ctx_under Σ Γ1 (CTWand τx τ) (tret v1)) ->
  (denot_ctx_in_env Σ Γ2 ⊫
    denot_ty_in_ctx_under Σ Γ2 τx (tret (vfvar x))) ->
  m ⊨ denot_ty_lvar_gas gas
    (atom_env_to_lty_env (erase_ctx_under Σ (CtxStar Γ1 Γ2)))
    ({0 ~> x} τ) (tapp v1 (vfvar x)).
Proof.
Admitted.

Lemma fix_direct_denotation_gas_in_ctx
    gas (Σ : gmap atom ty) Γ τx τ vf (L : aset) (m : WfWorldT) :
  m ⊨ denot_ctx_in_env Σ Γ ->
  erase_ctx_under Σ Γ ⊢ₑ
    tret (vfix (erase_ty (CTArrow τx τ)) vf) ⋮ erase_ty (CTArrow τx τ) ->
  (forall y, y ∉ L ->
    denot_ctx_in_env Σ (CtxComma Γ (CtxBind y τx)) ⊫
      denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind y τx))
        (CTArrow (CTArrow τx τ) ({0 ~> y} τ))
        (tret ({0 ~> vfvar y} vf))) ->
  m ⊨ denot_ty_lvar_gas gas
    (atom_env_to_lty_env (erase_ctx_under Σ Γ))
    (CTArrow τx τ) (tret (vfix (erase_ty (CTArrow τx τ)) vf)).
Proof.
Admitted.

Lemma fixd_direct_denotation_gas_in_ctx
    gas (Σ : gmap atom ty) Γ τx τ vf (L : aset) (m : WfWorldT) :
  m ⊨ denot_ctx_in_env Σ Γ ->
  erase_ctx_under Σ Γ ⊢ₑ
    tret (vfix (erase_ty (CTWand τx τ)) vf) ⋮ erase_ty (CTWand τx τ) ->
  (forall y, y ∉ L ->
    denot_ctx_in_env Σ (CtxStar Γ (CtxBind y τx)) ⊫
      denot_ty_in_ctx_under Σ (CtxStar Γ (CtxBind y τx))
        (CTWand (CTWand τx τ) ({0 ~> y} τ))
        (tret ({0 ~> vfvar y} vf))) ->
  m ⊨ denot_ty_lvar_gas gas
    (atom_env_to_lty_env (erase_ctx_under Σ Γ))
    (CTWand τx τ) (tret (vfix (erase_ty (CTWand τx τ)) vf)).
Proof.
Admitted.

Lemma appop_direct_denotation_gas_in_ctx
    gas (Σ : gmap atom ty) Γ op x τarg τres (m : WfWorldT) :
  m ⊨ denot_ctx_in_env Σ Γ ->
  erase_ctx_under Σ Γ ⊢ₑ
    tprim op (vfvar x) ⋮ erase_ty ({0 ~> x} τres) ->
  (denot_ctx_in_env Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ τarg (tret (vfvar x))) ->
  m ⊨ denot_ty_lvar_gas gas
    (atom_env_to_lty_env (erase_ctx_under Σ Γ))
    ({0 ~> x} τres) (tprim op (vfvar x)).
Proof.
Admitted.

Lemma match_both_direct_denotation_gas_in_ctx
    gas (Σ : gmap atom ty) Γt Γf v τt τf et ef (m : WfWorldT) :
  m ⊨ denot_ctx_in_env Σ (CtxSum Γt Γf) ->
  erase_ctx_under Σ (CtxSum Γt Γf) ⊢ₑ
    tmatch v et ef ⋮ erase_ty (CTSum τt τf) ->
  (denot_ctx_in_env Σ Γt ⊫
    denot_ty_in_ctx_under Σ Γt (bool_precise_ty true) (tret v)) ->
  (denot_ctx_in_env Σ Γf ⊫
    denot_ty_in_ctx_under Σ Γf (bool_precise_ty false) (tret v)) ->
  (denot_ctx_in_env Σ Γt ⊫ denot_ty_in_ctx_under Σ Γt τt et) ->
  (denot_ctx_in_env Σ Γf ⊫ denot_ty_in_ctx_under Σ Γf τf ef) ->
  m ⊨ denot_ty_lvar_gas gas
    (atom_env_to_lty_env (erase_ctx_under Σ (CtxSum Γt Γf)))
    (CTSum τt τf) (tmatch v et ef).
Proof.
Admitted.

Lemma match_true_direct_denotation_gas_in_ctx
    gas (Σ : gmap atom ty) Γ v τ et ef (m : WfWorldT) :
  m ⊨ denot_ctx_in_env Σ Γ ->
  erase_ctx_under Σ Γ ⊢ₑ tmatch v et ef ⋮ erase_ty τ ->
  (denot_ctx_in_env Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ (bool_precise_ty true) (tret v)) ->
  (denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ et) ->
  erase_ctx_under Σ Γ ⊢ₑ ef ⋮ erase_ty τ ->
  m ⊨ denot_ty_lvar_gas gas
    (atom_env_to_lty_env (erase_ctx_under Σ Γ)) τ (tmatch v et ef).
Proof.
Admitted.

Lemma match_false_direct_denotation_gas_in_ctx
    gas (Σ : gmap atom ty) Γ v τ et ef (m : WfWorldT) :
  m ⊨ denot_ctx_in_env Σ Γ ->
  erase_ctx_under Σ Γ ⊢ₑ tmatch v et ef ⋮ erase_ty τ ->
  (denot_ctx_in_env Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ (bool_precise_ty false) (tret v)) ->
  erase_ctx_under Σ Γ ⊢ₑ et ⋮ erase_ty τ ->
  (denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ ef) ->
  m ⊨ denot_ty_lvar_gas gas
    (atom_env_to_lty_env (erase_ctx_under Σ Γ)) τ (tmatch v et ef).
Proof.
Admitted.

End ContextTypeDenotationCases.
