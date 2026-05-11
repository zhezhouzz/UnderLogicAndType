(** * ChoiceTyping.TLetExprResult

    Expression-result and fiber bridges for the [tlet] proof.

    The proved lemmas in this file are expression/result-world facts.  They do
    not by themselves prove the final typing [tlet] case.  The intentionally
    admitted high-level theorem below is kept only as a placeholder for the
    future proof once the generic [denot_ty_on] transport principle is repaired. *)

From CoreLang Require Import Instantiation InstantiationProps OperationalProps BasicTypingProps
  LocallyNamelessProps.
From ChoiceTyping Require Export TLetTotal.
From ChoiceTyping Require Import Naming.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

Lemma denot_tlet_semantic_at_world
    (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : choice_ty) e1 e2 (L : aset)
    (m : WfWorld) :
  choice_typing_wf Σ Γ e1 τ1 →
  choice_typing_wf Σ Γ (tlete e1 e2) τ2 →
  (denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ1 e1) →
  (∀ x, x ∉ L →
    denot_ctx_in_env Σ (CtxComma Γ (CtxBind x τ1)) ⊫
      denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2 (e2 ^^ x)) →
  m ⊨ denot_ctx_in_env Σ Γ →
  m ⊨ denot_ty_in_ctx_under Σ Γ τ2 (tlete e1 e2).
Proof.
(** Placeholder: this is the final semantic [tlet] statement and should not be
    used as evidence that the [tlet] case is proved.  The current proved
    material below stops at expression-result exactness/fiber bookkeeping. *)
Admitted.

Lemma expr_result_store_from_body_xfiber
    X e2 x ν ρ (mlet : WfWorld) σ vx v :
  x ∉ X →
  store_restrict σ X = ρ →
  (mlet : World) (<[x := vx]> σ) →
  res_models_with_store ρ mlet (FFib x (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν))) →
  expr_result_store ν
    (subst_map (<[x := vx]> (store_restrict σ X)) (e2 ^^ x))
    {[ν := v]} →
  expr_result_store ν
    (subst_map (<[x := vx]> ρ) (e2 ^^ x))
    {[ν := v]}.
Proof.
  intros _ Hρ _ _ Hstore. rewrite <- Hρ. exact Hstore.
Qed.

Lemma expr_result_in_world_tlete_xfiber_sound
    X e1 e2 x ν (n : WfWorld)
    (Hfresh : x ∉ world_dom (n : World))
    (Hresult : ∀ σ, (n : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx)
    (ρ : Store) (m mlet : WfWorld) σν :
  x ∉ X ∪ fv_tm e2 ∪ {[ν]} →
  (∀ σ, (n : World) σ → closed_env (store_restrict σ X)) →
  (∀ σ, (n : World) σ → lc_env (store_restrict σ X)) →
  (∀ σ vx,
    (n : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    stale vx = ∅ ∧ is_lc vx) →
  (∀ σ, (n : World) σ → body_tm (subst_map (store_restrict σ X) e2)) →
  (∀ σ, (m : World) σ → (n : World) σ ∧ store_restrict σ X = ρ) →
  (∀ σx, (mlet : World) σx →
    ∃ σ vx,
      (m : World) σ ∧
      subst_map (store_restrict σ X) e1 →* tret vx ∧
      σx = <[x := vx]> σ) →
  (∀ σ vx,
    (m : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    (mlet : World) (<[x := vx]> σ)) →
  res_models_with_store ρ mlet (FFib x (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν))) →
  (res_restrict m {[ν]} : World) σν →
  expr_result_store ν (subst_map ρ (tlete e1 e2)) σν.
Proof.
Admitted.

Lemma expr_result_in_world_tlete_xfiber_complete
    X e1 e2 x ν (n : WfWorld)
    (Hfresh : x ∉ world_dom (n : World))
    (Hresult : ∀ σ, (n : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx)
    (ρ : Store) (m mlet : WfWorld) σν :
  x ∉ X ∪ fv_tm e2 ∪ {[ν]} →
  (∀ σ, (n : World) σ → closed_env (store_restrict σ X)) →
  (∀ σ, (n : World) σ → lc_env (store_restrict σ X)) →
  (∀ σ vx,
    (n : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    stale vx = ∅ ∧ is_lc vx) →
  (∀ σ, (n : World) σ → body_tm (subst_map (store_restrict σ X) e2)) →
  (∀ σ, (m : World) σ → (n : World) σ ∧ store_restrict σ X = ρ) →
  (∀ σx, (mlet : World) σx →
    ∃ σ vx,
      (m : World) σ ∧
      subst_map (store_restrict σ X) e1 →* tret vx ∧
      σx = <[x := vx]> σ) →
  (∀ σ vx,
    (m : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    (mlet : World) (<[x := vx]> σ)) →
  res_models_with_store ρ mlet (FFib x (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν))) →
  expr_result_store ν (subst_map ρ (tlete e1 e2)) σν →
  (res_restrict m {[ν]} : World) σν.
Proof.
Admitted.

(** One-projection semantic core of tlet.

    After the outer [X]-fibers have fixed the input store [ρ], the body-side
    obligation still contains one more fiber for [x].  That [x]-fiber ranges
    over exactly the stores produced by [let_result_world_on]: each admissible
    input store is paired with an actual result [vx] of [e1].  Exactness of the
    inner result projection for [e2 ^^ x], together with the operational let
    bridge [expr_result_store_tlete_from_body_store], yields exactness of the
    [ν]-projection for [tlete e1 e2].

    The remaining proof work here is algebraic alignment of the fibered
    [let_result_world_on] with the fibered base world. *)
Lemma expr_result_in_world_tlete_from_body_xfiber
    X e1 e2 x ν (n : WfWorld)
    (Hfresh : x ∉ world_dom (n : World))
    (Hresult : ∀ σ, (n : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx)
    (ρ : Store) (m mlet : WfWorld) :
  x ∉ X ∪ fv_tm e2 ∪ {[ν]} →
  fv_tm (tlete e1 e2) ⊆ X →
  (∀ σ, (n : World) σ → closed_env (store_restrict σ X)) →
  (∀ σ, (n : World) σ → lc_env (store_restrict σ X)) →
  (∀ σ vx,
    (n : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    stale vx = ∅ ∧ is_lc vx) →
  (∀ σ, (n : World) σ → body_tm (subst_map (store_restrict σ X) e2)) →
  (* [m] is the current [X]-fiber of [n], and [ρ] is its fixed projection. *)
  (∀ σ, (m : World) σ → (n : World) σ ∧ store_restrict σ X = ρ) →
  (* [mlet] is the matching [X]-fiber of [let_result_world_on e1 x n]. *)
  (∀ σx, (mlet : World) σx →
    ∃ σ vx,
      (m : World) σ ∧
      subst_map (store_restrict σ X) e1 →* tret vx ∧
      σx = <[x := vx]> σ) →
  (∀ σ vx,
    (m : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    (mlet : World) (<[x := vx]> σ)) →
  res_models_with_store ρ mlet (FFib x (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν))) →
  expr_result_in_world ρ (tlete e1 e2) ν m.
Proof.
Admitted.

Lemma expr_result_in_world_tlete_from_body_projection_fiber
    X e1 e2 x ν (n : WfWorld)
    (Hfresh : x ∉ world_dom (n : World))
    (Hresult : ∀ σ, (n : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx)
    ρ Hprojn Hprojlet :
  X ⊆ world_dom (n : World) →
  x ∉ X ∪ fv_tm e2 ∪ {[ν]} →
  fv_tm (tlete e1 e2) ⊆ X →
  (∀ σ, (n : World) σ → closed_env (store_restrict σ X)) →
  (∀ σ, (n : World) σ → lc_env (store_restrict σ X)) →
  (∀ σ vx,
    (n : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    stale vx = ∅ ∧ is_lc vx) →
  (∀ σ, (n : World) σ → body_tm (subst_map (store_restrict σ X) e2)) →
  res_models_with_store ρ
    (res_fiber_from_projection
      (let_result_world_on e1 x n Hfresh Hresult) X ρ Hprojlet)
    (FFib x (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν))) →
  expr_result_in_world ρ (tlete e1 e2) ν
    (res_fiber_from_projection n X ρ Hprojn).
Proof.
Admitted.

Lemma fib_vars_obligation_tlete_from_body_foldr_base
    X e1 e2 x ν (n : WfWorld)
    (Hfresh : x ∉ world_dom (n : World))
    (Hresult : ∀ σ, (n : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx)
    ρ (m mlet : WfWorld) :
  x ∉ X ∪ fv_tm e2 ∪ {[ν]} →
  fv_tm (tlete e1 e2) ⊆ X →
  (∀ σ, (n : World) σ → closed_env (store_restrict σ X)) →
  (∀ σ, (n : World) σ → lc_env (store_restrict σ X)) →
  (∀ σ vx,
    (n : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    stale vx = ∅ ∧ is_lc vx) →
  (∀ σ, (n : World) σ → body_tm (subst_map (store_restrict σ X) e2)) →
  world_dom (m : World) = world_dom (n : World) →
  world_dom (mlet : World) = world_dom (n : World) ∪ {[x]} →
  (∀ σ, (m : World) σ → (n : World) σ ∧ store_restrict σ X = ρ) →
  (∀ σx, (mlet : World) σx →
    ∃ σ vx,
      (m : World) σ ∧
      subst_map (store_restrict σ X) e1 →* tret vx ∧
      σx = <[x := vx]> σ) →
  (∀ σ vx,
    (m : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    (mlet : World) (<[x := vx]> σ)) →
  res_models_with_store ρ mlet
    (FFib x (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν))) →
  res_models_with_store ρ m
    (FAtom (expr_logic_qual_on X (tlete e1 e2) ν)).
Proof.
Admitted.

Lemma fib_vars_obligation_tlete_from_body_foldr
    xs X e1 e2 x ν (n : WfWorld)
    (Hfresh : x ∉ world_dom (n : World))
    (Hresult : ∀ σ, (n : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx) :
  NoDup xs →
  (list_to_set xs : aset) ⊆ X →
  X ⊆ world_dom (n : World) →
  x ∉ X ∪ fv_tm e2 ∪ {[ν]} →
  fv_tm (tlete e1 e2) ⊆ X →
  (∀ σ, (n : World) σ → closed_env (store_restrict σ X)) →
  (∀ σ, (n : World) σ → lc_env (store_restrict σ X)) →
  (∀ σ vx,
    (n : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    stale vx = ∅ ∧ is_lc vx) →
  (∀ σ, (n : World) σ → body_tm (subst_map (store_restrict σ X) e2)) →
  ∀ ρ (m mlet : WfWorld),
    world_dom (m : World) = world_dom (n : World) →
    world_dom (mlet : World) = world_dom (n : World) ∪ {[x]} →
    (∀ σ, (m : World) σ →
      (n : World) σ ∧
      store_restrict σ (X ∖ (list_to_set xs : aset)) = ρ) →
    (∀ σx, (mlet : World) σx →
      ∃ σ vx,
        (m : World) σ ∧
        subst_map (store_restrict σ X) e1 →* tret vx ∧
        σx = <[x := vx]> σ) →
    (∀ σ vx,
      (m : World) σ →
      subst_map (store_restrict σ X) e1 →* tret vx →
      (mlet : World) (<[x := vx]> σ)) →
    snd (foldr fib_vars_acc_step
      (FFib x (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν)),
       fun ρ m => res_models_with_store ρ m
         (FFib x (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν)))) xs)
      ρ mlet →
    snd (foldr fib_vars_acc_step
      (FAtom (expr_logic_qual_on X (tlete e1 e2) ν),
       fun ρ m => res_models_with_store ρ m
         (FAtom (expr_logic_qual_on X (tlete e1 e2) ν))) xs)
      ρ m.
Proof.
Admitted.

(** Lifting the one-projection semantic core through the outer [X] fibers.
    This is the induction over [fib_vars_obligation X].  Its non-mechanical
    leaf is [expr_result_in_world_tlete_from_body_xfiber]; the rest is threading
    the invariant that the current fiber of [n] consists exactly of stores with
    the accumulated projection [ρ]. *)
Lemma fib_vars_obligation_tlete_from_body_normalized
    X e1 e2 x ν (n : WfWorld) Hfresh Hresult :
  X ⊆ world_dom (n : World) →
  x ∉ X ∪ fv_tm e2 ∪ {[ν]} →
  fv_tm (tlete e1 e2) ⊆ X →
  (∀ σ, (n : World) σ → closed_env (store_restrict σ X)) →
  (∀ σ, (n : World) σ → lc_env (store_restrict σ X)) →
  (∀ σ vx,
    (n : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    stale vx = ∅ ∧ is_lc vx) →
  (∀ σ, (n : World) σ → body_tm (subst_map (store_restrict σ X) e2)) →
  fib_vars_obligation X
    (FFib x (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν))) ∅
    (let_result_world_on e1 x n Hfresh Hresult) →
  fib_vars_obligation X
    (FAtom (expr_logic_qual_on X (tlete e1 e2) ν)) ∅ n.
Proof.
Admitted.

Lemma fib_vars_obligation_tlete_from_body_result_world
    X e1 e2 x ν (n : WfWorld) Hfresh Hresult :
  X ⊆ world_dom (n : World) →
  x ∉ X ∪ fv_tm e2 ∪ {[ν]} →
  fv_tm (tlete e1 e2) ⊆ X →
  (∀ σ, (n : World) σ → closed_env (store_restrict σ X)) →
  (∀ σ, (n : World) σ → lc_env (store_restrict σ X)) →
  (∀ σ vx,
    (n : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    stale vx = ∅ ∧ is_lc vx) →
  (∀ σ, (n : World) σ → body_tm (subst_map (store_restrict σ X) e2)) →
  fib_vars_obligation (X ∪ {[x]})
    (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν)) ∅
    (let_result_world_on e1 x n Hfresh Hresult) →
  fib_vars_obligation X
    (FAtom (expr_logic_qual_on X (tlete e1 e2) ν)) ∅ n.
Proof.
Admitted.

Lemma FExprResult_tlete_from_body_result_world
    X e1 e2 x ν (n : WfWorld) Hfresh Hresult :
  x ∉ X ∪ fv_tm e2 ∪ {[ν]} →
  fv_tm (tlete e1 e2) ⊆ X →
  (∀ σ, (n : World) σ → closed_env (store_restrict σ X)) →
  (∀ σ, (n : World) σ → lc_env (store_restrict σ X)) →
  (∀ σ vx,
    (n : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    stale vx = ∅ ∧ is_lc vx) →
  (∀ σ, (n : World) σ → body_tm (subst_map (store_restrict σ X) e2)) →
  let_result_world_on e1 x n Hfresh Hresult ⊨
    FExprResultOn (X ∪ {[x]}) (e2 ^^ x) ν →
  n ⊨ FExprResultOn X (tlete e1 e2) ν.
Proof.
Admitted.

(** Body-to-let lifting for the total tlet proof.

    This statement is deliberately phrased for an arbitrary result type [τ].
    The proof should use two ingredients:

    - expression-result exactness/composition for [tlete e1 e2];
    - a generic denotation transport theorem for [denot_ty_on].

    It should not prove the tlet case separately for [CTOver], [CTUnder], or
    any other type constructor.  Such a split would make the typing rule depend
    on the shape of [τ], which is the abstraction leak this lemma is meant to
    avoid.

    Anti-slip rule: the only let-specific work here should be expression-result
    composition for [tlete].  Once that composition is established, the
    arbitrary result type [τ] must be handled by a reusable
    [denot_ty_on]-transport theorem, not by local recursion on [τ2]. *)
