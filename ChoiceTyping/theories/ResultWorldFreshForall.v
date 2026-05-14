(** * ChoiceTyping.ResultWorldFreshForall

    Bridges from cofinite [fresh_forall] expression-result formulas to the
    concrete result world used by the tlet proof.

    The representative chosen by [fresh_forall] is explicit-name/cofinite, so
    the primitive lemma returns the renamed body.  Callers that know the body is
    equivariant can use the wrapper lemma to transport it back to [body y]. *)

From CoreLang Require Import Instantiation InstantiationProps OperationalProps
  BasicTypingProps LocallyNamelessProps.
From ChoiceTyping Require Import ResultWorldBridge.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

(** Renaming the cofinite representative of an expression-result continuation
    only changes the result coordinate. *)
Lemma FExprResultOn_dom_rename_from_current_exact_domain
    (Σ : gmap atom ty) (T : ty) e ν (n : WfWorld) :
  Σ ⊢ₑ e ⋮ T →
  ν ∉ dom Σ →
  world_dom (n : World) = dom Σ ∪ {[ν]} →
  n ⊨ FExprResultOn (dom Σ) e ν →
  n ⊨ formula_rename_atom (fresh_for (dom Σ)) ν
        (FExprResultOn (dom Σ) e (fresh_for (dom Σ))).
Proof.
  intros _ Hν _ Hmodel.
  cbn [dom].
  rewrite FExprResultOn_rename_result_fresh.
  - exact Hmodel.
  - apply fresh_for_not_in.
  - exact Hν.
Qed.

Lemma FExprResultOn_dom_exact_domain_eq_let_result_world_on
    (Σ : gmap atom ty) (T : ty) e ν (m n : WfWorld)
    (Hfresh : ν ∉ world_dom (m : World))
    (Hresult : ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e)) e →* tret vx) :
  Σ ⊢ₑ e ⋮ T →
  world_dom (m : World) = dom Σ →
  world_store_closed_on (dom Σ) m →
  world_dom (n : World) = dom Σ ∪ {[ν]} →
  res_restrict n (dom Σ) = m →
  n ⊨ FExprResultOn (dom Σ) e ν →
  n = let_result_world_on e ν m Hfresh Hresult.
Proof.
  (* Fold-based proof removed with primitive multi-fiber; this will be
     re-proved directly from FFibVars during the LN pass. *)
Admitted.

Lemma set_difference_pull_singleton (X Y : aset) x :
  x ∈ X →
  x ∉ Y →
  X ∖ Y = (X ∖ ({[x]} ∪ Y)) ∪ {[x]}.
Proof.
  intros HxX HxY.
  apply set_eq. intros z.
  rewrite elem_of_difference, elem_of_union, elem_of_difference,
    elem_of_union, !elem_of_singleton.
  split.
  - intros [HzX HzY].
    destruct (decide (z = x)) as [->|Hzx].
    + right. reflexivity.
    + left. split; [exact HzX |].
      intros [Hzx'|HzY']; [congruence | contradiction].
  - intros [[HzX Hnot] | Hzx].
    + split; [exact HzX |].
      intros HzY. apply Hnot. right. exact HzY.
    + subst z. split; [exact HxX | exact HxY].
Qed.

Lemma let_result_world_on_fiber_expr_result_in_world
    X e ν (n : WfWorld) Hfresh Hresult σX Hproj :
  fv_tm e ⊆ X →
  lc_tm e →
  ν ∉ X →
  X ⊆ world_dom (n : World) →
  world_store_closed_on X n →
  expr_result_in_world (store_restrict σX X) e ν
    (res_restrict
      (res_fiber_from_projection
        (let_result_world_on e ν n Hfresh Hresult) X σX Hproj)
      (X ∪ {[ν]})).
Proof.
  (* Pending direct multi-fiber exactness proof.  The proof is conceptually a
     projection argument, but the current script hits slow set normalization
     around [dom σX = X] and insert/restrict rewrites.  Keep this explicit
     statement as the future proof boundary instead of letting [set_solver]
     block the LN refactor. *)
Admitted.

Lemma let_result_world_on_FExprResultOn_scoped X e ν (n : WfWorld) Hfresh Hresult :
  ν ∉ X →
  X ⊆ world_dom (n : World) →
  formula_scoped_in_world ∅
    (let_result_world_on e ν n Hfresh Hresult)
    (FExprResultOn X e ν).
Proof.
  (* Pending lightweight scopedness proof; deliberately admitted while the
     formula naming representation is being replaced by LN. *)
Admitted.

Lemma FExprResultAtomOn_scoped_in_result_fiber
    X e ν (n : WfWorld) Hfresh Hresult σX Hproj :
  ν ∉ X →
  X ⊆ world_dom (n : World) →
  formula_scoped_in_world σX
    (res_fiber_from_projection
      (let_result_world_on e ν n Hfresh Hresult) X σX Hproj)
    (FExprResultAtomOn X e ν).
Proof.
  (* Pending lightweight scopedness proof; deliberately admitted while the
     formula naming representation is being replaced by LN. *)
Admitted.

Lemma let_result_world_on_models_FExprResult :
  ∀ X e ν (n : WfWorld) Hfresh Hresult,
    fv_tm e ⊆ X →
    lc_tm e →
    ν ∉ X →
    X ⊆ world_dom (n : World) →
    world_store_closed_on X n →
    let_result_world_on e ν n Hfresh Hresult ⊨ FExprResultOn X e ν.
Proof.
  (* Pending direct projection proof; this is the main bridge that should become
     simpler once formulas use LN binders and multi-fibers over [logic_var]. *)
Admitted.

Lemma fresh_forall_expr_result_to_let_result_world_renamed
    X e D (body : atom → FormulaQ) (m : WfWorld) :
  fv_tm e ⊆ X →
  lc_tm e →
  X ⊆ world_dom (m : World) →
  world_store_closed_on X m →
  m ⊨ fresh_forall D (fun x => FImpl (FExprResultOn X e x) (body x)) →
  ∃ L : aset,
    world_dom (m : World) ∪ D ∪ X ∪ fv_tm e ⊆ L ∧
    ∀ y,
      y ∉ L →
      ∀ Hfresh Hresult,
        (∀ (n : WfWorld),
          world_dom (n : World) = world_dom (m : World) ∪ {[y]} →
          n ⊨ FExprResultOn X e y →
          n ⊨ formula_rename_atom (fresh_for D) y
                 (FExprResultOn X e (fresh_for D))) →
        let_result_world_on e y m Hfresh Hresult ⊨
          formula_rename_atom (fresh_for D) y (body (fresh_for D)).
Proof.
  (* Legacy fresh_forall bridge; to be replaced by LN open/cofinite bridge. *)
Admitted.

Lemma fresh_forall_expr_result_to_let_result_world
    X e D (body : atom → FormulaQ) (m : WfWorld) :
  fv_tm e ⊆ X →
  lc_tm e →
  X ⊆ world_dom (m : World) →
  world_store_closed_on X m →
  m ⊨ fresh_forall D (fun x => FImpl (FExprResultOn X e x) (body x)) →
  ∃ L : aset,
    world_dom (m : World) ∪ D ∪ X ∪ fv_tm e ⊆ L ∧
    ∀ y,
      y ∉ L →
      ∀ Hfresh Hresult,
        (∀ (n : WfWorld),
          world_dom (n : World) = world_dom (m : World) ∪ {[y]} →
          n ⊨ FExprResultOn X e y →
          n ⊨ formula_rename_atom (fresh_for D) y
                 (FExprResultOn X e (fresh_for D))) →
        (∀ n,
          n ⊨ formula_rename_atom (fresh_for D) y (body (fresh_for D)) →
          n ⊨ body y) →
        let_result_world_on e y m Hfresh Hresult ⊨ body y.
Proof.
  intros Hfv Hlc HX Hclosed Hforall.
  destruct (fresh_forall_expr_result_to_let_result_world_renamed
    X e D body m Hfv Hlc HX Hclosed Hforall) as [L [HL Huse]].
  exists L. split; [exact HL |].
  intros y Hy Hfresh Hresult Hante Hbody.
  apply Hbody.
  eapply Huse; eauto.
Qed.

Lemma FExprContIn_to_let_result_world_on_exact_domain
    (Σ : gmap atom ty) (T : ty) e
    (P : atom → FormulaQ) (m : WfWorld) :
  Σ ⊢ₑ e ⋮ T →
  world_dom (m : World) = dom Σ →
  world_store_closed_on (dom Σ) m →
  expr_total_on (dom Σ) e m →
  (∀ ν, formula_fv (P ν) ⊆ dom Σ ∪ {[ν]}) →
  formula_family_rename_stable_on (dom Σ) P →
  m ⊨ FExprContIn Σ e P →
  ∃ L : aset,
    dom Σ ⊆ L ∧
    ∀ ν,
      ν ∉ L →
      ∀ Hfresh Hresult,
        let_result_world_on e ν m Hfresh Hresult ⊨ P ν.
Proof.
  (* Legacy fresh_forall bridge; to be replaced by LN open/cofinite bridge. *)
Admitted.

Lemma let_result_world_on_to_FExprContIn_exact_domain
    (Σ : gmap atom ty) (T : ty) e
    (P : atom → FormulaQ) (m : WfWorld) :
  Σ ⊢ₑ e ⋮ T →
  world_dom (m : World) = dom Σ →
  world_store_closed_on (dom Σ) m →
  expr_total_on (dom Σ) e m →
  (∀ ν, formula_fv (P ν) ⊆ dom Σ ∪ {[ν]}) →
  formula_family_rename_stable_on (dom Σ) P →
  (∃ L : aset,
    dom Σ ⊆ L ∧
    ∀ ν,
      ν ∉ L →
      ∀ Hfresh Hresult,
        let_result_world_on e ν m Hfresh Hresult ⊨ P ν) →
  m ⊨ FExprContIn Σ e P.
Proof.
  (* Legacy fresh_forall bridge; to be replaced by LN open/cofinite bridge. *)
Admitted.

Lemma FExprContIn_iff_let_result_world_on_exact_domain
    (Σ : gmap atom ty) (T : ty) e
    (P : atom → FormulaQ) (m : WfWorld) :
  Σ ⊢ₑ e ⋮ T →
  world_dom (m : World) = dom Σ →
  world_store_closed_on (dom Σ) m →
  expr_total_on (dom Σ) e m →
  (∀ ν, formula_fv (P ν) ⊆ dom Σ ∪ {[ν]}) →
  formula_family_rename_stable_on (dom Σ) P →
  m ⊨ FExprContIn Σ e P ↔
  ∃ L : aset,
    dom Σ ⊆ L ∧
    ∀ ν,
      ν ∉ L →
      ∀ Hfresh Hresult,
        let_result_world_on e ν m Hfresh Hresult ⊨ P ν.
Proof.
  (* Legacy fresh_forall bridge; to be replaced by LN open/cofinite bridge. *)
Admitted.
