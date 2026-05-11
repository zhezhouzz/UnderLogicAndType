(** * ChoiceTyping.TLetGraph

    Proof-side graph worlds for exact [tlet] result tracking. *)

From CoreLang Require Import Instantiation InstantiationProps OperationalProps BasicTypingProps
  LocallyNamelessProps.
From ChoiceTyping Require Export SoundnessCommon.
From ChoiceTyping Require Import Naming.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

Definition let_result_raw_world
    (ρ : Store) (e : tm) (x : atom) (w : WfWorld) : World := {|
  world_dom := world_dom (w : World) ∪ {[x]};
  world_stores := fun σx =>
    ∃ σ vx,
      (w : World) σ ∧
      subst_map σ (subst_map ρ e) →* tret vx ∧
      σx = <[x := vx]> σ;
|}.

Lemma let_result_raw_world_wf ρ e x (w : WfWorld) :
  x ∉ world_dom (w : World) →
  (∀ σ, (w : World) σ → ∃ vx, subst_map σ (subst_map ρ e) →* tret vx) →
  wf_world (let_result_raw_world ρ e x w).
Proof.
  intros Hfresh Hresult. constructor.
  - destruct (world_wf w) as [[σ Hσ] _].
    destruct (Hresult σ Hσ) as [vx Hsteps].
    exists (<[x := vx]> σ). exists σ, vx. repeat split; eauto.
  - intros σx [σ [vx [Hσ [Hsteps ->]]]].
    rewrite dom_insert_L.
    rewrite (wfworld_store_dom w σ Hσ).
    set_solver.
Qed.

Definition let_result_world
    (ρ : Store) (e : tm) (x : atom) (w : WfWorld)
    (Hfresh : x ∉ world_dom (w : World))
    (Hresult : ∀ σ, (w : World) σ → ∃ vx, subst_map σ (subst_map ρ e) →* tret vx)
    : WfWorld :=
  exist _ (let_result_raw_world ρ e x w)
    (let_result_raw_world_wf ρ e x w Hfresh Hresult).

Lemma let_result_world_member ρ e x (w : WfWorld) Hfresh Hresult σ vx :
  (w : World) σ →
  subst_map σ (subst_map ρ e) →* tret vx →
  (let_result_world ρ e x w Hfresh Hresult : World) (<[x := vx]> σ).
Proof.
  intros Hσ Hsteps. exists σ, vx. repeat split; eauto.
Qed.

Lemma let_result_world_elim ρ e x (w : WfWorld) Hfresh Hresult σx :
  (let_result_world ρ e x w Hfresh Hresult : World) σx →
  ∃ σ vx,
    (w : World) σ ∧
    subst_map σ (subst_map ρ e) →* tret vx ∧
    σx = <[x := vx]> σ.
Proof. intros Hσx. exact Hσx. Qed.

Lemma let_result_world_restrict ρ e x (w : WfWorld) Hfresh Hresult :
  res_restrict (let_result_world ρ e x w Hfresh Hresult)
    (world_dom (w : World)) = w.
Proof.
  apply wfworld_ext. apply world_ext.
  - simpl. set_solver.
  - intros σ. simpl. split.
    + intros [σx [[σ0 [vx [Hσ0 [Hsteps ->]]]] Hrestrict]].
      rewrite store_restrict_insert_notin in Hrestrict by exact Hfresh.
      assert (Hid : store_restrict σ0 (world_dom (w : World)) = σ0).
      { apply store_restrict_idemp.
        pose proof (wfworld_store_dom w σ0 Hσ0). set_solver. }
      rewrite Hid in Hrestrict.
      subst. exact Hσ0.
    + intros Hσ.
      destruct (Hresult σ Hσ) as [vx Hsteps].
      exists (<[x := vx]> σ). split.
      * exists σ, vx. repeat split; eauto.
      * rewrite store_restrict_insert_notin by exact Hfresh.
        apply store_restrict_idemp.
        pose proof (wfworld_store_dom w σ Hσ). set_solver.
Qed.

Lemma let_result_world_le ρ e x (w : WfWorld) Hfresh Hresult :
  w ⊑ let_result_world ρ e x w Hfresh Hresult.
Proof.
  pose proof (res_restrict_le
    (let_result_world ρ e x w Hfresh Hresult)
    (world_dom (w : World))) as Hle.
  rewrite (let_result_world_restrict ρ e x w Hfresh Hresult) in Hle.
  exact Hle.
Qed.

Lemma let_result_world_preserves_context Σ Γ ρ e x (w : WfWorld) Hfresh Hresult :
  w ⊨ denot_ctx_in_env Σ Γ →
  let_result_world ρ e x w Hfresh Hresult ⊨ denot_ctx_in_env Σ Γ.
Proof.
  intros Hctx.
  eapply res_models_kripke.
  - apply let_result_world_le.
  - exact Hctx.
Qed.

(** Proof-only exact graph for [tlet] results.

    This definition is deliberately not part of the paper syntax or semantic
    presentation.  The paper reasons informally with the result set of
    [let x = e1 in e2]; the Rocq proof sometimes needs a concrete witness
    world that remembers which intermediate result produced which final result.

    The important design point is that this is a *relation graph*, not a
    function graph.  If [e1] is nondeterministic, the same input projection
    [σ|X] may produce many intermediate values [vx].  If [e2] is
    nondeterministic, the same pair [(σ|X, vx)] may produce many final values
    [v].  Membership below therefore ranges over all triples [(σ, vx, v)]
    satisfying the two operational reductions:

      [subst_map (store_restrict σ X) e1 →* tret vx]
      [open_tm 0 vx (subst_map (store_restrict σ X) e2) →* tret v]

    The graph must be exact: it should contain no store unless it comes from
    such a triple, and every such triple is represented by the store
    [<[x := vx]> σ], where the base store [σ] already contains [ν ↦ v].
    This is the important alignment with [denot_ty_on]: result coordinates are
    introduced by the surrounding result quantifier, not by this auxiliary
    graph.  The graph only adds the intermediate coordinate [x].

    Freshness of [x] is essential.  It is a proof coordinate, so inserting it
    must not overwrite fields already present in the base world.  The final
    result coordinate [ν] is not fresh for [w]; it is expected to be part of
    [w]'s domain already.

    Whenever this definition appears in a proof, remember: it is an auxiliary
    Rocq witness world for tlet soundness, not a new paper-level modality.

    Relation to the expression-result/fiber view:

    - The paper-level intuition is still [∀M FV(e). Atom(mstep e ν)].  The
      surrounding fiber fixes the input store; the atom at the leaf should only
      talk about the result coordinate.  The graph below is the proof-side
      expansion of that idea for [tlet], where the input projection [X], the
      intermediate coordinate [x], and the final result coordinate [ν] all have
      to stay paired.
    - Do not read [world_stores] as allowing arbitrary extensions such as
      [{x ↦ vx, ν ↦ v}] disconnected from the same base input [σ].  Every member
      must come from one base store [σ] in [w], whose existing [ν] field is the
      final result [v], one result [vx] of [e1] over [σ|X], and one result [v]
      of [e2] opened with exactly that [vx].
    - Conversely, every such operational triple must be present.  This is the
      "no extra and no missing stores" invariant we need before proving either
      the over-approximate direction or the under-approximate direction.

    High-risk proof obligation to check first: after projecting/fibering this
    graph at [X ∪ {[x]}], the remaining [ν]-fiber must be exactly the result
    world for [(e2 ^^ x)] under that paired projection.  If that lemma fails,
    this graph shape is wrong and the later fundamental [tlet] case should not
    be trusted. *)
Definition tlet_result_graph_raw_world_on
    (X : aset) (e1 e2 : tm) (x ν : atom) (w : WfWorld) : World := {|
  world_dom := world_dom (w : World) ∪ {[x]};
  world_stores := fun σxν =>
    ∃ σ vx v,
      (w : World) σ ∧
      σ !! ν = Some v ∧
      subst_map (store_restrict σ X) e1 →* tret vx ∧
      open_tm 0 vx (subst_map (store_restrict σ X) e2) →* tret v ∧
      stale vx = ∅ ∧
      is_lc vx ∧
      stale v = ∅ ∧
      is_lc v ∧
      σxν = <[x := vx]> σ;
|}.

Lemma tlet_result_graph_raw_world_on_wf X e1 e2 x ν (w : WfWorld) :
  x ∉ world_dom (w : World) →
  (∃ σ vx v,
    (w : World) σ ∧
    σ !! ν = Some v ∧
    subst_map (store_restrict σ X) e1 →* tret vx ∧
    open_tm 0 vx (subst_map (store_restrict σ X) e2) →* tret v ∧
    stale vx = ∅ ∧
    is_lc vx ∧
    stale v = ∅ ∧
    is_lc v) →
  wf_world (tlet_result_graph_raw_world_on X e1 e2 x ν w).
Proof.
  intros Hfreshx Hinh.
  destruct Hinh as [σ [vx [v Hinh]]].
  destruct Hinh as [Hσ [Hν [Hsteps1 [Hsteps2 [Hvx_stale [Hvx_lc [Hv_stale Hv_lc]]]]]]].
  constructor.
  - exists (<[x := vx]> σ).
    exists σ, vx, v. repeat split; eauto.
  - intros σxν Hσxν.
    destruct Hσxν as [σ' [vx' [v' Hgraph]]].
    destruct Hgraph as [Hσ' [_ [_ [_ [_ [_ [_ [_ ->]]]]]]]].
    rewrite dom_insert_L.
    rewrite (wfworld_store_dom w σ' Hσ').
    set_solver.
Qed.

Definition tlet_result_graph_world_on
    (X : aset) (e1 e2 : tm) (x ν : atom) (w : WfWorld)
    (Hfreshx : x ∉ world_dom (w : World))
    (_Hnudom : ν ∈ world_dom (w : World))
    (Hinh : ∃ σ vx v,
      (w : World) σ ∧
      σ !! ν = Some v ∧
      subst_map (store_restrict σ X) e1 →* tret vx ∧
      open_tm 0 vx (subst_map (store_restrict σ X) e2) →* tret v ∧
      stale vx = ∅ ∧
      is_lc vx ∧
      stale v = ∅ ∧
      is_lc v)
    : WfWorld :=
  exist _ (tlet_result_graph_raw_world_on X e1 e2 x ν w)
    (tlet_result_graph_raw_world_on_wf X e1 e2 x ν w Hfreshx Hinh).

Lemma tlet_result_graph_world_on_member
    X e1 e2 x ν (w : WfWorld) Hfreshx Hnudom Hinh σ vx v :
  (w : World) σ →
  σ !! ν = Some v →
  subst_map (store_restrict σ X) e1 →* tret vx →
  open_tm 0 vx (subst_map (store_restrict σ X) e2) →* tret v →
  stale vx = ∅ →
  is_lc vx →
  stale v = ∅ →
  is_lc v →
  (tlet_result_graph_world_on X e1 e2 x ν w Hfreshx Hnudom Hinh : World)
    (<[x := vx]> σ).
Proof.
  intros Hσ Hν Hsteps1 Hsteps2 Hvx_stale Hvx_lc Hv_stale Hv_lc.
  exists σ, vx, v. repeat split; eauto.
Qed.

Lemma tlet_result_graph_world_on_elim
    X e1 e2 x ν (w : WfWorld) Hfreshx Hnudom Hinh σxν :
  (tlet_result_graph_world_on X e1 e2 x ν w Hfreshx Hnudom Hinh : World) σxν →
  ∃ σ vx v,
    (w : World) σ ∧
    σ !! ν = Some v ∧
    subst_map (store_restrict σ X) e1 →* tret vx ∧
    open_tm 0 vx (subst_map (store_restrict σ X) e2) →* tret v ∧
    stale vx = ∅ ∧
    is_lc vx ∧
    stale v = ∅ ∧
    is_lc v ∧
    σxν = <[x := vx]> σ.
Proof. intros Hσxν. exact Hσxν. Qed.

(** Soundness direction from a graph member to the whole-let result atom.

    Anti-slip rule: this is purely an expression-result/operational lemma.
    Prove it only by unpacking the graph member, store restrictions, and the
    [tlete] operational bridge.  Do not mention [denot_ty_on], do not inspect
    [τ], and do not split into over/under cases. *)
Lemma tlet_result_graph_member_to_tlet_result_store
    X e1 e2 x ν (w : WfWorld) Hfreshx Hnudom Hinh σxν :
  x ∉ X →
  ν ∉ X →
  (∀ σ, (w : World) σ → body_tm (subst_map (store_restrict σ X) e2)) →
  (tlet_result_graph_world_on X e1 e2 x ν w Hfreshx Hnudom Hinh : World) σxν →
  expr_result_store ν
    (subst_map (store_restrict σxν X) (tlete e1 e2))
    (store_restrict σxν {[ν]}).
Proof.
  intros HxX HνX Hbody Hgraph.
  destruct (tlet_result_graph_world_on_elim
    X e1 e2 x ν w Hfreshx Hnudom Hinh σxν Hgraph)
    as [σ [vx [v [Hσ [Hν [Hsteps1 [Hsteps2 [Hvx_stale [Hvx_lc [Hv_stale [Hv_lc ->]]]]]]]]]]].
  assert (Hρ :
    store_restrict (<[x := vx]> σ) X =
    store_restrict σ X).
  { rewrite store_restrict_insert_notin by exact HxX. reflexivity. }
  assert (Hνstore :
    store_restrict (<[x := vx]> σ) {[ν]} =
    ({[ν := v]} : Store)).
  {
    rewrite store_restrict_insert_singleton_ne by set_solver.
    apply store_restrict_singleton_lookup. exact Hν.
  }
  rewrite Hρ, Hνstore.
  eapply expr_result_store_let_intro; eauto.
Qed.

(** Soundness direction from a graph member to the opened-body result atom.

    Anti-slip rule: this must stay at the graph/fiber layer.  The key work is
    the LN/store-substitution bridge turning the graph's stored edge for
    [open_tm 0 vx ... e2] into an atom for [(e2 ^^ x)].  No proof step here
    should depend on the result type or on [CTOver]/[CTUnder]. *)
Lemma tlet_result_graph_member_to_body_result_store
    X e1 e2 x ν (w : WfWorld) Hfreshx Hnudom Hinh σxν :
  x ∉ X →
  x ∉ fv_tm e2 →
  ν ∉ X ∪ {[x]} →
  (∀ σ, (w : World) σ → closed_env (store_restrict σ X)) →
  (∀ σ, (w : World) σ → lc_env (store_restrict σ X)) →
  (tlet_result_graph_world_on X e1 e2 x ν w Hfreshx Hnudom Hinh : World) σxν →
  expr_result_store ν
    (subst_map (store_restrict σxν (X ∪ {[x]})) (e2 ^^ x))
    (store_restrict σxν {[ν]}).
Proof.
  intros HxX Hxe2 HνXx Hclosed Hlc Hgraph.
  destruct (tlet_result_graph_world_on_elim
    X e1 e2 x ν w Hfreshx Hnudom Hinh σxν Hgraph)
    as [σ [vx [v [Hσ [Hν [Hsteps1 [Hsteps2 [Hvx_stale [Hvx_lc [Hv_stale [Hv_lc ->]]]]]]]]]]].
  assert (Hσx :
    store_restrict (<[x := vx]> σ) (X ∪ {[x]}) =
    <[x := vx]> (store_restrict σ X)).
  {
    apply store_restrict_insert_fresh_union.
    - eapply store_lookup_none_of_dom.
      + apply wfworld_store_dom. exact Hσ.
      + exact Hfreshx.
    - exact HxX.
  }
  assert (Hνstore :
    store_restrict (<[x := vx]> σ) {[ν]} =
    ({[ν := v]} : Store)).
  {
    rewrite store_restrict_insert_singleton_ne by set_solver.
    apply store_restrict_singleton_lookup. exact Hν.
  }
  rewrite Hσx, Hνstore.
  apply expr_result_store_intro; [exact Hv_stale | exact Hv_lc |].
  eapply (steps_open_body_to_msubst_result X σ e2 x vx v).
  - exact HxX.
  - exact Hxe2.
  - apply Hclosed. exact Hσ.
  - exact Hvx_stale.
  - exact Hvx_lc.
  - apply Hlc. exact Hσ.
  - exact Hsteps2.
Qed.

(** Body-fiber exactness for the tlet graph.

    Anti-slip rule: this is one of the high-risk checks for the graph shape.
    The proof must show exact equality between the body result atom and the
    [X ∪ {[x]}]-fiber of the graph.  If the proof wants to split on
    [CTOver]/[CTUnder] or recurse on [τ], the abstraction boundary has been
    crossed and the statement should be refactored instead. *)
Lemma tlet_result_graph_body_fiber_exact
    X e1 e2 x ν (w : WfWorld) Hfreshx Hnudom Hinh ρx Hproj :
  X ⊆ world_dom (w : World) →
  x ∉ X →
  x ∉ fv_tm e2 →
  ν ∉ X ∪ {[x]} →
  (∀ σ, (w : World) σ → closed_env (store_restrict σ X)) →
  (∀ σ, (w : World) σ → lc_env (store_restrict σ X)) →
  (∀ σ, (w : World) σ → body_tm (subst_map (store_restrict σ X) e2)) →
  ∀ HprojX : res_restrict w X (store_restrict ρx X),
  expr_result_in_world
    (store_restrict ρx X) (tlete e1 e2) ν
    (res_fiber_from_projection w X (store_restrict ρx X) HprojX) →
  expr_result_in_world
    (store_restrict ρx (X ∪ {[x]})) (e2 ^^ x) ν
    (res_fiber_from_projection
      (tlet_result_graph_world_on X e1 e2 x ν w Hfreshx Hnudom Hinh)
      (X ∪ {[x]}) ρx Hproj).
Proof.
  intros HXdom HxX Hxe2 HνXx Hclosed Hlc Hbody HprojX Hwhole σν. split.
  - intros Hσν.
    destruct Hσν as [σxν [Hσxν Hσν_eq]].
    destruct Hσxν as [Hgraph Hρx].
    pose proof (tlet_result_graph_member_to_body_result_store
      X e1 e2 x ν w Hfreshx Hnudom Hinh σxν
      HxX Hxe2 HνXx Hclosed Hlc Hgraph) as Hstore.
    assert (Hdomρx : dom ρx = X ∪ {[x]}).
    {
      pose proof (wfworld_store_dom
        (res_restrict
          (tlet_result_graph_world_on X e1 e2 x ν w Hfreshx Hnudom Hinh)
          (X ∪ {[x]})) ρx Hproj) as Hdomρx.
      simpl in Hdomρx. unfold tlet_result_graph_raw_world_on in Hdomρx.
      simpl in Hdomρx. set_solver.
    }
    assert (Hρx_full :
      store_restrict σxν (X ∪ {[x]}) = store_restrict ρx (X ∪ {[x]})).
    {
      transitivity ρx.
      - rewrite <- Hdomρx. exact Hρx.
      - symmetry. apply store_restrict_idemp. rewrite Hdomρx. set_solver.
    }
    rewrite Hρx_full in Hstore.
    rewrite Hσν_eq in Hstore.
    exact Hstore.
  - intros Hstore.
    destruct Hproj as [σx0 [Hgraph0 Hρx0]].
    destruct (tlet_result_graph_world_on_elim
      X e1 e2 x ν w Hfreshx Hnudom Hinh σx0 Hgraph0)
      as [σ0 [vx0 [v0 [Hσ0 [Hσ0ν [Hsteps10 [Hsteps20 [Hvx0_stale [Hvx0_lc [Hv0_stale [Hv0_lc ->]]]]]]]]]]].
    assert (Hdomρx : dom ρx = X ∪ {[x]}).
    {
      pose proof (wfworld_store_dom
        (res_restrict
          (tlet_result_graph_world_on X e1 e2 x ν w Hfreshx Hnudom Hinh)
          (X ∪ {[x]})) ρx) as Hdom.
      specialize (Hdom (ex_intro _ (<[x := vx0]> σ0) (conj Hgraph0 Hρx0))).
      simpl in Hdom. unfold tlet_result_graph_raw_world_on in Hdom.
      simpl in Hdom. set_solver.
    }
    assert (Hρx_shape :
      ρx = <[x := vx0]> (store_restrict σ0 X)).
    {
      rewrite <- Hρx0.
      rewrite store_restrict_insert_fresh_union.
      - reflexivity.
      - eapply store_lookup_none_of_dom.
        + apply wfworld_store_dom. exact Hσ0.
        + exact Hfreshx.
      - exact HxX.
    }
    assert (HρxX : store_restrict ρx X = store_restrict σ0 X).
    {
      rewrite Hρx_shape.
      rewrite store_restrict_insert_notin by exact HxX.
      apply store_restrict_idemp. rewrite store_restrict_dom. set_solver.
    }
    assert (HρxXx : store_restrict ρx (X ∪ {[x]}) = ρx).
    { apply store_restrict_idemp. rewrite Hdomρx. set_solver. }
    rewrite HρxXx in Hstore.
    rewrite Hρx_shape in Hstore.
    destruct (expr_result_store_elim ν
      (subst_map (<[x := vx0]> (store_restrict σ0 X)) (e2 ^^ x)) σν Hstore)
      as [v [Hσν_store [Hv_stale [Hv_lc Hsteps_body]]]].
    assert (Hsteps2 :
      open_tm 0 vx0 (subst_map (store_restrict σ0 X) e2) →* tret v).
    {
      eapply (steps_msubst_open_body_result X σ0 e2 x vx0 v).
      - exact HxX.
      - exact Hxe2.
      - apply Hclosed. exact Hσ0.
      - exact Hvx0_stale.
      - exact Hvx0_lc.
      - apply Hlc. exact Hσ0.
      - exact Hsteps_body.
    }
    assert (Htlet_store :
      expr_result_store ν
        (subst_map (store_restrict ρx X) (tlete e1 e2)) σν).
    {
      rewrite HρxX.
      rewrite Hσν_store.
      eapply expr_result_store_let_intro; eauto.
    }
    pose proof (expr_result_in_world_complete
      (store_restrict ρx X) (tlete e1 e2) ν
      (res_fiber_from_projection w X (store_restrict ρx X) HprojX)
      σν Hwhole Htlet_store) as Hσν_w.
    destruct Hσν_w as [σbase [Hσbase Hσν_eq]].
    destruct Hσbase as [Hσbase Hσbase_X].
    assert (HdomρxX : dom (store_restrict ρx X) = X).
    { rewrite store_restrict_dom, Hdomρx. set_solver. }
    assert (Hσbase_restrict_X :
      store_restrict σbase X = store_restrict ρx X).
    { rewrite <- HdomρxX at 1. exact Hσbase_X. }
    assert (Hσbaseν : σbase !! ν = Some v).
    {
      assert (Hνlookup : σν !! ν = Some v).
      { rewrite Hσν_store, lookup_singleton, decide_True by reflexivity. reflexivity. }
      rewrite <- Hσν_eq in Hνlookup.
      apply store_restrict_lookup_some in Hνlookup as [_ Hlookup].
      exact Hlookup.
    }
    exists (<[x := vx0]> σbase). split.
    + split.
      * apply (tlet_result_graph_world_on_member
          X e1 e2 x ν w Hfreshx Hnudom Hinh σbase vx0 v).
        -- exact Hσbase.
        -- exact Hσbaseν.
        -- rewrite Hσbase_restrict_X, HρxX. exact Hsteps10.
        -- rewrite Hσbase_restrict_X, HρxX. exact Hsteps2.
        -- exact Hvx0_stale.
        -- exact Hvx0_lc.
        -- exact Hv_stale.
        -- exact Hv_lc.
      * replace (dom ρx) with (X ∪ {[x]}) by (symmetry; exact Hdomρx).
        rewrite store_restrict_insert_fresh_union.
        -- rewrite Hσbase_restrict_X.
           rewrite HρxX.
           symmetry. exact Hρx_shape.
        -- eapply store_lookup_none_of_dom.
           ++ apply wfworld_store_dom. exact Hσbase.
           ++ exact Hfreshx.
        -- exact HxX.
    + rewrite store_restrict_insert_singleton_ne by set_solver.
      exact Hσν_eq.
Qed.

(** Input-fiber exactness of the tlet graph.

    This is the companion check to [tlet_result_graph_body_fiber_exact].  If
    we project the graph only at the original input domain [X], then the
    remaining [ν]-fiber is exactly the result world of the whole
    [tlete e1 e2].  In other words, the graph has neither extra final results
    nor missing final results when viewed from the outside.

    This is the high-risk invariant needed by the generic expression-result
    transport used in the tlet proof: an arbitrary final result of the let
    expression can be represented in the same graph that also remembers the
    intermediate [x] result used by the body proof.

    Anti-slip rule: this theorem lives entirely below [denot_ty_on].  It should
    compose exact expression-result atoms and fibers; it must not prove
    separate over/under versions, and it must not use the shape of the final
    choice type. *)
Lemma tlet_result_graph_tlet_fiber_exact
    X e1 e2 x ν (w : WfWorld) Hfreshx Hnudom Hinh ρ Hproj :
  X ⊆ world_dom (w : World) →
  x ∉ X →
  ν ∉ X →
  (∀ σ, (w : World) σ → closed_env (store_restrict σ X)) →
  (∀ σ, (w : World) σ → lc_env (store_restrict σ X)) →
  (∀ σ vx,
    (w : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    stale vx = ∅ ∧ is_lc vx) →
  (∀ σ, (w : World) σ → body_tm (subst_map (store_restrict σ X) e2)) →
  ∀ HprojX : res_restrict w X (store_restrict ρ X),
  expr_result_in_world
    (store_restrict ρ X) (tlete e1 e2) ν
    (res_fiber_from_projection w X (store_restrict ρ X) HprojX) →
  expr_result_in_world
    (store_restrict ρ X) (tlete e1 e2) ν
    (res_fiber_from_projection
      (tlet_result_graph_world_on X e1 e2 x ν w Hfreshx Hnudom Hinh)
      X ρ Hproj).
Proof.
  intros HXdom HxX HνX Hclosed Hlc Hresult_closed Hbody HprojX Hwhole σν.
  split.
  - intros Hσν.
    destruct Hσν as [σx [Hσx Hσν_eq]].
    destruct Hσx as [Hgraph Hρ].
    pose proof (tlet_result_graph_member_to_tlet_result_store
      X e1 e2 x ν w Hfreshx Hnudom Hinh σx
      HxX HνX Hbody Hgraph) as Hstore.
    rewrite Hσν_eq in Hstore.
    assert (Hdomρ : dom ρ = X).
    {
      pose proof (wfworld_store_dom
        (res_restrict
          (tlet_result_graph_world_on X e1 e2 x ν w Hfreshx Hnudom Hinh)
          X) ρ Hproj) as Hdomρ.
      simpl in Hdomρ. unfold tlet_result_graph_raw_world_on in Hdomρ.
      simpl in Hdomρ. set_solver.
    }
    assert (HρX : store_restrict σx X = store_restrict ρ X).
    {
      transitivity ρ.
      - rewrite <- Hdomρ. exact Hρ.
      - symmetry. apply store_restrict_idemp. rewrite Hdomρ. set_solver.
    }
    rewrite HρX in Hstore. exact Hstore.
  - intros Hstore.
    pose proof (expr_result_in_world_complete
      (store_restrict ρ X) (tlete e1 e2) ν
      (res_fiber_from_projection w X (store_restrict ρ X) HprojX)
      σν Hwhole Hstore) as Hσν_w.
    destruct Hσν_w as [σbase [Hσbase Hσν_eq]].
    destruct Hσbase as [Hσbase Hσbase_X].
    destruct (expr_result_store_let_elim
      (store_restrict ρ X) e1 e2 ν σν Hstore)
      as [v [vx [Hσν_store [Hsteps1 Hsteps2]]]].
    destruct (expr_result_store_elim ν
      (subst_map (store_restrict ρ X) (tlete e1 e2)) σν Hstore)
      as [v' [Hσν_store' [Hv_stale [Hv_lc _]]]].
    assert (Hv' : v' = v).
    {
      assert (Hlookv : σν !! ν = Some v).
      { rewrite Hσν_store, lookup_singleton, decide_True by reflexivity. reflexivity. }
      assert (Hlookv' : σν !! ν = Some v').
      { rewrite Hσν_store', lookup_singleton, decide_True by reflexivity. reflexivity. }
      rewrite Hlookv in Hlookv'. inversion Hlookv'. reflexivity.
    }
    subst v'.
    assert (Hdomρ : dom ρ = X).
    {
      pose proof (wfworld_store_dom
        (res_restrict
          (tlet_result_graph_world_on X e1 e2 x ν w Hfreshx Hnudom Hinh)
          X) ρ Hproj) as Hdomρ.
      simpl in Hdomρ. unfold tlet_result_graph_raw_world_on in Hdomρ.
      simpl in Hdomρ. set_solver.
    }
    assert (HdomρX : dom (store_restrict ρ X) = X).
    { rewrite store_restrict_dom, Hdomρ. set_solver. }
    assert (Hσbase_restrict_X : store_restrict σbase X = store_restrict ρ X).
    {
      rewrite <- HdomρX at 1. exact Hσbase_X.
    }
    assert (Hσbaseν : σbase !! ν = Some v).
    {
      assert (Hνlookup : σν !! ν = Some v).
      { rewrite Hσν_store, lookup_singleton, decide_True by reflexivity. reflexivity. }
      rewrite <- Hσν_eq in Hνlookup.
      apply store_restrict_lookup_some in Hνlookup as [_ Hlookup].
      exact Hlookup.
    }
    pose proof (Hresult_closed σbase vx Hσbase
      ltac:(rewrite Hσbase_restrict_X; exact Hsteps1)) as [Hvx_stale Hvx_lc].
    exists (<[x := vx]> σbase). split.
    + split.
      * apply (tlet_result_graph_world_on_member
          X e1 e2 x ν w Hfreshx Hnudom Hinh σbase vx v).
        -- exact Hσbase.
        -- exact Hσbaseν.
        -- rewrite Hσbase_restrict_X. exact Hsteps1.
        -- rewrite Hσbase_restrict_X. exact Hsteps2.
        -- exact Hvx_stale.
        -- exact Hvx_lc.
        -- exact Hv_stale.
        -- exact Hv_lc.
      * replace (dom ρ) with X by (symmetry; exact Hdomρ).
        rewrite store_restrict_insert_notin by exact HxX.
        rewrite Hσbase_restrict_X.
        apply store_restrict_idemp. rewrite Hdomρ. set_solver.
    + rewrite store_restrict_insert_singleton_ne by set_solver.
      exact Hσν_eq.
Qed.

(** Completeness direction from a whole-let result store back into the graph.

    Anti-slip rule: use the already-proved whole-let fiber exactness rather
    than duplicating its proof or branching on a result type.  This lemma is
    the projection/completeness half of [tlet_result_graph_tlet_fiber_exact]. *)
Lemma tlet_result_store_to_graph_member
    X e1 e2 x ν (w : WfWorld) Hfreshx Hnudom Hinh ρ
    (Hproj : res_restrict
      (tlet_result_graph_world_on X e1 e2 x ν w Hfreshx Hnudom Hinh) X ρ)
    (HprojX : res_restrict w X (store_restrict ρ X)) σν :
  X ⊆ world_dom (w : World) →
  x ∉ X →
  ν ∉ X →
  (∀ σ, (w : World) σ → closed_env (store_restrict σ X)) →
  (∀ σ, (w : World) σ → lc_env (store_restrict σ X)) →
  (∀ σ vx,
    (w : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    stale vx = ∅ ∧ is_lc vx) →
  (∀ σ, (w : World) σ → body_tm (subst_map (store_restrict σ X) e2)) →
  expr_result_in_world
    (store_restrict ρ X) (tlete e1 e2) ν
    (res_fiber_from_projection w X (store_restrict ρ X) HprojX) →
  expr_result_store ν (subst_map (store_restrict ρ X) (tlete e1 e2)) σν →
  ∃ σxν,
    (tlet_result_graph_world_on X e1 e2 x ν w Hfreshx Hnudom Hinh : World) σxν ∧
    store_restrict σxν (dom ρ) = ρ ∧
    store_restrict σxν {[ν]} = σν.
Proof.
  intros HXdom HxX HνX Hclosed Hlc Hresult_closed Hbody Hwhole Hstore.
  pose proof (tlet_result_graph_tlet_fiber_exact
    X e1 e2 x ν w Hfreshx Hnudom Hinh ρ Hproj
    HXdom HxX HνX Hclosed Hlc Hresult_closed Hbody
    HprojX Hwhole σν) as [_ Hcomplete].
  destruct (Hcomplete Hstore) as [σxν [[Hgraph Hρ] Hν]].
  exists σxν. repeat split; assumption.
Qed.

(** The graph extends the ordinary let-result world when the body is total.

    This is the proof-side bridge that lets a body denotation obtained on
    [let_result_world_on e1 x w] be used on the richer graph world by
    Kripke monotonicity.  The bridge is not automatic: the graph contains a
    store for [(σ, vx)] only when [e2] produces the result already stored in
    [σ]'s [ν] coordinate.  Therefore the premise below is intentionally
    stronger than plain body totality: it records exact paired agreement
    between the intermediate result [vx] and the existing result coordinate
    [ν].

    If this lemma were false, the graph would be too small to transport the
    body proof, and the tlet case could not be proved just from exact result
    atoms.

    Anti-slip rule: this is a Kripke/resource bridge between two proof worlds.
    It may use totality and graph exactness, but it must not become a
    constructor-specific proof about [τ], [CTOver], or [CTUnder]. *)
Lemma let_result_world_on_le_tlet_result_graph
    X e1 e2 x ν (w : WfWorld)
    Hfresh Hresult Hfreshx Hnudom Hinh :
  (∀ σ vx,
    (w : World) σ →
    subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx →
    ∀ v,
      σ !! ν = Some v →
      open_tm 0 vx (subst_map (store_restrict σ X) e2) →* tret v ∧
      stale vx = ∅ ∧
      is_lc vx ∧
      stale v = ∅ ∧
      is_lc v) →
  let_result_world_on e1 x w Hfresh Hresult ⊑
    tlet_result_graph_world_on X e1 e2 x ν w Hfreshx Hnudom Hinh.
Proof.
Admitted.

(** Extract the graph-building body totality obligation from the ordinary
    totality statement on [let_result_world_on].

    [expr_total_on (X ∪ {[x]}) (e2 ^^ x)] talks about substituting the whole
    projected store of [<[x := vx]> σ] into the opened body.  The graph, on the
    other hand, stores the operational edge in the normalized form
    [open_tm 0 vx (subst_map (store_restrict σ X) e2) →* tret v].  This lemma is
    exactly that conversion, plus the regularity facts needed to make the graph
    world well-formed.

    This is a high-risk bridge because any mismatch between the LN opening
    convention and the store-projection convention shows up here before the
    final tlet theorem. *)
Lemma body_total_on_let_result_world_to_graph_obligation
    X e1 e2 x (w : WfWorld) Hfresh Hresult :
  x ∉ X →
  x ∉ fv_tm e2 →
  (∀ σ, (w : World) σ → closed_env (store_restrict σ X)) →
  (∀ σ, (w : World) σ → lc_env (store_restrict σ X)) →
  (∀ σ vx,
    (w : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    stale vx = ∅ ∧ is_lc vx) →
  (∀ σ, (w : World) σ → body_tm (subst_map (store_restrict σ X) e2)) →
  (∀ σx v,
    (let_result_world_on e1 x w Hfresh Hresult : World) σx →
    subst_map (store_restrict σx (X ∪ {[x]})) (e2 ^^ x) →* tret v →
    stale v = ∅ ∧ is_lc v) →
  expr_total_on (X ∪ {[x]}) (e2 ^^ x)
    (let_result_world_on e1 x w Hfresh Hresult) →
  ∀ σ vx,
    (w : World) σ →
    subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx →
    ∃ v,
      open_tm 0 vx (subst_map (store_restrict σ X) e2) →* tret v ∧
      stale vx = ∅ ∧
      is_lc vx ∧
      stale v = ∅ ∧
      is_lc v.
Proof.
Admitted.

(** Transport a body formula from the ordinary let-result world to the graph.

    Anti-slip rule: this should be a generic Kripke monotonicity application
    after proving [let_result_world_on_le_tlet_result_graph].  The formula [φ]
    is arbitrary; do not inspect it as if it were generated by a particular
    type constructor. *)
Lemma let_result_body_model_to_tlet_graph
    X e1 e2 x ν (w : WfWorld)
    Hfresh Hresult Hfreshx Hnudom Hinh (φ : FormulaQ) :
  (∀ σ vx,
    (w : World) σ →
    subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx →
    ∀ v,
      σ !! ν = Some v →
      open_tm 0 vx (subst_map (store_restrict σ X) e2) →* tret v ∧
      stale vx = ∅ ∧
      is_lc vx ∧
      stale v = ∅ ∧
      is_lc v) →
  let_result_world_on e1 x w Hfresh Hresult ⊨ φ →
  tlet_result_graph_world_on X e1 e2 x ν w Hfreshx Hnudom Hinh ⊨ φ.
Proof.
  intros Hbody_paired Hmodel.
  eapply res_models_kripke.
  - eapply let_result_world_on_le_tlet_result_graph.
    exact Hbody_paired.
  - exact Hmodel.
Qed.
