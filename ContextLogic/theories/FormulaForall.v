(** * ContextLogic.FormulaForall

    Derived proof principles for forall under the extension-based formula
    semantics. *)

From ContextLogic Require Import FormulaSemantics FormulaTactics FormulaConnectivesCore FormulaImpl FormulaWand.
From ContextAlgebra Require Import ResourceInterface ResourceCompat.

Section FormulaForall.

Context {V : Type} `{ValueSig V}.

Local Notation WorldT := (World (V := V)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation FormulaT := (Formula (V := V)) (only parsing).
Local Notation "m ⊨ φ" := (res_models m φ)
  (at level 70, format "m  ⊨  φ").

Definition res_extend_by_input_widened_to
    (m : WfWorldT) (F : fiber_extension) (X : aset) (my : WfWorldT) : Prop :=
  ∃ Fwide : fiber_extension,
    F ~>i Fwide ∧
    ext_in Fwide = X ∧
    res_extend_by m Fwide my.

Lemma res_models_forall_intro (m : WfWorldT) (φ : FormulaT) :
  formula_scoped_in_world m (FForall φ) →
  (∃ L : aset,
    ∀ y : atom, y ∉ L →
    ∀ F : fiber_extension,
      ext_in F = formula_fv φ →
      ext_out F = {[y]} →
      ∀ my : WfWorldT,
        res_extend_by m F my →
        my ⊨ formula_open 0 y φ) →
  m ⊨ FForall φ.
Proof.
  unfold res_models.
  simpl. intros Hscope [L Hforall]. split; [exact Hscope |].
  exists L. intros y Hy F HFin HFout my Hext.
  pose proof (Hforall y Hy F HFin HFout my Hext) as Hbody.
  models_fuel_irrel Hbody.
Qed.

Lemma res_models_forall_iff (m : WfWorldT) (φ : FormulaT) :
  formula_scoped_in_world m (FForall φ) →
  (m ⊨ FForall φ ↔
    ∃ L : aset,
      ∀ y : atom, y ∉ L →
      ∀ F : fiber_extension,
        ext_in F = formula_fv φ →
        ext_out F = {[y]} →
        ∀ my : WfWorldT,
          res_extend_by m F my →
          my ⊨ formula_open 0 y φ).
Proof.
  intros Hscope. split.
  - unfold res_models. simpl.
    intros [_ [L Hforall]]. exists L.
    intros y Hy F HFin HFout my Hext.
    specialize (Hforall y Hy F HFin HFout my Hext).
    unfold res_models. models_fuel_irrel Hforall.
  - intros Hforall.
    eapply res_models_forall_intro; eauto.
Qed.

Lemma res_models_forall_map_subset_fv
    (m : WfWorldT) (φ ψ : FormulaT) :
  formula_fv ψ ⊆ formula_fv φ →
  formula_scoped_in_world m (FForall ψ) →
  (∃ L : aset,
    ∀ y : atom, y ∉ L →
    ∀ F my,
      ext_in F = formula_fv ψ →
      ext_out F = {[y]} →
      res_extend_by_input_widened_to m F (formula_fv φ) my →
      my ⊨ formula_open 0 y φ →
      my ⊨ formula_open 0 y ψ) →
  m ⊨ FForall φ →
  m ⊨ FForall ψ.
Proof.
  intros Hsub Hscope Hmap Hforall.
  eapply res_models_forall_intro; [exact Hscope |].
  pose proof (res_models_fuel_scoped _ _ _ Hforall) as Hφscope.
  pose proof (proj1 (res_models_forall_iff m φ Hφscope) Hforall) as [L Hbody].
  destruct Hmap as [Lmap Hmap].
  exists (L ∪ Lmap ∪ world_dom (m : WorldT)).
  intros y Hy F HFin HFout my Hext.
  assert (HyBody : y ∉ L) by set_solver.
  assert (HyMap : y ∉ Lmap) by set_solver.
  assert (Hym : y ∉ world_dom (m : WorldT)) by set_solver.
  assert (Hin : ext_in F ⊆ formula_fv φ) by (rewrite HFin; exact Hsub).
  assert (Hdisj : formula_fv φ ## ext_out F).
  {
    rewrite HFout.
    unfold formula_scoped_in_world in Hφscope. set_solver.
  }
  pose (Fφ := fiber_extension_input_widen F (formula_fv φ) Hin Hdisj).
  assert (Hwid : F ~>i Fφ)
    by apply fiber_extension_input_widen_to_construct.
  assert (HFinφ : ext_in Fφ = formula_fv φ) by reflexivity.
  assert (HFoutφ : ext_out Fφ = {[y]}).
  {
    rewrite (input_widen_out _ _ Hwid). exact HFout.
  }
  assert (Hextφ : res_extend_by m Fφ my).
  {
    apply (proj1 (res_extend_by_input_widen_to_iff m F Fφ my Hwid
      ltac:(rewrite HFinφ; exact Hφscope))).
    exact Hext.
  }
  eapply (Hmap y HyMap F my);
    [exact HFin | exact HFout | |].
  - exists Fφ. split; [exact Hwid | split; [exact HFinφ | exact Hextφ]].
  - eapply (Hbody y HyBody Fφ); eauto.
Qed.

Lemma res_models_forall_map_same_fv
    (m : WfWorldT) (φ ψ : FormulaT) :
  formula_fv φ = formula_fv ψ →
  formula_scoped_in_world m (FForall ψ) →
  (∃ L : aset,
    ∀ y : atom, y ∉ L →
    ∀ F my,
      ext_in F = formula_fv φ →
      ext_out F = {[y]} →
      res_extend_by m F my →
      my ⊨ formula_open 0 y φ →
      my ⊨ formula_open 0 y ψ) →
  m ⊨ FForall φ →
  m ⊨ FForall ψ.
Proof.
  intros Hfv Hscope [L Hmap] Hforall.
  eapply res_models_forall_map_subset_fv; [| exact Hscope | | exact Hforall].
  - rewrite <- Hfv. reflexivity.
  - exists L. intros y Hy F my _ HFout [Fφ [Hwid [HFinφ Hext]]] Hφ.
    eapply Hmap; [exact Hy | exact HFinφ | | exact Hext | exact Hφ].
    rewrite (input_widen_out _ _ Hwid). exact HFout.
Qed.

Lemma res_models_forall_map
    (m : WfWorldT) (φ ψ : FormulaT) :
  formula_fv φ = formula_fv ψ →
  formula_scoped_in_world m (FForall ψ) →
  (∃ L : aset,
    ∀ y : atom, y ∉ L →
    ∀ (F : fiber_extension (V := V)) (my : WfWorldT),
      ext_in F = formula_fv φ →
      ext_out F = {[y]} →
      res_extend_by m F my →
      my ⊨ formula_open 0 y φ →
      my ⊨ formula_open 0 y ψ) →
  m ⊨ FForall φ →
  m ⊨ FForall ψ.
Proof.
  apply res_models_forall_map_same_fv.
Qed.

Lemma res_models_forall_congr_same_fv
    (m : WfWorldT) (φ ψ : FormulaT) :
  formula_fv φ = formula_fv ψ →
  formula_scoped_in_world m (FForall φ) →
  formula_scoped_in_world m (FForall ψ) →
  (∃ L : aset,
    ∀ y : atom, y ∉ L →
    ∀ (F : fiber_extension (V := V)) (my : WfWorldT),
      ext_in F = formula_fv φ →
      ext_out F = {[y]} →
      res_extend_by m F my →
      (my ⊨ formula_open 0 y φ ↔
	     my ⊨ formula_open 0 y ψ)) →
  (m ⊨ FForall φ ↔ m ⊨ FForall ψ).
Proof.
  intros Hfv Hφscope Hψscope [Liff Hiff]. split.
  - intros Hforall.
    eapply res_models_forall_map_same_fv; [exact Hfv | exact Hψscope | | exact Hforall].
    exists Liff. intros y Hy F my HFin HFout Hext Hφ.
    apply (proj1 (Hiff y Hy F my HFin HFout Hext)). exact Hφ.
  - intros Hforall.
    eapply res_models_forall_map_same_fv; [symmetry; exact Hfv | exact Hφscope | | exact Hforall].
    exists Liff. intros y Hy F my HFin HFout Hext Hψ.
    apply (proj2 (Hiff y Hy F my ltac:(rewrite Hfv; exact HFin) HFout Hext)).
    exact Hψ.
Qed.

Lemma res_models_forall_transport
    (m n : WfWorldT) (φ ψ : FormulaT) :
  formula_fv ψ ⊆ formula_fv φ →
  formula_scoped_in_world n (FForall ψ) →
  (∃ L : aset,
    ∀ y : atom, y ∉ L →
    ∀ F my ny,
      ext_in F = formula_fv ψ →
      ext_out F = {[y]} →
      res_extend_by_input_widened_to m F (formula_fv φ) my →
      res_extend_by n F ny →
	      my ⊨ formula_open 0 y φ →
	      ny ⊨ formula_open 0 y ψ) →
  m ⊨ FForall φ →
  n ⊨ FForall ψ.
Proof.
  intros Hsub Hψscope Htransport Hforall.
  eapply res_models_forall_intro; [exact Hψscope |].
  pose proof (res_models_fuel_scoped _ _ _ Hforall) as Hφscope.
  pose proof (proj1 (res_models_forall_iff m φ Hφscope) Hforall)
    as [L Hbody].
  destruct Htransport as [Ltransport Htransport].
  exists (L ∪ Ltransport ∪ world_dom (m : WorldT)).
  intros y Hy F HFin HFout ny Hny.
  assert (HyL : y ∉ L) by set_solver.
  assert (HyTransport : y ∉ Ltransport) by set_solver.
  assert (Hym : y ∉ world_dom (m : WorldT)) by set_solver.
  assert (Hin : ext_in F ⊆ formula_fv φ) by (rewrite HFin; exact Hsub).
  assert (Hdisj : formula_fv φ ## ext_out F).
  {
    rewrite HFout.
    unfold formula_scoped_in_world in Hφscope. set_solver.
  }
  pose (Fφ := fiber_extension_input_widen F (formula_fv φ) Hin Hdisj).
  assert (Hwid : F ~>i Fφ)
    by apply fiber_extension_input_widen_to_construct.
  assert (HFinφ : ext_in Fφ = formula_fv φ) by reflexivity.
  assert (HFoutφ : ext_out Fφ = {[y]}).
  {
    rewrite (input_widen_out _ _ Hwid). exact HFout.
  }
  assert (Happ : extension_applicable Fφ m).
  {
    constructor.
    - change (ext_in Fφ ⊆ world_dom (m : WorldT)).
      rewrite HFinφ. exact Hφscope.
    - change (ext_out Fφ ## world_dom (m : WorldT)).
      rewrite HFoutφ. set_solver.
  }
  destruct (res_extend_by_exists m Fφ Happ) as [my Hmy].
  eapply (Htransport y HyTransport F my ny);
    [exact HFin | exact HFout | | exact Hny |].
  - exists Fφ. split; [exact Hwid | split; [exact HFinφ | exact Hmy]].
  - eapply (Hbody y HyL Fφ); eauto.
Qed.

Lemma res_models_forall_rev
    (m : WfWorldT) (φ : FormulaT) :
  m ⊨ FForall φ ->
  exists L : aset,
    forall y : atom, y ∉ L ->
      forall my : WfWorldT,
        world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
        res_restrict my (world_dom (m : WorldT)) = m ->
        my ⊨ formula_open 0 y φ.
Proof.
  intros Hforall.
  pose proof (res_models_scoped m (FForall φ) Hforall) as Hscope.
  pose proof (proj1 (res_models_forall_iff m φ Hscope) Hforall)
    as [L Hbody].
  exists (L ∪ world_dom (m : WorldT)).
  intros y Hy my Hdom Hrestrict.
  assert (HyL : y ∉ L) by set_solver.
  assert (Hym : y ∉ world_dom (m : WorldT)) by set_solver.
  assert (Hfv : formula_fv φ ⊆ world_dom (m : WorldT)).
  { exact Hscope. }
  destruct (forall_extension_from_world_dom_projection
    m my (formula_fv φ) y Hfv Hym Hdom Hrestrict)
    as [F [n [HFin [HFout [Hext Hproj]]]]].
  pose proof (Hbody y HyL F HFin HFout n Hext) as Hn.
  assert (Hopen_fv :
      formula_fv (formula_open 0 y φ) ⊆ formula_fv φ ∪ {[y]}).
  { apply formula_open_fv_subset. }
  apply (proj2 (res_models_minimal_on (formula_fv φ ∪ {[y]}) my
    (formula_open 0 y φ) Hopen_fv)).
  rewrite <- Hproj.
  apply (proj1 (res_models_minimal_on (formula_fv φ ∪ {[y]}) n
    (formula_open 0 y φ) Hopen_fv)).
  exact Hn.
Qed.

Lemma res_models_forall_rev_intro
    (m : WfWorldT) (φ : FormulaT) :
  formula_scoped_in_world m (FForall φ) ->
  (exists L : aset,
    forall y : atom, y ∉ L ->
      forall my : WfWorldT,
        world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
        res_restrict my (world_dom (m : WorldT)) = m ->
        my ⊨ formula_open 0 y φ) ->
  m ⊨ FForall φ.
Proof.
  intros Hscope [L Hfull].
  eapply res_models_forall_intro; [exact Hscope |].
  exists L. intros y Hy F HFin HFout my Hext.
  eapply Hfull; [exact Hy | |].
  - pose proof (res_extend_by_dom m F my Hext) as Hdom.
    unfold ext_out in HFout.
    rewrite Hdom, HFout. reflexivity.
  - eapply res_extend_by_restrict_base; exact Hext.
Qed.

Lemma res_models_forall_full_world_iff
    (m : WfWorldT) (φ : FormulaT) :
  formula_scoped_in_world m (FForall φ) ->
  (m ⊨ FForall φ <->
    exists L : aset,
      forall y : atom, y ∉ L ->
        forall my : WfWorldT,
          world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
          res_restrict my (world_dom (m : WorldT)) = m ->
          my ⊨ formula_open 0 y φ).
Proof.
  intros Hscope. split.
  - apply res_models_forall_rev.
  - apply res_models_forall_rev_intro. exact Hscope.
Qed.

Lemma res_models_forall_full_world_map
    (m : WfWorldT) (φ ψ : FormulaT) :
  (** This is the "full-world" view of [FForall].  The primitive semantics
      only asks extensions to read [formula_fv φ], but nested denotation
      transports often open a formula under several binders and then need to
      compare witnesses whose input domain is the whole current world.  The
      proof converts [FForall φ] to that full-world form with
      [res_models_forall_rev], maps the opened body there, and packages the
      result back with [res_models_forall_rev_intro].  This is intentionally
      independent of any [formula_fv φ = formula_fv ψ] side condition; the
      world-domain restriction/restrict-back hypotheses carry the alignment. *)
  formula_scoped_in_world m (FForall ψ) ->
  (∃ L : aset,
    forall y : atom, y ∉ L ->
      forall my : WfWorldT,
        world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
        res_restrict my (world_dom (m : WorldT)) = m ->
        my ⊨ formula_open 0 y φ ->
        my ⊨ formula_open 0 y ψ) ->
  m ⊨ FForall φ ->
  m ⊨ FForall ψ.
Proof.
  intros Hψscope [Lmap Hmap] Hφ.
  pose proof (res_models_forall_rev m φ Hφ) as [Lφ Hφfull].
  eapply res_models_forall_rev_intro; [exact Hψscope |].
  exists (Lmap ∪ Lφ). intros y Hy my Hdom Hrestrict.
  eapply Hmap; [set_solver | exact Hdom | exact Hrestrict |].
  eapply Hφfull; [set_solver | exact Hdom | exact Hrestrict].
Qed.

Lemma res_models_forall_ext_transport_by_extension
    (m mx : WfWorldT) (F : fiber_extension (V := V)) (φ ψ : FormulaT) :
  formula_scoped_in_world m (FForall ψ) →
  res_extend_by m F mx →
  (∃ L : aset,
    ∀ y : atom, y ∉ L →
    ∀ Fy my myx,
      ext_in Fy = formula_fv ψ →
      ext_out Fy = {[y]} →
      res_extend_by m Fy my →
      res_extend_by my F myx →
      myx ⊨ formula_open 0 y φ →
      my ⊨ formula_open 0 y ψ) →
  mx ⊨ FForall φ →
  m ⊨ FForall ψ.
Proof.
  intros Hψscope HmF [Ltransport Htransport] Hmx_forall.
  eapply res_models_forall_intro; [exact Hψscope |].
  pose proof (res_models_forall_rev mx φ Hmx_forall) as [Lφ Hφrev].
  exists (Ltransport ∪ Lφ ∪ world_dom (mx : WorldT)).
  intros y Hy Fy HFin HFout my HmFy.
  assert (HyTransport : y ∉ Ltransport) by set_solver.
  assert (Hyφ : y ∉ Lφ) by set_solver.
  assert (Hymx : y ∉ world_dom (mx : WorldT)) by set_solver.
  assert (HFinFy_mx : ext_in Fy ⊆ world_dom (mx : WorldT)).
  {
    pose proof (res_extend_by_dom m F mx HmF) as Hdom_mx.
    unfold formula_scoped_in_world in Hψscope.
    rewrite HFin. set_solver.
  }
  destruct (res_extend_by_commute_exists_right m mx my F Fy HmF HmFy
    HFinFy_mx ltac:(rewrite HFout; set_solver)) as [myx [HmyF HmxFy]].
  assert (Hdom_myx : world_dom (myx : WorldT) =
      world_dom (mx : WorldT) ∪ {[y]}).
  {
    pose proof (res_extend_by_dom mx Fy myx HmxFy) as Hdom.
    unfold ext_out in HFout.
    rewrite Hdom, HFout. reflexivity.
  }
  assert (Hrestrict_myx : res_restrict myx (world_dom (mx : WorldT)) = mx).
  { eapply res_extend_by_restrict_base; exact HmxFy. }
  pose proof (Hφrev y Hyφ myx Hdom_myx Hrestrict_myx) as Hmyxφ.
  eapply Htransport; eauto.
Qed.

Lemma res_models_forall_ext_transport
    (m mx : WfWorldT) (F : fiber_extension (V := V)) (φ ψ : FormulaT) :
  formula_scoped_in_world m (FForall ψ) →
  res_extend_by m F mx →
  (∃ L : aset,
    ∀ y : atom, y ∉ L →
    ∀ my myx,
      m ⊑ my ->
      world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
      res_extend_by my F myx →
      myx ⊨ formula_open 0 y φ →
      my ⊨ formula_open 0 y ψ) →
  mx ⊨ FForall φ →
  m ⊨ FForall ψ.
Proof.
  intros Hψscope HmF [L Htransport] Hmx.
  eapply res_models_forall_ext_transport_by_extension; eauto.
  exists L. intros y Hy Fy my myx HFin HFout HmFy HmyF Hmyxφ.
  eapply Htransport; eauto.
  - eapply res_extend_by_le; exact HmFy.
  - pose proof (res_extend_by_dom m Fy my HmFy) as Hdom.
    unfold ext_out in HFout.
    rewrite Hdom, HFout. reflexivity.
Qed.

End FormulaForall.
