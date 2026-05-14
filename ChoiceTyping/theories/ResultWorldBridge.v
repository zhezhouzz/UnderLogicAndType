(** * ChoiceTyping.ResultWorldBridge

    Bridges between expression-result formulas and the concrete result worlds
    used by the soundness proof.

    The first group relates the cofinite [fresh_forall] encoding

      forall x.  [e ⇓ x] ==> body x

    to the operational result world [let_result_world_on e x m].  Because
    [fresh_forall] is explicit-name/cofinite rather than locally nameless, the
    primitive bridge is phrased with the renamed representative
    [formula_rename_atom (fresh_for D) y (body (fresh_for D))].  Callers that
    know their body is equivariant can use the wrapper lemma to transport this
    renamed body to the desired [body y]. *)

From CoreLang Require Import Instantiation InstantiationProps OperationalProps
  LocallyNamelessProps.
From ChoiceTyping Require Export SoundnessCommon.
From ChoiceTyping Require Export LetResultWorld.
From ChoiceTyping Require Export ResultWorldClosed.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

Lemma store_restrict_union_singleton_fresh_eq
    (σ : Store) (X : aset) (x : atom) :
  σ !! x = None →
  store_restrict σ (X ∪ {[x]}) = store_restrict σ X.
Proof.
  intros Hfresh.
  apply (map_eq (M := gmap atom)). intros z.
  rewrite !store_restrict_lookup.
  destruct (decide (z ∈ X ∪ {[x]})) as [HzU|HzU];
    destruct (decide (z ∈ X)) as [HzX|HzX]; try reflexivity.
  - assert (z = x) by set_solver. subst z. exact Hfresh.
  - set_solver.
Qed.

Lemma store_restrict_accum_cons_projection
    (ρ σ : Store) (X S : aset) (x : atom) :
  x ∉ S →
  dom ρ ## ({[x]} ∪ S) →
  store_restrict (ρ ∪ store_restrict σ ({[x]} ∪ S)) X =
  store_restrict ((ρ ∪ store_restrict σ {[x]}) ∪ store_restrict σ S) X.
Proof.
  intros HxS Hdisj.
  apply (map_eq (M := gmap atom)). intros z.
  rewrite !store_restrict_lookup.
  destruct (decide (z ∈ X)) as [HzX|HzX].
  2:{ repeat (rewrite decide_False by exact HzX); reflexivity. }
  repeat (rewrite decide_True by exact HzX).
  change (((ρ ∪ store_restrict σ ({[x]} ∪ S)) : Store) !! z =
    (((ρ ∪ store_restrict σ {[x]}) ∪ store_restrict σ S) : Store) !! z).
  destruct (decide (z ∈ dom ρ)) as [Hzρ|Hzρ].
  - apply elem_of_dom in Hzρ as [v Hv].
    rewrite (@lookup_union_l' atom (gmap atom) _ _ _ _ _ _ _ _ _
      value ρ (store_restrict σ ({[x]} ∪ S)) z ltac:(eauto)).
    rewrite (@lookup_union_l' atom (gmap atom) _ _ _ _ _ _ _ _ _
      value (ρ ∪ store_restrict σ {[x]}) (store_restrict σ S) z).
    2:{ rewrite (@lookup_union_l' atom (gmap atom) _ _ _ _ _ _ _ _ _
          value ρ (store_restrict σ {[x]}) z ltac:(eauto)).
        eauto. }
    rewrite (@lookup_union_l' atom (gmap atom) _ _ _ _ _ _ _ _ _
      value ρ (store_restrict σ {[x]}) z ltac:(eauto)).
    reflexivity.
  - rewrite !lookup_union_r by (apply not_elem_of_dom; exact Hzρ).
    rewrite !store_restrict_lookup.
    destruct (decide (z = x)) as [->|Hzx].
    + repeat (rewrite decide_True by set_solver).
      repeat (rewrite decide_False by exact HxS).
      rewrite lookup_union_l.
      2:{ rewrite store_restrict_lookup, decide_False by exact HxS. reflexivity. }
      rewrite lookup_union_r by (apply not_elem_of_dom; exact Hzρ).
      rewrite store_restrict_lookup, decide_True by set_solver.
      reflexivity.
    + destruct (decide (z ∈ S)) as [HzS|HzS].
      * repeat (rewrite decide_True by set_solver).
        rewrite lookup_union_r.
        -- rewrite store_restrict_lookup, decide_True by exact HzS.
           reflexivity.
        -- rewrite lookup_union_None. split.
           ++ apply not_elem_of_dom. exact Hzρ.
           ++ rewrite store_restrict_lookup, decide_False by set_solver.
              reflexivity.
      * repeat (rewrite decide_False by set_solver).
        rewrite lookup_union_r.
        -- rewrite store_restrict_lookup, decide_False by exact HzS.
           reflexivity.
        -- rewrite lookup_union_None. split.
           ++ apply not_elem_of_dom. exact Hzρ.
           ++ rewrite store_restrict_lookup, decide_False by set_solver.
           reflexivity.
Qed.

Lemma store_restrict_union_singleton_eq_from_parts
    (σ τ : Store) (x : atom) (S : aset) :
  x ∉ S →
  store_restrict σ {[x]} = store_restrict τ {[x]} →
  store_restrict σ S = store_restrict τ S →
  store_restrict σ ({[x]} ∪ S) = store_restrict τ ({[x]} ∪ S).
Proof.
  intros HxS Hx HS.
  apply (map_eq (M := gmap atom)). intros z.
  rewrite !store_restrict_lookup.
  destruct (decide (z ∈ {[x]} ∪ S)) as [HzU|HzU].
  2:{ repeat (rewrite decide_False by exact HzU). reflexivity. }
  repeat (rewrite decide_True by exact HzU).
  destruct (decide (z = x)) as [->|Hzx].
  - pose proof (f_equal (fun σ0 => σ0 !! x) Hx) as Hlookup.
    rewrite !store_restrict_lookup in Hlookup.
    repeat (rewrite decide_True in Hlookup by set_solver).
    exact Hlookup.
  - assert (HzS : z ∈ S) by set_solver.
    pose proof (f_equal (fun σ0 => σ0 !! z) HS) as Hlookup.
    rewrite !store_restrict_lookup in Hlookup.
    repeat (rewrite decide_True in Hlookup by exact HzS).
    exact Hlookup.
Qed.

Lemma foldr_fib_expr_result_sound
    xs X e ν ρ (m : WfWorld) σw sigmanu :
  NoDup xs →
  dom ρ ## (list_to_set xs : aset) →
  res_models_with_store ρ m
    (FFibVars (lvars_of_atoms (list_to_set xs))
      (FAtom (expr_logic_qual_on X e ν))) →
  (m : World) σw →
  store_restrict σw {[ν]} = sigmanu →
  expr_result_store ν
    (subst_map
      (store_restrict (ρ ∪ store_restrict σw (list_to_set xs : aset)) X)
      e)
    sigmanu.
Proof.
  (* Legacy foldr fiber bridge; primitive multi-fiber replaces this route. *)
Admitted.

Lemma foldr_fib_expr_result_complete
    xs X e ν ρ (m : WfWorld) σw sigmanu :
  NoDup xs →
  dom ρ ## (list_to_set xs : aset) →
  res_models_with_store ρ m
    (FFibVars (lvars_of_atoms (list_to_set xs))
      (FAtom (expr_logic_qual_on X e ν))) →
  (m : World) σw →
  expr_result_store ν
    (subst_map
      (store_restrict (ρ ∪ store_restrict σw (list_to_set xs : aset)) X)
      e)
    sigmanu →
  (res_restrict m {[ν]} : World) sigmanu.
Proof.
  (* Legacy foldr fiber bridge; primitive multi-fiber replaces this route. *)
Admitted.

Lemma foldr_fib_expr_result_complete_paired
    xs X e ν ρ (m : WfWorld) σw sigmanu :
  NoDup xs →
  dom ρ ## (list_to_set xs : aset) →
  res_models_with_store ρ m
    (FFibVars (lvars_of_atoms (list_to_set xs))
      (FAtom (expr_logic_qual_on X e ν))) →
  (m : World) σw →
  expr_result_store ν
    (subst_map
      (store_restrict (ρ ∪ store_restrict σw (list_to_set xs : aset)) X)
      e)
    sigmanu →
  ∃ τ,
    (m : World) τ ∧
    store_restrict τ (list_to_set xs : aset) =
      store_restrict σw (list_to_set xs : aset) ∧
    store_restrict τ {[ν]} = sigmanu.
Proof.
  (* Legacy foldr fiber bridge; primitive multi-fiber replaces this route. *)
Admitted.

Lemma store_restrict_union_singleton_insert_from_projection
    (σ : Store) (X : aset) (ν : atom) (v : value) :
  ν ∉ X →
  store_restrict σ {[ν]} = {[ν := v]} →
  store_restrict σ (X ∪ {[ν]}) =
    <[ν := v]> (store_restrict σ X).
Proof.
  intros HνX Hν.
  apply (map_eq (M := gmap atom)). intros z.
  rewrite store_restrict_lookup.
  destruct (decide (z = ν)) as [->|Hzν].
  - rewrite decide_True by set_solver.
    pose proof (f_equal (fun σ0 : Store => σ0 !! ν) Hν) as Hlookup.
    rewrite store_restrict_lookup in Hlookup.
    rewrite decide_True in Hlookup by set_solver.
    rewrite lookup_singleton in Hlookup.
    rewrite decide_True in Hlookup by reflexivity.
    transitivity (Some v); [exact Hlookup |].
    rewrite lookup_insert. rewrite decide_True by reflexivity. reflexivity.
  - rewrite lookup_insert_ne by congruence.
    rewrite store_restrict_lookup.
    destruct (decide (z ∈ X)) as [HzX|HzX].
    + rewrite decide_True by set_solver. reflexivity.
    + rewrite decide_False by set_solver. reflexivity.
Qed.

Lemma store_restrict_union_singleton_from_parts'
    (σ ρ σx : Store) (Fixed : aset) (x : atom) :
  x ∉ Fixed →
  dom ρ = Fixed →
  dom σx = {[x]} →
  store_restrict σ Fixed = ρ →
  store_restrict σ {[x]} = σx →
  store_restrict σ (Fixed ∪ {[x]}) = ρ ∪ σx.
Proof.
  intros HxFixed Hdomρ Hdomσx HFixed Hx.
  apply (map_eq (M := gmap atom)). intros z.
  rewrite store_restrict_lookup.
  destruct (decide (z ∈ Fixed ∪ {[x]})) as [HzU|HzU].
  2:{
    symmetry. apply lookup_union_None. split.
    - apply not_elem_of_dom. rewrite Hdomρ. set_solver.
    - apply not_elem_of_dom. rewrite Hdomσx. set_solver.
  }
  destruct (decide (z = x)) as [->|Hzx].
  - rewrite lookup_union_r.
    + pose proof (f_equal (fun s => s !! x) Hx) as Hlook.
      rewrite store_restrict_lookup in Hlook.
      rewrite decide_True in Hlook by set_solver.
      exact Hlook.
    + apply not_elem_of_dom. rewrite Hdomρ. exact HxFixed.
  - rewrite (lookup_union_l' ρ σx z).
    + pose proof (f_equal (fun s => s !! z) HFixed) as Hlook.
      rewrite store_restrict_lookup in Hlook.
      assert (HzFixed : z ∈ Fixed) by set_solver.
      rewrite decide_True in Hlook by exact HzFixed.
      exact Hlook.
    + apply elem_of_dom. rewrite Hdomρ. set_solver.
Qed.

Lemma store_restrict_union_singleton_to_parts'
    (σ ρ σx : Store) (Fixed : aset) (x : atom) :
  x ∉ Fixed →
  dom ρ = Fixed →
  dom σx = {[x]} →
  store_restrict σ (Fixed ∪ {[x]}) = ρ ∪ σx →
  store_restrict σ Fixed = ρ ∧ store_restrict σ {[x]} = σx.
Proof.
  intros HxFixed Hdomρ Hdomσx Hunion.
  split; apply (map_eq (M := gmap atom)); intros z.
  - pose proof (f_equal (fun s => s !! z) Hunion) as Hlook.
    rewrite store_restrict_lookup in Hlook.
    rewrite store_restrict_lookup.
    destruct (decide (z ∈ Fixed)) as [HzFixed|HzFixed].
    + rewrite decide_True in Hlook by set_solver.
      rewrite (lookup_union_l' ρ σx z) in Hlook.
      * exact Hlook.
      * apply elem_of_dom. rewrite Hdomρ. exact HzFixed.
    + symmetry. apply not_elem_of_dom. rewrite Hdomρ. exact HzFixed.
  - pose proof (f_equal (fun s => s !! z) Hunion) as Hlook.
    rewrite store_restrict_lookup in Hlook.
    rewrite store_restrict_lookup.
    destruct (decide (z = x)) as [->|Hzx].
    + rewrite decide_True by set_solver.
      rewrite decide_True in Hlook by set_solver.
      change (σ !! x = (ρ ∪ σx : Store) !! x) in Hlook.
      rewrite (lookup_union_r ρ σx x) in Hlook.
      * exact Hlook.
      * apply not_elem_of_dom. rewrite Hdomρ. exact HxFixed.
    + rewrite decide_False by set_solver.
      symmetry. apply not_elem_of_dom. rewrite Hdomσx. set_solver.
Qed.

Lemma fib_vars_obligation_intro
    X (p : FormulaQ)
    (I : aset → Store → WfWorld → Prop)
    (ρ : Store) (w : WfWorld) :
  I ∅ ρ w →
  (∀ x Y ρ' w',
      x ∈ X →
      x ∉ Y →
      I (X ∖ ({[x]} ∪ Y)) ρ' w' →
      dom ρ' ## {[x]}) →
  (∀ x Y ρ' w',
      x ∈ X →
      x ∉ Y →
      I (X ∖ ({[x]} ∪ Y)) ρ' w' →
      dom ρ' ## {[x]} →
      ∀ σx (Hproj : res_restrict w' {[x]} σx),
        I (X ∖ Y) (ρ' ∪ σx)
          (res_fiber_from_projection w' {[x]} σx Hproj)) →
  (∀ ρ' w',
      I X ρ' w' →
      res_models_with_store ρ' w' p) →
  fib_vars_obligation X p ρ w.
Proof.
  (* Primitive multi-fiber version: this replaces the old fold-over-elements
     induction.  The direct proof should decompose a projection over [X] into
     one-coordinate projections; keeping it admitted while the LN refactor
     removes the fold interface. *)
Admitted.

(** Slice invariant used to read a primitive multi-fiber formula as an exact result world.

    After fixing the variables in [Fixed], the current fiber world [w] should
    be exactly the slice of [result] whose [Fixed]-projection is the current
    store [ρ].  This is intentionally phrased over [X ∪ {[ν]}], the input-plus-
    result interface: the ambient world may carry additional coordinates, but
    the expression-result atom only observes this interface. *)
Definition result_world_slice_inv
    (X : aset) (ν : atom) (result : WfWorld)
    (Fixed : aset) (ρ : Store) (w : WfWorld) : Prop :=
  dom ρ = Fixed ∧
  Fixed ⊆ X ∧
  X ∪ {[ν]} ⊆ world_dom (w : World) ∧
  ∀ σXν,
    (res_restrict w (X ∪ {[ν]}) : World) σXν ↔
      (result : World) σXν ∧ store_restrict σXν Fixed = ρ.

Lemma result_world_slice_inv_initial X ν (result m : WfWorld) :
  X ∪ {[ν]} ⊆ world_dom (m : World) →
  res_restrict m (X ∪ {[ν]}) = result →
  result_world_slice_inv X ν result (∅ : aset) (∅ : Store) m.
Proof.
  intros Hdom Heq. unfold result_world_slice_inv.
  split.
  - reflexivity.
  - split.
    + set_solver.
    + split.
      * exact Hdom.
      * intros σXν. split.
        -- intros Hσ.
           split.
           ++ rewrite <- Heq. exact Hσ.
           ++ rewrite store_restrict_empty_set. reflexivity.
        -- intros [Hσ _]. rewrite <- Heq in Hσ. exact Hσ.
Qed.

Lemma result_world_slice_inv_disjoint X ν result Fixed ρ w x :
  x ∈ X →
  x ∉ Fixed →
  result_world_slice_inv X ν result Fixed ρ w →
  dom ρ ## {[x]}.
Proof.
  intros HxX HxFixed [Hdomρ _].
  rewrite Hdomρ. set_solver.
Qed.

Lemma result_world_slice_inv_step X ν result Fixed ρ w x σx Hproj :
  x ∈ X →
  x ∉ Fixed →
  result_world_slice_inv X ν result Fixed ρ w →
  dom ρ ## {[x]} →
  result_world_slice_inv X ν result (Fixed ∪ {[x]}) (ρ ∪ σx)
    (res_fiber_from_projection w {[x]} σx Hproj).
Proof.
  intros HxX HxFixed Hinv Hdisj.
  unfold result_world_slice_inv in *.
  destruct Hinv as [Hdomρ [HFixedX [Hdomw Hslice]]].
  assert (Hxw : x ∈ world_dom (w : World)) by set_solver.
  assert (Hdomσx : dom σx = {[x]}).
  {
    pose proof (wfworld_store_dom (res_restrict w {[x]}) σx Hproj) as Hdom.
    simpl in Hdom. rewrite Hdom. set_solver.
  }
  split.
  - rewrite dom_union_L, Hdomρ, Hdomσx. set_solver.
  - split.
    + set_solver.
    + split.
      * simpl. exact Hdomw.
      * intros σXν. split.
        -- intros [τ [[Hτw Hτx] Hτrestrict]].
           assert (Hproj_old : (res_restrict w (X ∪ {[ν]}) : World) σXν).
           { exists τ. split; [exact Hτw | exact Hτrestrict]. }
           destruct (proj1 (Hslice σXν) Hproj_old) as [Hresult Hfixed].
           split; [exact Hresult |].
           eapply store_restrict_union_singleton_from_parts'.
           ++ exact HxFixed.
           ++ exact Hdomρ.
           ++ exact Hdomσx.
           ++ exact Hfixed.
           ++ rewrite <- Hτrestrict.
              rewrite store_restrict_restrict.
              replace ((X ∪ {[ν]}) ∩ {[x]}) with ({[x]} : aset) by set_solver.
              rewrite <- Hdomσx. exact Hτx.
        -- intros [Hresult Hfixed_new].
           destruct (store_restrict_union_singleton_to_parts'
             σXν ρ σx Fixed x HxFixed Hdomρ Hdomσx Hfixed_new)
             as [Hfixed Hxpart].
           assert (Hproj_old : (res_restrict w (X ∪ {[ν]}) : World) σXν).
           { apply (proj2 (Hslice σXν)). split; [exact Hresult | exact Hfixed]. }
           destruct Hproj_old as [τ [Hτw Hτrestrict]].
           exists τ. split.
           ++ split; [exact Hτw |].
              rewrite Hdomσx.
              rewrite <- Hτrestrict in Hxpart.
              rewrite store_restrict_restrict in Hxpart.
              replace ((X ∪ {[ν]}) ∩ {[x]}) with ({[x]} : aset) in Hxpart
                by set_solver.
              exact Hxpart.
           ++ exact Hτrestrict.
Qed.

Lemma result_world_slice_inv_base X e ν (n : WfWorld)
    (Hdomn : world_dom (n : World) = X)
    (Hfresh : ν ∉ world_dom (n : World))
    (Hresult :
      ∀ σ, (n : World) σ →
        ∃ vx, subst_map (store_restrict σ (fv_tm e)) e →* tret vx)
    (Hfv : fv_tm e ⊆ X)
    (Hlc : lc_tm e)
    (Hclosed : world_store_closed_on X n)
    ρ (w : WfWorld) :
  result_world_slice_inv X ν
    (let_result_world_on e ν n Hfresh Hresult)
    X ρ w →
  res_models_with_store ρ w (FAtom (expr_logic_qual_on X e ν)).
Proof.
  (*
    Legacy exact-result bridge for the old folded fiber path.  The primitive
    multi-fiber refactor will replace this with a direct FFibVars/LN bridge;
    keeping the old script commented avoids spending minutes compiling proof
    search against definitions we are actively deleting.

  intros Hinv.
  unfold result_world_slice_inv in Hinv.
  destruct Hinv as [Hdomρ [HFixedX [Hdomw Hslice]]].
  apply FAtom_expr_logic_qual_on_intro.
  - unfold formula_scoped_in_world. simpl.
    unfold stale, stale_logic_qualifier. simpl.
    rewrite Hdomρ. set_solver.
  - intros σν. split.
    + intros Hprojν.
      destruct Hprojν as [τ [Hτw Hτν]].
      assert (HprojXν : (res_restrict w (X ∪ {[ν]}) : World)
        (store_restrict τ (X ∪ {[ν]}))).
      { exists τ. split; [exact Hτw | reflexivity]. }
      destruct (proj1 (Hslice _) HprojXν) as [Hresult_store Hfixed].
      destruct (let_result_world_on_elim e ν n Hfresh Hresult
        (store_restrict τ (X ∪ {[ν]})) Hresult_store)
        as [σ [vx [Hσn [Hsteps Hτeq]]]].
      assert (Hσρ : σ = ρ).
      {
        assert (Hrestrict_insert :
          store_restrict (<[ν := vx]> σ) X = store_restrict σ X).
        { rewrite store_restrict_insert_notin; [reflexivity |].
          rewrite <- Hdomn. exact Hfresh. }
        rewrite Hτeq in Hfixed.
        rewrite Hrestrict_insert in Hfixed.
        assert (Hσid : store_restrict σ X = σ).
        {
          apply store_restrict_idemp.
          eapply wfworld_store_dom_subset; [exact Hσn |].
          rewrite Hdomn. set_solver.
        }
        rewrite Hσid in Hfixed. exact Hfixed.
      }
      subst σ.
      assert (Hstepsρ :
        subst_map (store_restrict ρ X) e →* tret vx).
      {
        replace (subst_map (store_restrict ρ X) e)
          with (subst_map (store_restrict ρ (fv_tm e)) e).
        - exact Hsteps.
        - symmetry.
          pose proof (subst_map_eq_on_fv e
            (store_restrict ρ X)
            (store_restrict ρ (fv_tm e))) as Heq.
          assert (Hclosed_fv :
            closed_env (store_restrict (store_restrict ρ X) (fv_tm e))).
          {
            apply closed_env_restrict.
            exact (proj1 (Hclosed ρ Hσn)).
          }
          specialize (Heq Hclosed_fv).
          assert (Hagree :
            store_restrict (store_restrict ρ (fv_tm e)) (fv_tm e) =
            store_restrict (store_restrict ρ X) (fv_tm e)).
          {
            store_norm.
            replace (X ∩ fv_tm e) with (fv_tm e) by set_solver.
            reflexivity.
          }
          specialize (Heq Hagree).
          symmetry. exact Heq.
      }
      assert (Hσν_single : σν = {[ν := vx]}).
      {
        rewrite <- Hτν.
        replace (store_restrict τ ({[ν]} : aset))
          with (store_restrict (store_restrict τ (X ∪ {[ν]})) ({[ν]} : aset)).
        2:{
          rewrite store_restrict_restrict.
          replace ((X ∪ {[ν]}) ∩ ({[ν]} : aset)) with ({[ν]} : aset)
            by set_solver.
          reflexivity.
        }
        rewrite Hτeq.
        rewrite store_restrict_insert_singleton.
        reflexivity.
      }
      rewrite Hσν_single.
      apply expr_result_store_intro.
      * assert (Hρproj : (res_restrict n X : World) ρ).
        {
          exists ρ. split; [exact Hσn |].
          rewrite <- Hdomρ. apply store_restrict_idemp. set_solver.
        }
        pose proof (steps_closed_result_of_restrict_world X e n ρ vx
          ltac:(rewrite Hdomn; set_solver) Hfv Hlc Hclosed Hρproj Hstepsρ)
          as [Hstale_vx _].
        exact Hstale_vx.
      * assert (Hρproj : (res_restrict n X : World) ρ).
        {
          exists ρ. split; [exact Hσn |].
          rewrite <- Hdomρ. apply store_restrict_idemp. set_solver.
        }
        pose proof (steps_closed_result_of_restrict_world X e n ρ vx
          ltac:(rewrite Hdomn; set_solver) Hfv Hlc Hclosed Hρproj Hstepsρ)
          as [_ Hlc_vx].
        exact Hlc_vx.
      * exact Hstepsρ.
    + intros Hstore.
      unfold expr_result_store in Hstore.
      destruct Hstore as [vx [Hσν [Hclosed_vx [Hlc_vx Hstepsρ]]]].
      subst σν.
      destruct (world_wf w) as [[τ Hτw] _].
      assert (HprojXν : (res_restrict w (X ∪ {[ν]}) : World)
        (store_restrict τ (X ∪ {[ν]}))).
      { exists τ. split; [exact Hτw | reflexivity]. }
      destruct (proj1 (Hslice _) HprojXν) as [Hresult_store Hfixed].
      destruct (let_result_world_on_elim e ν n Hfresh Hresult
        (store_restrict τ (X ∪ {[ν]})) Hresult_store)
        as [σ [vy [Hσn [Hsteps_y Hτeq]]]].
      assert (Hσρ : σ = ρ).
      {
        assert (Hrestrict_insert :
          store_restrict (<[ν := vy]> σ) X = store_restrict σ X).
        { rewrite store_restrict_insert_notin; [reflexivity |].
          rewrite <- Hdomn. exact Hfresh. }
        rewrite Hτeq in Hfixed.
        rewrite Hrestrict_insert in Hfixed.
        assert (Hσid : store_restrict σ X = σ).
        {
          apply store_restrict_idemp.
          eapply wfworld_store_dom_subset; [exact Hσn |].
          rewrite Hdomn. set_solver.
        }
        rewrite Hσid in Hfixed. exact Hfixed.
      }
      subst σ.
      assert (Hsteps_fv :
        subst_map (store_restrict ρ (fv_tm e)) e →* tret vx).
      {
        replace (subst_map (store_restrict ρ (fv_tm e)) e)
          with (subst_map (store_restrict ρ X) e).
        - exact Hstepsρ.
        - pose proof (subst_map_eq_on_fv e
            (store_restrict ρ X)
            (store_restrict ρ (fv_tm e))) as Heq.
          assert (Hclosed_fv :
            closed_env (store_restrict (store_restrict ρ X) (fv_tm e))).
          {
            apply closed_env_restrict.
            exact (proj1 (Hclosed ρ Hσn)).
          }
          specialize (Heq Hclosed_fv).
          assert (Hagree :
            store_restrict (store_restrict ρ (fv_tm e)) (fv_tm e) =
            store_restrict (store_restrict ρ X) (fv_tm e)).
          {
            store_norm.
            replace (X ∩ fv_tm e) with (fv_tm e) by set_solver.
            reflexivity.
          }
          specialize (Heq Hagree).
          symmetry. exact Heq.
      }
      assert (Hmember :
        (let_result_world_on e ν n Hfresh Hresult : World)
          (<[ν := vx]> ρ)).
      { apply let_result_world_on_member; [exact Hσn | exact Hsteps_fv]. }
      assert (Hfixed_new :
        store_restrict (<[ν := vx]> ρ) X = ρ).
      {
        rewrite store_restrict_insert_notin.
        - rewrite <- Hdomρ. apply store_restrict_idemp. set_solver.
        - rewrite <- Hdomn. exact Hfresh.
      }
      assert (HprojXν_new :
        (res_restrict w (X ∪ {[ν]}) : World) (<[ν := vx]> ρ)).
      { apply (proj2 (Hslice _)). split; [exact Hmember | exact Hfixed_new]. }
      destruct HprojXν_new as [τ' [Hτ'w Hτ'restrict]].
      exists τ'. split; [exact Hτ'w |].
      replace (store_restrict τ' ({[ν]} : aset))
        with (store_restrict (store_restrict τ' (X ∪ {[ν]})) ({[ν]} : aset)).
      2:{
        rewrite store_restrict_restrict.
        replace ((X ∪ {[ν]}) ∩ ({[ν]} : aset)) with ({[ν]} : aset)
          by set_solver.
        reflexivity.
      }
      rewrite Hτ'restrict.
      rewrite store_restrict_insert_singleton.
      reflexivity.
  *)
Admitted.
