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

Lemma foldr_fib_vars_acc_fst_bridge xs φ R :
  fst (foldr fib_vars_acc_step (φ, R) xs) = foldr FFib φ xs.
Proof.
  induction xs as [|x xs IH]; simpl; [reflexivity |].
  rewrite <- IH. destruct (foldr fib_vars_acc_step (φ, R) xs); reflexivity.
Qed.

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
    (foldr FFib (FAtom (expr_logic_qual_on X e ν)) xs) →
  (m : World) σw →
  store_restrict σw {[ν]} = sigmanu →
  expr_result_store ν
    (subst_map
      (store_restrict (ρ ∪ store_restrict σw (list_to_set xs : aset)) X)
      e)
    sigmanu.
Proof.
  revert ρ m σw sigmanu.
  induction xs as [|x xs IH]; intros ρ m σw sigmanu Hnodup Hdisj Hmodel Hσw Heqν.
  - pose proof (FAtom_expr_logic_qual_on_exact X e ν ρ m Hmodel) as Hexact.
    simpl in *.
    rewrite store_restrict_empty_set.
    replace (ρ ∪ (∅ : Store)) with ρ.
    change (expr_result_store ν (subst_map (store_restrict ρ X) e) sigmanu).
    assert (Hprojν : (res_restrict m {[ν]} : World) sigmanu).
    { exists σw. split; [exact Hσw | exact Heqν]. }
    exact (expr_result_in_world_sound (store_restrict ρ X) e ν m sigmanu Hexact Hprojν).
    apply (map_eq (M := gmap atom)). intros z.
    rewrite lookup_union_l by apply lookup_empty.
    reflexivity.
  - simpl in *.
    inversion Hnodup as [|x0 xs0 Hx_notin Hnodup']; subst x0 xs0.
    unfold res_models_with_store in Hmodel. simpl in Hmodel.
    destruct Hmodel as [Hscope [Hρx Hfib]].
    set (σx := store_restrict σw {[x]}).
    assert (Hprojx : res_restrict m {[x]} σx).
    { exists σw. split; [exact Hσw | reflexivity]. }
    specialize (Hfib σx Hprojx).
    assert (Hσw_fib :
      (res_fiber_from_projection m {[x]} σx Hprojx : World) σw).
    { apply res_fiber_from_projection_member; [exact Hσw | reflexivity]. }
    specialize (IH (ρ ∪ σx)
      (res_fiber_from_projection m {[x]} σx Hprojx) σw sigmanu
      Hnodup').
    assert (Hdisj_tail : dom (ρ ∪ σx) ## (list_to_set xs : aset)).
    {
      rewrite dom_union_L.
      unfold σx. rewrite store_restrict_dom.
      set_solver.
    }
    specialize (IH Hdisj_tail).
    pose proof (IH ltac:(models_fuel_irrel Hfib)
      Hσw_fib ltac:(assumption)) as Hstore.
    unfold σx in Hstore.
    rewrite <- store_restrict_accum_cons_projection in Hstore.
    + exact Hstore.
    + rewrite elem_of_list_to_set. exact Hx_notin.
    + exact Hdisj.
Qed.

Lemma foldr_fib_expr_result_complete
    xs X e ν ρ (m : WfWorld) σw sigmanu :
  NoDup xs →
  dom ρ ## (list_to_set xs : aset) →
  res_models_with_store ρ m
    (foldr FFib (FAtom (expr_logic_qual_on X e ν)) xs) →
  (m : World) σw →
  expr_result_store ν
    (subst_map
      (store_restrict (ρ ∪ store_restrict σw (list_to_set xs : aset)) X)
      e)
    sigmanu →
  (res_restrict m {[ν]} : World) sigmanu.
Proof.
  revert ρ m σw sigmanu.
  induction xs as [|x xs IH]; simpl; intros ρ m σw sigmanu Hnodup Hdisj Hmodel Hσw Hstore.
  - pose proof (FAtom_expr_logic_qual_on_exact X e ν ρ m Hmodel) as Hexact.
    rewrite store_restrict_empty_set in Hstore.
    replace (ρ ∪ (∅ : Store)) with ρ in Hstore.
    + exact (expr_result_in_world_complete (store_restrict ρ X) e ν m sigmanu Hexact Hstore).
    + apply (map_eq (M := gmap atom)). intros z.
      rewrite lookup_union_l by apply lookup_empty.
      reflexivity.
  - inversion Hnodup as [|? ? Hx_notin Hnodup']; subst.
    unfold res_models_with_store in Hmodel. simpl in Hmodel.
    destruct Hmodel as [Hscope [Hρx Hfib]].
    set (σx := store_restrict σw {[x]}).
    assert (Hprojx : res_restrict m {[x]} σx).
    { exists σw. split; [exact Hσw | reflexivity]. }
    specialize (Hfib σx Hprojx).
    assert (Hσw_fib :
      (res_fiber_from_projection m {[x]} σx Hprojx : World) σw).
    { apply res_fiber_from_projection_member; [exact Hσw | reflexivity]. }
    assert (Hdisj_tail : dom (ρ ∪ σx) ## (list_to_set xs : aset)).
    {
      rewrite dom_union_L.
      unfold σx. rewrite store_restrict_dom.
      set_solver.
    }
    rewrite store_restrict_accum_cons_projection in Hstore.
    2:{ rewrite elem_of_list_to_set. exact Hx_notin. }
    2:{ exact Hdisj. }
    specialize (IH (ρ ∪ σx)
      (res_fiber_from_projection m {[x]} σx Hprojx) σw sigmanu
      Hnodup' Hdisj_tail
      ltac:(models_fuel_irrel Hfib)
      Hσw_fib Hstore).
    destruct IH as [τ [Hτ Hτν]].
    destruct Hτ as [Hτm _].
    exists τ. split; [exact Hτm | exact Hτν].
Qed.

Lemma foldr_fib_expr_result_complete_paired
    xs X e ν ρ (m : WfWorld) σw sigmanu :
  NoDup xs →
  dom ρ ## (list_to_set xs : aset) →
  res_models_with_store ρ m
    (foldr FFib (FAtom (expr_logic_qual_on X e ν)) xs) →
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
  revert ρ m σw sigmanu.
  induction xs as [|x xs IH]; simpl; intros ρ m σw sigmanu Hnodup Hdisj Hmodel Hσw Hstore.
  - pose proof (FAtom_expr_logic_qual_on_exact X e ν ρ m Hmodel) as Hexact.
    rewrite store_restrict_empty_set in Hstore.
    replace (ρ ∪ (∅ : Store)) with ρ in Hstore.
    2:{
      apply (map_eq (M := gmap atom)). intros z.
      rewrite lookup_union_l by apply lookup_empty. reflexivity.
    }
    pose proof (expr_result_in_world_complete
      (store_restrict ρ X) e ν m sigmanu Hexact Hstore)
      as [τ [Hτ Hτν]].
    exists τ. repeat split; auto.
    rewrite !store_restrict_empty_set. reflexivity.
  - inversion Hnodup as [|? ? Hx_notin Hnodup']; subst.
    unfold res_models_with_store in Hmodel. simpl in Hmodel.
    destruct Hmodel as [Hscope [Hρx Hfib]].
    set (σx := store_restrict σw {[x]}).
    assert (Hprojx : res_restrict m {[x]} σx).
    { exists σw. split; [exact Hσw | reflexivity]. }
    specialize (Hfib σx Hprojx).
    assert (Hσw_fib :
      (res_fiber_from_projection m {[x]} σx Hprojx : World) σw).
    { apply res_fiber_from_projection_member; [exact Hσw | reflexivity]. }
    assert (Hdisj_tail : dom (ρ ∪ σx) ## (list_to_set xs : aset)).
    {
      rewrite dom_union_L.
      unfold σx. rewrite store_restrict_dom.
      set_solver.
    }
    rewrite store_restrict_accum_cons_projection in Hstore.
    2:{ rewrite elem_of_list_to_set. exact Hx_notin. }
    2:{ exact Hdisj. }
    destruct (IH (ρ ∪ σx)
      (res_fiber_from_projection m {[x]} σx Hprojx) σw sigmanu
      Hnodup' Hdisj_tail
      ltac:(models_fuel_irrel Hfib)
      Hσw_fib Hstore)
      as [τ [Hτfib [Hτxs Hτν]]].
    destruct Hτfib as [Hτm Hτx].
    assert (Hxdom : x ∈ world_dom (m : World)).
    {
      unfold formula_scoped_in_world in Hscope. simpl in Hscope.
      apply Hscope. set_solver.
    }
    assert (Hdomσx : dom σx = {[x]}).
    { pose proof (wfworld_store_dom (res_restrict m {[x]}) σx Hprojx) as Hdom.
      simpl in Hdom.
      transitivity (world_dom (m : World) ∩ {[x]}).
      - exact Hdom.
      - set_solver. }
    assert (Hτx' : store_restrict τ {[x]} = store_restrict σw {[x]}).
    {
      assert (Hσx_dom : store_restrict σw (dom σx) = σx).
      { rewrite Hdomσx. unfold σx. reflexivity. }
      rewrite <- Hdomσx.
      rewrite Hσx_dom.
      exact Hτx.
    }
    exists τ. split; [exact Hτm |]. split; [| exact Hτν].
    eapply store_restrict_union_singleton_eq_from_parts.
    + rewrite elem_of_list_to_set. exact Hx_notin.
    + exact Hτx'.
    + exact Hτxs.
Qed.

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

Lemma foldr_fib_vars_obligation_intro
    xs X (p : FormulaQ)
    (I : aset → Store → WfWorld → Prop)
    (ρ : Store) (w : WfWorld) :
  NoDup xs →
  (list_to_set xs : aset) ⊆ X →
  I (X ∖ (list_to_set xs : aset)) ρ w →
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
  snd (foldr fib_vars_acc_step
        (p, fun ρ' w' => res_models_with_store ρ' w' p) xs) ρ w.
Proof.
  revert ρ w.
  induction xs as [|x xs IH]; intros ρ w Hnodup Hxs HI Hdisj Hstep Hbase.
  - simpl in *. replace (X ∖ (∅ : aset)) with X in HI by set_solver.
    exact (Hbase ρ w HI).
  - simpl in *.
    inversion Hnodup as [|? ? Hx_notin Hnodup']; subst.
    destruct (foldr fib_vars_acc_step
      (p, fun ρ' w' => res_models_with_store ρ' w' p) xs) as [q R] eqn:Hfold.
    simpl.
    unfold fib_vars_obligation_step.
    assert (HxX : x ∈ X).
    { apply Hxs. simpl. set_solver. }
    assert (Hxs_sub : (list_to_set xs : aset) ⊆ X).
    { intros z Hz. apply Hxs. simpl. set_solver. }
    split.
    + exact (Hdisj x (list_to_set xs) ρ w HxX
        ltac:(rewrite elem_of_list_to_set; exact Hx_notin) HI).
    + intros σx Hproj.
      eapply IH; eauto.
      * eapply Hstep; eauto.
        -- rewrite elem_of_list_to_set. exact Hx_notin.
        -- exact (Hdisj x (list_to_set xs) ρ w HxX
             ltac:(rewrite elem_of_list_to_set; exact Hx_notin) HI).
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
  intros HI Hdisj Hstep Hbase.
  unfold fib_vars_obligation, fib_vars_acc, set_fold.
  cbn [compose].
  eapply foldr_fib_vars_obligation_intro.
  - apply NoDup_elements.
  - intros z Hz. rewrite elem_of_list_to_set, elem_of_elements in Hz. exact Hz.
  - replace (X ∖ (list_to_set (elements X) : aset)) with (∅ : aset).
    + exact HI.
    + apply set_eq. intros z. rewrite elem_of_difference.
      rewrite elem_of_list_to_set, elem_of_elements. set_solver.
  - exact Hdisj.
  - exact Hstep.
  - exact Hbase.
Qed.

(** Slice invariant used to read a [fib_vars] tower as an exact result world.

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

(** The exact bridge from [FExprResult] to [let_result_world_on] is deliberately
    disabled for now.  In the new setting [FExprResult e ν] scopes over
    [fv_tm e ∪ {ν}], while [let_result_world_on e ν ...] constructs a concrete
    result world from the [fv_tm e]-projection.  We still need to decide the
    right statement connecting these two views.

    Downstream lemmas that used this bridge are intentionally left admitted for
    the same reason, including:

    - [let_result_world_on_models_FExprResult]
    - [FExprResult_expr_result_equiv_in_world]
    - [nested_body_result_world_models_FExprResult]
    - [FExprResult_tlete_from_body_result_world]

    Keeping this block commented avoids accidentally using an obsolete bridge
    while the result-world semantics are still being redesigned. *)
(*
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
Admitted.

Lemma FExprResult_iff_let_result_world_on :
  ∀ e ν (m : WfWorld),
    fv_tm e ⊆ world_dom (m : World) →
    lc_tm e →
    ν ∉ fv_tm e →
    (m ⊨ FExprResult e ν ↔
     ∃ Hfresh Hresult,
       m =
         let_result_world_on e ν (res_restrict m (world_dom (m : World) ∖ fv_tm e)) Hfresh Hresult).
Proof.
Admitted. *)
