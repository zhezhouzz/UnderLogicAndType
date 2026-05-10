(** * ChoiceTyping.ResultWorldBridge

    Bridges between expression-result formulas and the concrete result worlds
    used by the soundness proof.

    The first group relates the cofinite [fresh_forall] encoding

      forall x.  [e ⇓ x] ==> body x

    to the operational result world [let_result_world_on X e x m].  Because
    [fresh_forall] is explicit-name/cofinite rather than locally nameless, the
    primitive bridge is phrased with the renamed representative
    [formula_rename_atom (fresh_for D) y (body (fresh_for D))].  Callers that
    know their body is equivariant can use the wrapper lemma to transport this
    renamed body to the desired [body y].

    The second group records resource-relative expression equivalence.  This is
    weaker than [expr_result_equiv_on]: it only compares the stores actually
    present in a world/resource.  It is the right shape for rewriting the
    expression part of denotations inside Kripke/resource proofs. *)

From CoreLang Require Import Instantiation InstantiationProps OperationalProps
  LocallyNamelessProps.
From ChoiceTyping Require Export SoundnessCommon.
From ChoiceTyping Require Export LetResultWorld.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

Definition world_store_closed_on (X : aset) (m : WfWorld) : Prop :=
  ∀ σ, (m : World) σ → store_closed (store_restrict σ X).

Lemma world_store_closed_on_le X (m n : WfWorld) :
  X ⊆ world_dom (m : World) →
  m ⊑ n →
  world_store_closed_on X m →
  world_store_closed_on X n.
Proof.
  intros HXm Hle Hclosed σ Hσ.
  pose proof (res_restrict_eq_of_le m n Hle) as Hrestrict.
  assert ((res_restrict n (world_dom (m : World)) : World)
    (store_restrict σ (world_dom (m : World)))) as Hσm.
  { exists σ. split; [exact Hσ | reflexivity]. }
  rewrite Hrestrict in Hσm.
  replace (store_restrict σ X) with
    (store_restrict (store_restrict σ (world_dom (m : World))) X).
  - exact (Hclosed _ Hσm).
  - rewrite store_restrict_restrict.
    replace (world_dom (m : World) ∩ X) with X by set_solver.
    reflexivity.
Qed.

Lemma world_store_closed_on_restrict X Y (m : WfWorld) :
  X ⊆ Y →
  world_store_closed_on X m →
  world_store_closed_on X (res_restrict m Y).
Proof.
  intros HXY Hclosed σ Hσ.
  destruct Hσ as [σ0 [Hσ0 Hrestrict]].
  rewrite <- Hrestrict.
  rewrite store_restrict_restrict.
  replace (Y ∩ X) with X by set_solver.
  exact (Hclosed σ0 Hσ0).
Qed.

Lemma let_result_world_on_store_closed_on
    X e ν (n : WfWorld) Hfresh Hresult :
  ν ∉ X →
  world_store_closed_on X n →
  world_store_closed_on X (let_result_world_on X e ν n Hfresh Hresult).
Proof.
  intros HνX Hclosed σx Hσx.
  destruct (let_result_world_on_elim X e ν n Hfresh Hresult σx Hσx)
    as [σ [vx [Hσ [Hsteps ->]]]].
  rewrite store_restrict_insert_notin by exact HνX.
  exact (Hclosed σ Hσ).
Qed.

Lemma let_result_world_on_store_closed_on_insert
    X e ν (n : WfWorld) Hfresh Hresult :
  ν ∉ X →
  world_store_closed_on X n →
  (∀ σ vx,
    (n : World) σ →
    subst_map (store_restrict σ X) e →* tret vx →
    stale vx = ∅ ∧ is_lc vx) →
  world_store_closed_on (X ∪ {[ν]})
    (let_result_world_on X e ν n Hfresh Hresult).
Proof.
  intros HνX Hclosed Hres σν Hσν.
  destruct (let_result_world_on_elim X e ν n Hfresh Hresult σν Hσν)
    as [σ [vx [Hσ [Hsteps ->]]]].
  rewrite store_restrict_insert_fresh_union.
  2:{
    eapply store_lookup_none_of_dom.
    - apply wfworld_store_dom. exact Hσ.
    - exact Hfresh.
  }
  2:{ exact HνX. }
  destruct (Hclosed σ Hσ) as [Hclosedσ Hlcσ].
  destruct (Hres σ vx Hσ Hsteps) as [Hvx_closed Hvx_lc].
  split.
  - unfold closed_env in *.
    apply map_Forall_insert_2; [exact Hvx_closed | exact Hclosedσ].
  - unfold lc_env in *.
    apply map_Forall_insert_2; [exact Hvx_lc | exact Hlcσ].
Qed.

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
  expr_result_in_store
    (store_restrict (ρ ∪ store_restrict σw (list_to_set xs : aset)) X)
    e ν sigmanu.
Proof.
  revert ρ m σw sigmanu.
  induction xs as [|x xs IH]; intros ρ m σw sigmanu Hnodup Hdisj Hmodel Hσw Heqν.
  - pose proof (FAtom_expr_logic_qual_on_exact X e ν ρ m Hmodel) as Hexact.
    simpl in *.
    rewrite store_restrict_empty_set.
    replace (ρ ∪ (∅ : Store)) with ρ.
    change (expr_result_in_store (store_restrict ρ X) e ν sigmanu).
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
    pose proof (IH ltac:(eapply res_models_with_store_fuel_irrel; [| | exact Hfib]; simpl; lia)
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
  expr_result_in_store
    (store_restrict (ρ ∪ store_restrict σw (list_to_set xs : aset)) X)
    e ν sigmanu →
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
      ltac:(eapply res_models_with_store_fuel_irrel; [| | exact Hfib]; simpl; lia)
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
  expr_result_in_store
    (store_restrict (ρ ∪ store_restrict σw (list_to_set xs : aset)) X)
    e ν sigmanu →
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
      ltac:(eapply res_models_with_store_fuel_irrel; [| | exact Hfib]; simpl; lia)
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

Lemma result_world_slice_inv_base X e ν (n : WfWorld)
    (Hdomn : world_dom (n : World) = X)
    (Hfresh : ν ∉ world_dom (n : World))
    (Hresult :
      ∀ σ, (n : World) σ →
        ∃ vx, subst_map (store_restrict σ X) e →* tret vx)
    (Hfv : fv_tm e ⊆ X)
    (Hlc : lc_tm e)
    (Hclosed : world_store_closed_on X n)
    ρ (w : WfWorld) :
  result_world_slice_inv X ν
    (let_result_world_on X e ν n Hfresh Hresult)
    X ρ w →
  res_models_with_store ρ w (FAtom (expr_logic_qual_on X e ν)).
Proof.
  intros Hinv.
  unfold result_world_slice_inv in Hinv.
  destruct Hinv as [Hdomρ [_ [Hdomw Hslice]]].
  assert (HνX : ν ∉ X) by (rewrite <- Hdomn; exact Hfresh).
  assert (Hρ_id : store_restrict ρ X = ρ).
  { apply store_restrict_idemp. set_solver. }
  eapply FAtom_expr_logic_qual_on_intro.
  - unfold formula_scoped_in_world. simpl.
    unfold stale, stale_logic_qualifier. simpl.
    intros z Hz.
    rewrite Hdomρ in Hz. set_solver.
  - intros σν. split.
    + intros Hprojν.
      destruct Hprojν as [τ [Hτw Hτν]].
      set (σXν := store_restrict τ (X ∪ {[ν]})).
      assert (HτXν_eq : store_restrict τ (X ∪ {[ν]}) = σXν) by reflexivity.
      assert (HprojXν : (res_restrict w (X ∪ {[ν]}) : World) σXν).
      { exists τ. split; [exact Hτw | reflexivity]. }
      destruct (proj1 (Hslice σXν) HprojXν) as [Hres Hfixed].
      destruct (let_result_world_on_elim X e ν n Hfresh Hresult σXν Hres)
        as [σ [vx [Hσn [Hsteps ->]]]].
      rewrite store_restrict_insert_notin in Hfixed by exact HνX.
      rewrite store_restrict_idemp in Hfixed.
      2:{ pose proof (wfworld_store_dom n σ Hσn) as Hdomσ.
          set_solver. }
      subst ρ.
      rewrite Hρ_id.
      assert (Hσν : σν = {[ν := vx]}).
      {
        rewrite <- Hτν.
        transitivity (store_restrict (store_restrict τ (X ∪ {[ν]})) {[ν]}).
        - rewrite store_restrict_restrict.
          replace ((X ∪ {[ν]}) ∩ {[ν]}) with ({[ν]} : aset) by set_solver.
          reflexivity.
        - rewrite HτXν_eq.
        rewrite store_restrict_insert_in by set_solver.
        replace (store_restrict σ {[ν]}) with (∅ : Store).
        2:{
          apply (map_eq (M := gmap atom)). intros z.
          rewrite store_restrict_lookup.
          destruct (decide (z ∈ ({[ν]} : aset))) as [Hzν|Hzν]; [| reflexivity].
          apply elem_of_singleton in Hzν. subst z.
          rewrite lookup_empty.
          destruct (σ !! ν) eqn:Hσν; [| symmetry; exact Hσν].
          exfalso. apply HνX.
          rewrite <- Hdomn.
          pose proof (wfworld_store_dom n σ Hσn) as Hdomσ.
          rewrite <- Hdomσ. apply elem_of_dom. eauto.
        }
        apply (map_eq (M := gmap atom)). intros z.
        destruct (decide (z = ν)) as [->|Hzν].
        + rewrite lookup_insert. rewrite lookup_singleton.
          destruct (decide (ν = ν)); [reflexivity | contradiction].
        + rewrite lookup_insert_ne by congruence.
          rewrite lookup_empty, lookup_singleton, decide_False by congruence.
          reflexivity.
      }
      subst σν.
      assert (Hinput_closed : closed_tm (subst_map (store_restrict σ X) e)).
      {
        apply msubst_closed_tm.
        - exact (Hclosed σ Hσn).
        - exact Hlc.
        - change (fv_tm e ⊆ dom (store_restrict σ X)).
          rewrite store_restrict_dom.
          pose proof (wfworld_store_dom n σ Hσn) as Hdomσ.
          set_solver.
      }
      pose proof (steps_closed_result _ _ Hinput_closed Hsteps) as [Hstale Hlc_v].
      rewrite Hρ_id in Hsteps.
      rewrite Hσν.
      apply expr_result_store_intro; [exact Hstale | exact Hlc_v | exact Hsteps].
    + intros Hstore.
      destruct (expr_result_store_elim ν (subst_map (store_restrict ρ X) e) σν Hstore)
        as [vx [-> [_ [_ Hsteps]]]].
      rewrite Hρ_id in Hsteps.
      destruct (world_wf w) as [[τ Hτw] _].
      set (σXν0 := store_restrict τ (X ∪ {[ν]})).
      assert (HprojXν0 : (res_restrict w (X ∪ {[ν]}) : World) σXν0).
      { exists τ. split; [exact Hτw | reflexivity]. }
      destruct (proj1 (Hslice σXν0) HprojXν0) as [Hres0 Hfixed0].
      destruct (let_result_world_on_elim X e ν n Hfresh Hresult σXν0 Hres0)
        as [σ0 [vx0 [Hσ0n [_ ->]]]].
      rewrite store_restrict_insert_notin in Hfixed0 by exact HνX.
      rewrite store_restrict_idemp in Hfixed0.
      2:{ pose proof (wfworld_store_dom n σ0 Hσ0n) as Hdomσ0.
          set_solver. }
      subst ρ.
      assert (Hres : (let_result_world_on X e ν n Hfresh Hresult : World)
        (<[ν := vx]> σ0)).
      { apply let_result_world_on_member; [exact Hσ0n |].
        rewrite Hρ_id. exact Hsteps. }
      assert (Hfixed : store_restrict (<[ν := vx]> σ0) X = σ0).
      {
        rewrite store_restrict_insert_notin by exact HνX.
        apply store_restrict_idemp.
        pose proof (wfworld_store_dom n σ0 Hσ0n) as Hdomσ0.
        set_solver.
      }
      assert (HprojXν : (res_restrict w (X ∪ {[ν]}) : World)
        (<[ν := vx]> σ0)).
      { apply (proj2 (Hslice (<[ν := vx]> σ0))). split; [exact Hres | exact Hfixed]. }
      destruct HprojXν as [τ' [Hτ'w Hτ'restrict]].
      exists τ'. split; [exact Hτ'w |].
      transitivity (store_restrict (store_restrict τ' (X ∪ {[ν]})) {[ν]}).
      * rewrite store_restrict_restrict.
        replace ((X ∪ {[ν]}) ∩ {[ν]}) with ({[ν]} : aset) by set_solver.
        reflexivity.
      * rewrite Hτ'restrict.
      rewrite store_restrict_insert_in by set_solver.
      replace (store_restrict σ0 {[ν]}) with (∅ : Store).
      2:{
        apply (map_eq (M := gmap atom)). intros z.
        rewrite store_restrict_lookup.
        destruct (decide (z ∈ ({[ν]} : aset))) as [Hzν|Hzν]; [| reflexivity].
        apply elem_of_singleton in Hzν. subst z.
        rewrite lookup_empty.
        destruct (σ0 !! ν) eqn:Hσν; [| symmetry; exact Hσν].
        exfalso. apply HνX.
        rewrite <- Hdomn.
        pose proof (wfworld_store_dom n σ0 Hσ0n) as Hdomσ0.
        rewrite <- Hdomσ0. apply elem_of_dom. eauto.
      }
      apply (map_eq (M := gmap atom)). intros z.
      destruct (decide (z = ν)) as [->|Hzν].
      { rewrite lookup_insert. rewrite lookup_singleton.
        destruct (decide (ν = ν)); [reflexivity | contradiction]. }
      { rewrite lookup_insert_ne by congruence.
        rewrite lookup_empty, lookup_singleton, decide_False by congruence.
        reflexivity. }
Qed.

Lemma FExprResultOn_iff_let_result_world_on :
  ∀ X e ν (m : WfWorld),
    fv_tm e ⊆ X →
    lc_tm e →
    ν ∉ X →
    X ⊆ world_dom (m : World) →
    world_store_closed_on X m →
    (m ⊨ FExprResultOn X e ν ↔
     ∃ Hfresh Hresult,
       res_restrict m (X ∪ {[ν]}) =
         let_result_world_on X e ν (res_restrict m X) Hfresh Hresult).
Proof.
  intros X e ν m Hfv Hlc HνX HXm Hclosed.
  assert (Hmodel_to_fold :
    m ⊨ FExprResultOn X e ν →
    res_models_with_store ∅ m
      (foldr FFib (FAtom (expr_logic_qual_on X e ν)) (elements X))).
  {
    intros Hmodel.
    unfold FExprResultOn, FExprResultOnRaw, fib_vars, fib_vars_acc, set_fold in Hmodel.
    cbn [compose] in Hmodel.
    rewrite foldr_fib_vars_acc_fst_bridge in Hmodel.
    exact Hmodel.
  }
  split.
  - intros Hmodel.
    pose proof (Hmodel_to_fold Hmodel) as Hmodel_fold.
    assert (Hfresh : ν ∉ world_dom (res_restrict m X : World)).
    { simpl. set_solver. }
    assert (Hresult :
      ∀ σ, (res_restrict m X : World) σ →
        ∃ vx, subst_map (store_restrict σ X) e →* tret vx).
    {
      intros σ Hσ.
      destruct Hσ as [σw [Hσw Hrestrict]].
      assert (Hdisj_empty_X : dom (∅ : Store) ## (list_to_set (elements X) : aset)).
      { rewrite dom_empty_L. set_solver. }
      pose proof (foldr_fib_expr_result_sound
        (elements X) X e ν ∅ m σw (store_restrict σw {[ν]})
        (NoDup_elements X)
        Hdisj_empty_X
        Hmodel_fold Hσw eq_refl) as Hstore.
      assert (HelemsX : (list_to_set (elements X) : aset) = X).
      { apply set_eq. intros z. rewrite elem_of_list_to_set, elem_of_elements. reflexivity. }
      rewrite HelemsX in Hstore.
      replace ((∅ : Store) ∪ store_restrict σw X) with (store_restrict σw X) in Hstore.
      2:{ apply (map_eq (M := gmap atom)). intros z.
          rewrite lookup_union_r; [reflexivity | apply lookup_empty]. }
      rewrite Hrestrict in Hstore.
      destruct (expr_result_store_elim ν (subst_map (store_restrict σ X) e)
        (store_restrict σw {[ν]}) Hstore)
        as [vx [_ [_ [_ Hsteps]]]].
      exists vx. exact Hsteps.
    }
    exists Hfresh, Hresult.
    pose proof (FExprResultOn_scoped_dom X e ν m
      (res_models_with_store_fuel_scoped _ _ _ _ Hmodel)) as Hscope_dom.
    apply wfworld_ext. apply world_ext.
    + simpl. unfold let_result_world_on, let_result_raw_world_on. simpl.
      apply set_eq. intros z. split; intros Hz; set_solver.
    + intros σXν. simpl. split.
      * intros [σw [Hσw Hrestrict]].
        assert (Hdisj_empty_X : dom (∅ : Store) ## (list_to_set (elements X) : aset)).
        { rewrite dom_empty_L. set_solver. }
        pose proof (foldr_fib_expr_result_sound
          (elements X) X e ν ∅ m σw (store_restrict σw {[ν]})
          (NoDup_elements X)
          Hdisj_empty_X
          Hmodel_fold Hσw eq_refl) as Hstore.
        assert (HelemsX : (list_to_set (elements X) : aset) = X).
        { apply set_eq. intros z. rewrite elem_of_list_to_set, elem_of_elements. reflexivity. }
        rewrite HelemsX in Hstore.
        replace ((∅ : Store) ∪ store_restrict σw X) with (store_restrict σw X) in Hstore.
        2:{ apply (map_eq (M := gmap atom)). intros z.
            rewrite lookup_union_r; [reflexivity | apply lookup_empty]. }
        rewrite store_restrict_restrict in Hstore.
        replace (X ∩ X) with X in Hstore by set_solver.
        destruct (expr_result_store_elim ν (subst_map (store_restrict σw X) e)
          (store_restrict σw {[ν]}) Hstore)
          as [vx [Hνstore [_ [_ Hsteps]]]].
        exists (store_restrict σw X), vx. split.
        -- exists σw. split; [exact Hσw | reflexivity].
        -- split.
           ++ rewrite store_restrict_idemp.
              ** exact Hsteps.
              ** rewrite store_restrict_dom.
                 pose proof (wfworld_store_dom m σw Hσw) as Hdomσw.
                 set_solver.
           ++ rewrite <- Hrestrict.
              by apply store_restrict_union_singleton_insert_from_projection.
      * intros [σ [vx [Hσ [Hsteps ->]]]].
        destruct Hσ as [σw [Hσw HrestrictX]].
        assert (Hinput_closed : closed_tm (subst_map (store_restrict σ X) e)).
        {
          apply msubst_closed_tm.
          - exact (world_store_closed_on_restrict X X m ltac:(set_solver) Hclosed σ
              ltac:(exists σw; split; eauto)).
          - exact Hlc.
          - change (fv_tm e ⊆ dom (store_restrict σ X)).
            rewrite store_restrict_dom.
            pose proof (wfworld_store_dom (res_restrict m X) σ
              ltac:(exists σw; split; eauto)) as Hdomσ.
            simpl in Hdomσ. set_solver.
        }
        pose proof (steps_closed_result _ _ Hinput_closed Hsteps)
          as [Hvx_closed Hvx_lc].
        assert (Hstore :
          expr_result_in_store
            (store_restrict ((∅ : Store) ∪ store_restrict σw (list_to_set (elements X))) X)
            e ν {[ν := vx]}).
        {
          assert (HelemsX : (list_to_set (elements X) : aset) = X).
          { apply set_eq. intros z. rewrite elem_of_list_to_set, elem_of_elements. reflexivity. }
          rewrite HelemsX.
          replace ((∅ : Store) ∪ store_restrict σw X) with (store_restrict σw X).
          2:{ apply (map_eq (M := gmap atom)). intros z.
              rewrite lookup_union_r; [reflexivity | apply lookup_empty]. }
          rewrite HrestrictX.
          apply expr_result_store_intro.
          - exact Hvx_closed.
          - exact Hvx_lc.
          - exact Hsteps.
        }
        assert (Hdisj_empty_X : dom (∅ : Store) ## (list_to_set (elements X) : aset)).
        { rewrite dom_empty_L. set_solver. }
        destruct (foldr_fib_expr_result_complete_paired
          (elements X) X e ν ∅ m σw {[ν := vx]}
          (NoDup_elements X)
          Hdisj_empty_X Hmodel_fold Hσw Hstore)
          as [τ [Hτm [HτX Hτν]]].
        exists τ. split; [exact Hτm |].
        assert (HelemsX : (list_to_set (elements X) : aset) = X).
        { apply set_eq. intros z. rewrite elem_of_list_to_set, elem_of_elements. reflexivity. }
        rewrite HelemsX in HτX.
        replace (X ∪ {[ν]}) with ({[ν]} ∪ X) by set_solver.
        transitivity (store_restrict (<[ν := vx]> σ) ({[ν]} ∪ X)).
        -- eapply (store_restrict_union_singleton_eq_from_parts
             τ (<[ν := vx]> σ) ν X).
           ++ exact HνX.
           ++ rewrite Hτν.
              apply (map_eq (M := gmap atom)). intros z.
              rewrite store_restrict_lookup.
              destruct (decide (z = ν)) as [->|Hzν].
              ** rewrite decide_True by set_solver.
                 symmetry.
                 change ((<[ν := vx]> σ : Store) !! ν = ({[ν := vx]} : Store) !! ν).
                 rewrite lookup_insert.
                 rewrite lookup_singleton.
                 destruct (decide (ν = ν)) as [_|Hneq]; [reflexivity | contradiction].
              ** rewrite decide_False by set_solver.
                 change (({[ν := vx]} : Store) !! z = None).
                 rewrite lookup_singleton, decide_False by congruence.
                 reflexivity.
           ++ rewrite store_restrict_insert_notin by exact HνX.
              rewrite HτX.
              rewrite <- HrestrictX.
              symmetry. apply store_restrict_idemp.
              rewrite store_restrict_dom. set_solver.
        -- apply (map_eq (M := gmap atom)). intros z.
           rewrite store_restrict_lookup.
           destruct (decide (z = ν)) as [->|Hzν].
           ++ rewrite decide_True by set_solver. reflexivity.
           ++ destruct (decide (z ∈ X)) as [HzX|HzX].
              ** rewrite decide_True by set_solver. reflexivity.
              ** rewrite decide_False by set_solver.
                 symmetry.
                 rewrite lookup_insert_ne by congruence.
                 apply not_elem_of_dom.
                 pose proof (wfworld_store_dom (res_restrict m X) σ
                   ltac:(exists σw; split; eauto)) as Hdomσ.
                 simpl in Hdomσ. rewrite Hdomσ. set_solver.
  - intros [Hfresh [Hresult Heq]].
    assert (Hscope_dom : X ∪ {[ν]} ⊆ world_dom (m : World)).
    {
      pose proof (f_equal (fun w : WfWorld => world_dom (w : World)) Heq)
        as Hdom_eq.
      assert (Hνm : ν ∈ world_dom (m : World)).
      {
        assert (Hνleft : ν ∈ world_dom (res_restrict m (X ∪ {[ν]}) : World)).
        {
          rewrite Hdom_eq.
          simpl. unfold let_result_world_on, let_result_raw_world_on. simpl.
          set_solver.
        }
        simpl in Hνleft.
        apply elem_of_intersection in Hνleft as [Hνm _].
        exact Hνm.
      }
      intros z Hz.
      apply elem_of_union in Hz as [HzX | Hzν].
      - apply HXm. exact HzX.
      - apply elem_of_singleton in Hzν. subst z. exact Hνm.
    }
    apply fib_vars_models_intro.
    + unfold formula_scoped_in_world.
      intros z Hz.
      apply elem_of_union in Hz as [Hzempty | Hz]; [set_solver |].
      unfold FExprResultOn, FExprResultOnRaw in Hz.
      rewrite fib_vars_formula_fv in Hz. simpl in Hz.
      unfold stale, stale_logic_qualifier in Hz. simpl in Hz.
      set_solver.
    + eapply (fib_vars_obligation_intro
        X (FAtom (expr_logic_qual_on X e ν))
        (result_world_slice_inv X ν
          (let_result_world_on X e ν (res_restrict m X) Hfresh Hresult))).
      * eapply result_world_slice_inv_initial.
        -- exact Hscope_dom.
        -- exact Heq.
      * intros x Y ρ' w' HxX HxY Hinv.
        eapply result_world_slice_inv_disjoint; [exact HxX | | exact Hinv].
        clear -HxY. set_solver.
      * intros x Y ρ' w' HxX HxY Hinv Hdisj σx Hproj.
        assert (Hfixed_step : X ∖ Y = (X ∖ ({[x]} ∪ Y)) ∪ {[x]}).
        {
          apply set_eq. intros z.
          rewrite elem_of_union, !elem_of_difference, elem_of_union,
            elem_of_singleton.
          split.
          - intros [HzX HzY].
            destruct (decide (z = x)) as [->|Hzx]; [right; reflexivity |].
            left. repeat split; try exact HzX; try exact HzY.
            intros [Hzx' | HzY']; [contradiction | contradiction].
          - intros [[HzX Hznot] | ->].
            + split; [exact HzX |].
              intros HzY. apply Hznot. right. exact HzY.
            + split; [exact HxX | exact HxY].
        }
        rewrite Hfixed_step.
        eapply result_world_slice_inv_step; [exact HxX | | exact Hinv | exact Hdisj].
        clear -HxY. set_solver.
      * intros ρ' w' Hinv.
        eapply (result_world_slice_inv_base X e ν (res_restrict m X)).
        -- change (world_dom (m : World) ∩ X = X). set_solver.
        -- exact Hfv.
        -- exact Hlc.
        -- eapply world_store_closed_on_restrict; [set_solver | exact Hclosed].
        -- exact Hinv.
Qed.

Lemma let_result_world_on_models_FExprResultOn :
  ∀ X e ν (n : WfWorld) Hfresh Hresult,
    fv_tm e ⊆ X →
    lc_tm e →
    ν ∉ X →
    X ⊆ world_dom (n : World) →
    world_store_closed_on X n →
    let_result_world_on X e ν n Hfresh Hresult ⊨ FExprResultOn X e ν.
Proof.
  intros X e ν n Hfresh Hresult Hfv Hlc HνX HXn Hclosed.
  apply (proj2 ((FExprResultOn_iff_let_result_world_on
    X e ν (let_result_world_on X e ν n Hfresh Hresult))
    Hfv Hlc HνX
    ltac:(simpl; unfold let_result_world_on, let_result_raw_world_on; simpl; set_solver)
    ltac:(by apply let_result_world_on_store_closed_on))).
  - assert (Hfresh0 :
      ν ∉ world_dom (res_restrict (let_result_world_on X e ν n Hfresh Hresult) X : World))
      by (simpl; set_solver).
    assert (Hresult0 :
      ∀ σ, (res_restrict (let_result_world_on X e ν n Hfresh Hresult) X : World) σ →
        ∃ vx, subst_map (store_restrict σ X) e →* tret vx).
    {
      intros σ Hσ.
      simpl in Hσ.
      destruct Hσ as [sigmanu [[σ0 [vx [Hσ0 [Hsteps ->]]]] Hrestrict]].
      rewrite store_restrict_insert_notin in Hrestrict by exact HνX.
      subst σ.
      exists vx.
      rewrite store_restrict_restrict.
      replace (X ∩ X) with X by set_solver.
      exact Hsteps.
    }
    exists Hfresh0, Hresult0.
    apply wfworld_ext. apply world_ext.
    + simpl. set_solver.
    + intros sigmanu. simpl. split.
      * intros [σfull [[σ0 [vx [Hσ0 [Hsteps ->]]]] Hrestrict]].
        rewrite store_restrict_insert_in in Hrestrict by set_solver.
        inversion Hrestrict. subst sigmanu.
        exists (store_restrict σ0 X), vx.
        split.
        -- exists (<[ν := vx]> σ0). split.
           ++ exists σ0, vx. repeat split; eauto.
           ++ rewrite store_restrict_insert_notin by exact HνX.
              reflexivity.
        -- split.
           ++ rewrite store_restrict_idemp.
              ** exact Hsteps.
              ** rewrite store_restrict_dom.
                 pose proof (wfworld_store_dom n σ0 Hσ0) as Hdomσ0.
                 set_solver.
           ++ f_equal.
              apply store_restrict_union_singleton_fresh_eq.
              apply not_elem_of_dom.
              pose proof (wfworld_store_dom n σ0 Hσ0) as Hdomσ0.
              rewrite Hdomσ0. exact Hfresh.
      * intros [σ [vx [Hσ [Hsteps ->]]]].
        destruct Hσ as [sigmanu [[σ0 [vx0 [Hσ0 [Hsteps0 ->]]]] Hrestrict]].
        rewrite store_restrict_insert_notin in Hrestrict by exact HνX.
        subst σ.
        exists (<[ν := vx]> σ0). split.
        -- exists σ0, vx. repeat split; eauto.
           rewrite store_restrict_restrict in Hsteps.
           replace (X ∩ X) with X in Hsteps by set_solver.
           exact Hsteps.
        -- rewrite store_restrict_insert_in by set_solver.
           rewrite store_restrict_union_singleton_fresh_eq.
           2:{
             apply not_elem_of_dom.
             pose proof (wfworld_store_dom n σ0 Hσ0) as Hdomσ0.
             rewrite Hdomσ0. exact Hfresh.
           }
           reflexivity.
Qed.

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
        (∀ n,
          n ⊨ FExprResultOn X e y →
          n ⊨ formula_rename_atom (fresh_for D) y
                 (FExprResultOn X e (fresh_for D))) →
        let_result_world_on X e y m Hfresh Hresult ⊨
          formula_rename_atom (fresh_for D) y (body (fresh_for D)).
Proof.
  intros Hfv Hlc HX Hclosed.
  unfold fresh_forall, res_models, res_models_with_store.
  simpl. intros [_ [L [HL Hforall]]].
  exists (L ∪ D ∪ X ∪ fv_tm e).
  split; [set_solver |].
  intros y Hy Hfresh Hresult Hante.
  assert (HyL : y ∉ L) by set_solver.
  set (w := let_result_world_on X e y m Hfresh Hresult).
  pose proof (Hforall y HyL w) as Himpl_fuel.
  specialize (Himpl_fuel ltac:(subst w; reflexivity)).
  specialize (Himpl_fuel (let_result_world_on_restrict X e y m Hfresh Hresult)).
  assert (Himpl :
    w ⊨ FImpl
      (formula_rename_atom (fresh_for D) y (FExprResultOn X e (fresh_for D)))
      (formula_rename_atom (fresh_for D) y (body (fresh_for D)))).
  {
    unfold res_models, res_models_with_store.
    simpl.
    destruct Himpl_fuel as [Hscope Himpl_cont].
    split; [exact Hscope |].
    intros m' Hle Hant.
    eapply res_models_with_store_fuel_irrel.
    3: {
      apply Himpl_cont; [exact Hle |].
      eapply res_models_with_store_fuel_irrel; [| | exact Hant];
        rewrite ?formula_rename_preserves_measure; lia.
    }
    all: rewrite ?formula_rename_preserves_measure; lia.
  }
  eapply res_models_impl_elim.
  - exact Himpl.
  - apply Hante.
    subst w.
    apply let_result_world_on_models_FExprResultOn.
    + exact Hfv.
    + exact Hlc.
    + set_solver.
    + simpl. set_solver.
    + exact Hclosed.
Qed.

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
        (∀ n,
          n ⊨ FExprResultOn X e y →
          n ⊨ formula_rename_atom (fresh_for D) y
                 (FExprResultOn X e (fresh_for D))) →
        (∀ n,
          n ⊨ formula_rename_atom (fresh_for D) y (body (fresh_for D)) →
          n ⊨ body y) →
        let_result_world_on X e y m Hfresh Hresult ⊨ body y.
Proof.
  intros Hfv Hlc HX Hclosed Hforall.
  destruct (fresh_forall_expr_result_to_let_result_world_renamed
    X e D body m Hfv Hlc HX Hclosed Hforall) as [L [HL Huse]].
  exists L. split; [exact HL |].
  intros y Hy Hfresh Hresult Hante Hbody.
  apply Hbody.
  eapply Huse; eauto.
Qed.

Definition expr_result_equiv_in_world
    (X : aset) (n : WfWorld) (e e' : tm) : Prop :=
  fv_tm e ∪ fv_tm e' ⊆ X ∧
  X ⊆ world_dom (n : World) ∧
  ∀ σ v,
    (n : World) σ →
    (subst_map (store_restrict σ X) e →* tret v ↔
     subst_map (store_restrict σ X) e' →* tret v).

Definition expr_result_equiv_future
    (X : aset) (m : WfWorld) (e e' : tm) : Prop :=
  ∀ n, m ⊑ n → expr_result_equiv_in_world X n e e'.

Lemma expr_result_equiv_in_world_refl X (n : WfWorld) e :
  fv_tm e ⊆ X →
  X ⊆ world_dom (n : World) →
  expr_result_equiv_in_world X n e e.
Proof.
  intros Hfv HX. split; [set_solver |].
  split; [exact HX |].
  intros σ v _; split; intros Hsteps; exact Hsteps.
Qed.

Lemma expr_result_equiv_in_world_sym X (n : WfWorld) e e' :
  expr_result_equiv_in_world X n e e' →
  expr_result_equiv_in_world X n e' e.
Proof.
  intros [Hfv [HX Heq]]. split; [set_solver |].
  split; [exact HX |].
  intros σ v Hσ. symmetry. apply Heq. exact Hσ.
Qed.

Lemma expr_result_equiv_in_world_trans X (n : WfWorld) e1 e2 e3 :
  expr_result_equiv_in_world X n e1 e2 →
  expr_result_equiv_in_world X n e2 e3 →
  expr_result_equiv_in_world X n e1 e3.
Proof.
  intros [Hfv12 [HX H12]] [Hfv23 [_ H23]].
  split; [set_solver |]. split; [exact HX |].
  intros σ v Hσ. split; intros Hsteps.
  - apply (proj1 (H23 σ v Hσ)).
    apply (proj1 (H12 σ v Hσ)). exact Hsteps.
  - apply (proj2 (H12 σ v Hσ)).
    apply (proj2 (H23 σ v Hσ)). exact Hsteps.
Qed.

Lemma expr_result_equiv_on_to_in_world X (n : WfWorld) e e' :
  expr_result_equiv_on X e e' →
  X ⊆ world_dom (n : World) →
  (∀ σ, (n : World) σ → closed_env (store_restrict σ X)) →
  expr_result_equiv_in_world X n e e'.
Proof.
  intros [[Hfv12 H12] [Hfv21 H21]] HX Hclosed.
  split; [exact Hfv12 |]. split; [exact HX |].
  intros σ v Hσ.
  assert (Hdom : dom (store_restrict σ X) = X).
  {
    rewrite store_restrict_dom.
    pose proof (wfworld_store_dom n σ Hσ) as Hσdom.
    set_solver.
  }
  split; intros Hsteps.
  - apply H12; [exact Hdom | apply Hclosed; exact Hσ | exact Hsteps].
  - apply H21; [exact Hdom | apply Hclosed; exact Hσ | exact Hsteps].
Qed.

Lemma let_result_world_on_expr_result_equiv_in_world
    X e e' x (n : WfWorld) Hfresh Hresult Hresult' :
  expr_result_equiv_in_world X n e e' →
  let_result_world_on X e x n Hfresh Hresult =
  let_result_world_on X e' x n Hfresh Hresult'.
Proof.
  intros [_ [_ Hequiv]].
  apply wfworld_ext. apply world_ext.
  - simpl. reflexivity.
  - intros σx. simpl. split.
    + intros [σ [vx [Hσ [Hsteps ->]]]].
      exists σ, vx. split; [exact Hσ |]. split.
      * apply (proj1 (Hequiv σ vx Hσ)). exact Hsteps.
      * reflexivity.
    + intros [σ [vx [Hσ [Hsteps ->]]]].
      exists σ, vx. split; [exact Hσ |]. split.
      * apply (proj2 (Hequiv σ vx Hσ)). exact Hsteps.
      * reflexivity.
Qed.

Lemma FExprResultOn_expr_result_equiv_in_world
    X e e' ν (m : WfWorld) :
  fv_tm e ∪ fv_tm e' ⊆ X →
  lc_tm e →
  lc_tm e' →
  ν ∉ X →
  X ⊆ world_dom (m : World) →
  world_store_closed_on X m →
  expr_result_equiv_in_world X (res_restrict m X) e e' →
  m ⊨ FExprResultOn X e ν →
  m ⊨ FExprResultOn X e' ν.
Proof.
  intros Hfv Hlce Hlce' HνX HXm Hclosed Hequiv Hmodel.
  pose proof (proj1 (FExprResultOn_iff_let_result_world_on
    X e ν m ltac:(set_solver) Hlce HνX HXm Hclosed) Hmodel)
    as [Hfresh [Hresult Heq]].
  assert (Hresult' :
    ∀ σ, (res_restrict m X : World) σ →
      ∃ vx, subst_map (store_restrict σ X) e' →* tret vx).
  {
    intros σ Hσ.
    destruct (Hresult σ Hσ) as [vx Hsteps].
    exists vx.
    apply (proj1 (proj2 (proj2 Hequiv) σ vx Hσ)).
    exact Hsteps.
  }
  apply (proj2 (FExprResultOn_iff_let_result_world_on
    X e' ν m ltac:(set_solver) Hlce' HνX HXm Hclosed)).
  exists Hfresh, Hresult'.
  rewrite Heq.
  apply let_result_world_on_expr_result_equiv_in_world.
  exact Hequiv.
Qed.

Lemma FExprResultOn_expr_result_equiv_future
    X e e' ν (m : WfWorld) :
  fv_tm e ∪ fv_tm e' ⊆ X →
  lc_tm e →
  lc_tm e' →
  ν ∉ X →
  X ⊆ world_dom (m : World) →
  world_store_closed_on X m →
  expr_result_equiv_future X (res_restrict m X) e e' →
  m ⊨ FExprResultOn X e ν →
  m ⊨ FExprResultOn X e' ν.
Proof.
  intros Hfv Hlce Hlce' HνX HXm Hclosed Hfuture Hmodel.
  eapply FExprResultOn_expr_result_equiv_in_world.
  - exact Hfv.
  - exact Hlce.
  - exact Hlce'.
  - exact HνX.
  - exact HXm.
  - exact Hclosed.
  - apply Hfuture. reflexivity.
  - exact Hmodel.
Qed.
