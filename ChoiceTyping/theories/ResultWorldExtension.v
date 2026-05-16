(** * ChoiceTyping.ResultWorldExtension

    Result-world facts phrased through explicit world extensions. *)

From CoreLang Require Import BasicTypingProps OperationalProps.
From ChoiceAlgebra Require Import WorldExtension.
From ChoiceTyping Require Import LetResultWorld ResultWorldExprCont.
From Stdlib Require Import Logic.Classical_Prop.

Local Lemma store_union_singleton_insert_fresh (σ : Store) x v :
  x ∉ dom σ →
  σ ∪ ({[x := v]} : Store) = <[x := v]> σ.
Proof.
  intros Hfresh.
  change ({[x := v]} : Store) with (<[x := v]> (∅ : Store)).
  rewrite store_insert_union_r_fresh by exact Hfresh.
  rewrite (map_union_empty σ). reflexivity.
Qed.

Definition expr_result_extension_fiber
    (X : aset) (e : tm) (x : atom) (σ : Store) : WfWorld.
Proof.
  refine (exist _ {|
    world_dom := {[x]};
    world_stores := fun σx =>
      dom σx = {[x]} /\
      ((∃ vx,
          σx = ({[x := vx]} : Store) /\
          subst_map (store_restrict σ (fv_tm e)) e →* tret vx) \/
       (~ (∃ vx, subst_map (store_restrict σ (fv_tm e)) e →* tret vx) /\
        σx = singleton_extension_store x))
  |} _).
  constructor.
  - destruct (classic
      (∃ vx, subst_map (store_restrict σ (fv_tm e)) e →* tret vx))
      as [[vx Hsteps] | Hnone].
    + exists ({[x := vx]} : Store). split.
      * rewrite dom_singleton_L. reflexivity.
      * left. eauto.
    + exists (singleton_extension_store x). split.
      * apply singleton_extension_store_dom.
      * right. eauto.
  - intros σx [Hdom _]. exact Hdom.
Defined.

Definition expr_result_extension (X : aset) (e : tm) (x : atom) (Hfresh : x ∉ X)
    : fiber_extension :=
  mk_forall_extension X x (expr_result_extension_fiber X e x) Hfresh
    ltac:(intros; simpl; reflexivity)
    ltac:(intros σ _; destruct (world_wf (expr_result_extension_fiber X e x σ))
      as [Hne _]; exact Hne).

Lemma expr_result_extension_shape X (e : tm) x Hfresh :
  forall_extension_shape X x (expr_result_extension X e x Hfresh).
Proof. unfold forall_extension_shape, expr_result_extension, mk_forall_extension,
  mk_fiber_extension; simpl; eauto. Qed.

Lemma expr_result_extension_extend_by
    X (e : tm) x (m : WfWorld) HfreshX Hfreshm Hresult :
  X ⊆ world_dom (m : World) →
  fv_tm e ⊆ X →
  m #> expr_result_extension X e x HfreshX ~~>
    let_result_world_on e x m Hfreshm Hresult.
Proof.
  intros HX Hfv.
  unfold res_extend_by, expr_result_extension, mk_forall_extension,
    mk_fiber_extension. simpl.
  split.
  {
    constructor; simpl.
    - exact HX.
    - set_solver.
  }
  split.
  {
    change (world_dom (let_result_world_on e x m Hfreshm Hresult : World) =
      world_dom (m : World) ∪ {[x]}).
    apply let_result_world_on_dom.
  }
  intros σx. split.
  - intros Hσx.
    destruct (let_result_world_on_elim e x m Hfreshm Hresult σx Hσx)
      as [σ [vx [Hσ [Hsteps ->]]]].
    exists σ, ({[x := vx]} : Store). split; [exact Hσ |].
    split.
    + split.
      * rewrite dom_singleton_L. reflexivity.
      * left. exists vx. split; [reflexivity |].
        replace (store_restrict (store_restrict σ X) (fv_tm e))
          with (store_restrict σ (fv_tm e)).
        -- exact Hsteps.
        -- rewrite store_restrict_twice_subset by exact Hfv.
           reflexivity.
    + replace (σ ∪ ({[x := vx]} : Store)) with (<[x := vx]> σ).
      * reflexivity.
      * symmetry. apply store_union_singleton_insert_fresh.
        rewrite (wfworld_store_dom m σ Hσ). exact Hfreshm.
  - intros [σ [σe [Hσ [Hfiber ->]]]].
    simpl in Hfiber.
    destruct Hfiber as [_ [[vx [-> Hsteps]] | [Hnone ->]]].
    + replace (σ ∪ ({[x := vx]} : Store)) with (<[x := vx]> σ).
      * eapply (let_result_world_on_member e x m Hfreshm Hresult σ vx);
          [exact Hσ |].
        replace (store_restrict σ (fv_tm e))
          with (store_restrict (store_restrict σ X) (fv_tm e)).
        -- exact Hsteps.
        -- rewrite store_restrict_twice_subset by exact Hfv.
           reflexivity.
      * symmetry. apply store_union_singleton_insert_fresh.
        rewrite (wfworld_store_dom m σ Hσ). exact Hfreshm.
    + exfalso. apply Hnone.
      destruct (Hresult σ Hσ) as [vx Hsteps].
      exists vx.
      replace (store_restrict (store_restrict σ X) (fv_tm e))
        with (store_restrict σ (fv_tm e)).
      * exact Hsteps.
      * rewrite store_restrict_twice_subset by exact Hfv.
        reflexivity.
Qed.

Lemma let_result_world_on_total_as_extend_by
    X e x (m : WfWorld)
    (Hfresh : x ∉ world_dom (m : World))
    (Htotal : expr_total_result_on X e m) :
  ∃ F,
    forall_extension_shape (world_dom (m : World)) x F ∧
    m #> F ~~> let_result_world_on_total X e x m Hfresh Htotal.
Proof.
  unfold let_result_world_on_total.
  eapply forall_world_as_extend_by.
  - exact Hfresh.
  - apply let_result_world_on_dom.
  - apply let_result_world_on_restrict.
Qed.

Lemma let_result_world_on_as_extend_by
    e x (m : WfWorld)
    (Hfresh : x ∉ world_dom (m : World)) Hresult :
  ∃ F,
    forall_extension_shape (world_dom (m : World)) x F ∧
    m #> F ~~> let_result_world_on e x m Hfresh Hresult.
Proof.
  eapply forall_world_as_extend_by.
  - exact Hfresh.
  - apply let_result_world_on_dom.
  - apply let_result_world_on_restrict.
Qed.

Lemma result_witness_lift_extend
    e (m my : WfWorld) F :
  fv_tm e ⊆ world_dom (m : World) →
  m #> F ~~> my →
  (∀ σ, (m : World) σ →
    ∃ vx, subst_map (store_restrict σ (fv_tm e)) e →* tret vx) →
  ∀ σ, (my : World) σ →
    ∃ vx, subst_map (store_restrict σ (fv_tm e)) e →* tret vx.
Proof.
  intros Hfv Hext Hresult σ Hσ.
  pose proof (res_extend_by_restrict_base _ _ _ Hext) as Hrestrict.
  assert ((res_restrict my (world_dom (m : World)) : World)
      (store_restrict σ (world_dom (m : World)))) as Hσm.
  { exists σ. split; [exact Hσ | reflexivity]. }
  rewrite Hrestrict in Hσm.
  destruct (Hresult _ Hσm) as [vx Hsteps].
  exists vx.
  rewrite store_restrict_twice_subset in Hsteps by exact Hfv.
  exact Hsteps.
Qed.

Lemma let_result_world_on_forall_extension
    e x (m my : WfWorld) Hfresh Hresult Hfresh_my Hresult_my
    y F :
  fv_tm e ⊆ world_dom (m : World) →
  y ∉ world_dom (let_result_world_on e x m Hfresh Hresult : World) →
  forall_extension_shape (world_dom (m : World)) y F →
  m #> F ~~> my →
  ∃ G,
    forall_extension_shape
      (world_dom (let_result_world_on e x m Hfresh Hresult : World)) y G ∧
    let_result_world_on e x m Hfresh Hresult #> G ~~>
      let_result_world_on e x my Hfresh_my Hresult_my.
Proof.
  intros Hfv Hy HFshape Hext.
  destruct HFshape as [_ HFout].
  eapply forall_world_as_extend_by.
  - exact Hy.
  - rewrite !let_result_world_on_dom.
    rewrite (res_extend_by_dom _ _ _ Hext), HFout.
    set_solver.
  - rewrite let_result_world_on_dom.
    eapply let_result_world_on_restrict_extension.
    + eapply res_extend_by_restrict_base. exact Hext.
    + exact Hfv.
    + eapply res_extend_by_dom_subset. exact Hext.
    + exact Hfresh.
Qed.

Lemma let_result_world_on_forall_extension_total
    e x (m my : WfWorld) Hfresh Hresult y F :
  fv_tm e ⊆ world_dom (m : World) →
  y ∉ world_dom (let_result_world_on e x m Hfresh Hresult : World) →
  forall_extension_shape (world_dom (m : World)) y F →
  m #> F ~~> my →
  ∃ (Hfresh_my : x ∉ world_dom (my : World))
    (Hresult_my : ∀ σ, (my : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e)) e →* tret vx)
    G,
    forall_extension_shape
      (world_dom (let_result_world_on e x m Hfresh Hresult : World)) y G ∧
    let_result_world_on e x m Hfresh Hresult #> G ~~>
      let_result_world_on e x my Hfresh_my Hresult_my.
Proof.
  intros Hfv Hy HFshape Hext.
  destruct HFshape as [HFin HFout].
  assert (Hfresh_my : x ∉ world_dom (my : World)).
  {
    rewrite (res_extend_by_dom _ _ _ Hext), HFout.
    rewrite let_result_world_on_dom in Hy.
    set_solver.
  }
  assert (Hresult_my : ∀ σ, (my : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e)) e →* tret vx).
  { eapply result_witness_lift_extend; eauto. }
  exists Hfresh_my, Hresult_my.
  eapply let_result_world_on_forall_extension; eauto.
  split; eauto.
Qed.

Lemma let_result_world_on_forall_extension_commute
    X e x (m my : WfWorld) HfreshX Hfresh Hresult
    y F :
  X ⊆ world_dom (m : World) →
  fv_tm e ⊆ X →
  y ∉ world_dom (let_result_world_on e x m Hfresh Hresult : World) →
  forall_extension_shape (world_dom (m : World)) y F →
  m #> F ~~> my →
  ∃ (Hfresh_my : x ∉ world_dom (my : World))
    (Hresult_my : ∀ σ, (my : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e)) e →* tret vx)
    G,
    forall_extension_shape
      (world_dom (let_result_world_on e x m Hfresh Hresult : World)) y G ∧
    m #> expr_result_extension X e x HfreshX ~~>
      let_result_world_on e x m Hfresh Hresult ∧
    my #> expr_result_extension X e x HfreshX ~~>
      let_result_world_on e x my Hfresh_my Hresult_my ∧
    let_result_world_on e x m Hfresh Hresult #> G ~~>
      let_result_world_on e x my Hfresh_my Hresult_my.
Proof.
  intros HXm Hfv Hy HFshape Hext.
  destruct (let_result_world_on_forall_extension_total
    e x m my Hfresh Hresult y F ltac:(set_solver) Hy HFshape Hext)
    as [Hfresh_my [Hresult_my [G [HGshape HGext]]]].
  exists Hfresh_my, Hresult_my, G.
  split; [exact HGshape |].
  split.
  - eapply expr_result_extension_extend_by; eauto.
  - split; [| exact HGext].
    eapply expr_result_extension_extend_by; eauto.
    etrans; [exact HXm |].
    eapply res_extend_by_dom_subset. exact Hext.
Qed.

Local Lemma store_restrict_result_forall_base
    X Z x y (σ σy : Store) vx :
  dom σ = X →
  dom σy = {[y]} →
  x ∉ X →
  y ∉ X →
  x <> y →
  Z ⊆ X →
  store_restrict
    (store_restrict ((<[x := vx]> σ) ∪ σy) (X ∪ {[y]})) Z =
  store_restrict σ Z.
Proof.
  intros Hdomσ Hdomσy HxX HyX Hxy HZX.
  apply (map_eq (M := gmap atom)). intros z.
  rewrite !store_restrict_lookup.
  destruct (decide (z ∈ Z)) as [Hz|Hz]; [| reflexivity].
  rewrite decide_True by set_solver.
  rewrite (lookup_union_l' (<[x := vx]> σ) σy z).
  - rewrite lookup_insert_ne by set_solver. reflexivity.
  - rewrite lookup_insert_ne by set_solver.
    destruct (σ !! z) as [v|] eqn:Hσz; eauto.
    exfalso.
    apply not_elem_of_dom in Hσz.
    apply Hσz. rewrite Hdomσ. set_solver.
Qed.

Local Lemma result_projection_dom (X : aset) x (σ : gmap atom value) vx :
  dom σ = X →
  dom (store_restrict (<[x := vx]> σ) (X ∪ {[x]})) = X ∪ {[x]}.
Proof.
  intros Hdomσ.
  rewrite (store_restrict_dom (<[x := vx]> σ) (X ∪ {[x]})).
  rewrite (dom_insert_L (M := gmap atom) σ x vx), Hdomσ. set_solver.
Qed.

Lemma let_result_world_on_forall_extension_recompose_typed
    (Σ : gmap atom ty) (T : ty) e x
    (m n : WfWorld) Hfresh Hresult y G :
  Σ ⊢ₑ e ⋮ T →
  world_dom (m : World) = dom Σ →
  world_closed_on (dom Σ) m →
  y ∉ world_dom (let_result_world_on e x m Hfresh Hresult : World) →
  forall_extension_shape
    (world_dom (let_result_world_on e x m Hfresh Hresult : World)) y G →
  let_result_world_on e x m Hfresh Hresult #> G ~~> n →
  ∃ (my : WfWorld)
    (Hfresh_my : x ∉ world_dom (my : World))
    (Hresult_my : ∀ σ, (my : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e)) e →* tret vx),
    world_dom (my : World) = world_dom (m : World) ∪ {[y]} ∧
    res_restrict my (world_dom (m : World)) = m ∧
    n = let_result_world_on e x my Hfresh_my Hresult_my.
Proof.
  intros Hty Hdom Hclosed Hy HGshape Hext.
  destruct HGshape as [HGin HGout].
  pose proof (basic_typing_contains_fv_tm Σ e T Hty) as HfvΣ.
  assert (Hfv : fv_tm e ⊆ world_dom (m : World)).
  { rewrite Hdom. exact HfvΣ. }
  pose proof (res_extend_by_dom _ _ _ Hext) as Hdom_n.
  set (X := world_dom (m : World)).
  set (Xy := X ∪ {[y]}).
  set (m1 := let_result_world_on e x m Hfresh Hresult).
  set (my := res_restrict n Xy).
  assert (Hdom_m1 : world_dom (m1 : World) = X ∪ {[x]}).
  { subst m1 X. apply let_result_world_on_dom. }
  assert (HyX : y ∉ X).
  { subst X m1. rewrite let_result_world_on_dom in Hy. set_solver. }
  assert (Hxy : x <> y).
  { subst m1 X. rewrite let_result_world_on_dom in Hy. set_solver. }
  assert (Hdom_my : world_dom (my : World) = Xy).
  {
    subst my Xy X m1. simpl.
    rewrite Hdom_n, HGout, let_result_world_on_dom.
    set_solver.
  }
  assert (Hrestrict_my : res_restrict my X = m).
  {
    subst my Xy X.
    rewrite res_restrict_restrict_eq.
    replace ((world_dom (m : World) ∪ {[y]}) ∩ world_dom (m : World))
      with (world_dom (m : World)) by set_solver.
    replace (world_dom (m : World))
      with (world_dom (let_result_world_on e x m Hfresh Hresult : World)
        ∩ world_dom (m : World))
      by (rewrite let_result_world_on_dom; set_solver).
    rewrite <- res_restrict_restrict_eq.
    rewrite (res_extend_by_restrict_base _ _ _ Hext).
    apply let_result_world_on_restrict.
  }
  assert (Hfresh_my : x ∉ world_dom (my : World)).
  { rewrite Hdom_my. subst Xy X. set_solver. }
  assert (Hresult_my : ∀ σ, (my : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e)) e →* tret vx).
  {
    intros σ Hσmy.
    subst my. simpl in Hσmy.
    destruct Hσmy as [σn [Hσn HσnXy]].
    apply (proj1 (res_extend_by_store_iff _ _ _ _ Hext)) in Hσn.
    destruct Hσn as [σx [σy [Hσx [Hσy ->]]]].
    subst m1.
    destruct (let_result_world_on_elim e x m Hfresh Hresult σx Hσx)
      as [σm [vx [Hσm [Hsteps ->]]]].
    exists vx.
    replace (store_restrict σ (fv_tm e))
      with (store_restrict σm (fv_tm e)).
    - exact Hsteps.
    - rewrite <- HσnXy.
      symmetry. eapply store_restrict_result_forall_base.
      + apply wfworld_store_dom. exact Hσm.
      + rewrite (wfworld_store_dom
          (ext_fun G (store_restrict (<[x:=vx]> σm) (ext_in G))) σy Hσy).
        rewrite (ext_fun_dom G).
        * exact HGout.
        * rewrite HGin, let_result_world_on_dom.
          apply result_projection_dom.
          apply wfworld_store_dom. exact Hσm.
      + exact Hfresh.
      + exact HyX.
      + exact Hxy.
      + exact Hfv.
  }
  exists my, Hfresh_my, Hresult_my.
  repeat split; [exact Hdom_my | exact Hrestrict_my |].
  apply wfworld_ext. apply world_ext.
  - rewrite Hdom_n, HGout.
    subst Xy X m1. rewrite let_result_world_on_dom.
    set_solver.
  - intros σn. split.
    + intros Hσn.
      apply (proj1 (res_extend_by_store_iff _ _ _ _ Hext)) in Hσn.
      destruct Hσn as [σx [σy [Hσx [Hσy ->]]]].
      subst m1.
      destruct (let_result_world_on_elim e x m Hfresh Hresult σx Hσx)
        as [σm [vx [Hσm [Hsteps ->]]]].
      exists (store_restrict ((<[x:=vx]> σm) ∪ σy) Xy), vx.
      split.
      {
        subst my. simpl.
        exists ((<[x:=vx]> σm) ∪ σy). split.
        - apply (proj2 (res_extend_by_store_iff _ _ _ _ Hext)).
          exists (<[x:=vx]> σm), σy. repeat split; eauto.
        - reflexivity.
      }
      split.
      {
        replace (store_restrict
          (store_restrict ((<[x:=vx]> σm) ∪ σy) Xy) (fv_tm e))
          with (store_restrict σm (fv_tm e)).
        - exact Hsteps.
        - symmetry. eapply store_restrict_result_forall_base.
          + apply wfworld_store_dom. exact Hσm.
          + rewrite (wfworld_store_dom
              (ext_fun G (store_restrict (<[x:=vx]> σm) (ext_in G))) σy Hσy).
            rewrite (ext_fun_dom G).
            * exact HGout.
            * rewrite HGin, let_result_world_on_dom.
              apply result_projection_dom.
              apply wfworld_store_dom. exact Hσm.
          + exact Hfresh.
          + exact HyX.
          + exact Hxy.
          + exact Hfv.
      }
      apply (store_eq_insert_of_restrict_singleton Xy
        ((<[x:=vx]> σm) ∪ σy)
        (store_restrict ((<[x:=vx]> σm) ∪ σy) Xy) x vx).
      * rewrite dom_union_L.
        rewrite dom_insert_L.
        rewrite (wfworld_store_dom m σm Hσm).
        rewrite (wfworld_store_dom
          (ext_fun G (store_restrict (<[x:=vx]> σm) (ext_in G))) σy Hσy).
        rewrite (ext_fun_dom G).
        -- subst Xy X. set_solver.
        -- rewrite HGin, let_result_world_on_dom.
           apply result_projection_dom.
           apply wfworld_store_dom. exact Hσm.
	      * subst Xy X. set_solver.
	      * reflexivity.
	      * apply store_restrict_singleton_lookup.
	        rewrite (lookup_union_l' (<[x:=vx]> σm) σy x).
	        -- apply lookup_insert_eq.
	        -- eexists. apply lookup_insert_eq.
    + intros Hσn_let.
      destruct (let_result_world_on_elim e x my Hfresh_my Hresult_my
        σn Hσn_let) as [σbase [vx [Hσbase [Hsteps_base ->]]]].
	      subst my. simpl in Hσbase.
	      destruct Hσbase as [σn0 [Hσn0 Hσn0Xy]].
	      pose proof Hσn0 as Hσn0_n.
	      apply (proj1 (res_extend_by_store_iff _ _ _ _ Hext)) in Hσn0.
      destruct Hσn0 as [σx [σy [Hσx [Hσy Hσn0_eq]]]].
      subst m1.
      destruct (let_result_world_on_elim e x m Hfresh Hresult σx Hσx)
        as [σm [vy [Hσm [Hsteps_m ->]]]].
      assert (Hsteps_base_as_m :
        subst_map (store_restrict σm (fv_tm e)) e →* tret vx).
      {
        replace (store_restrict σm (fv_tm e))
          with (store_restrict σbase (fv_tm e)).
        - exact Hsteps_base.
        - rewrite <- Hσn0Xy, Hσn0_eq.
          eapply store_restrict_result_forall_base.
          + apply wfworld_store_dom. exact Hσm.
          + rewrite (wfworld_store_dom
              (ext_fun G (store_restrict (<[x:=vy]> σm) (ext_in G))) σy Hσy).
            rewrite (ext_fun_dom G).
            * exact HGout.
            * rewrite HGin, let_result_world_on_dom.
              apply result_projection_dom.
              apply wfworld_store_dom. exact Hσm.
          + exact Hfresh.
          + exact HyX.
          + exact Hxy.
          + exact Hfv.
      }
      assert (vy = vx) by (eapply steps_result_unique; eauto).
      subst vy.
      rewrite <- (store_eq_insert_of_restrict_singleton Xy σn0 σbase x vx).
	      * exact Hσn0_n.
	      * rewrite (wfworld_store_dom n σn0 Hσn0_n).
        rewrite Hdom_n, HGout.
	        subst Xy X. rewrite let_result_world_on_dom. set_solver.
      * subst Xy X. set_solver.
      * exact Hσn0Xy.
	      * rewrite Hσn0_eq.
	        apply store_restrict_singleton_lookup.
	        rewrite (lookup_union_l' (<[x:=vx]> σm) σy x).
	        -- apply lookup_insert_eq.
	        -- eexists. apply lookup_insert_eq.
Qed.

Lemma FExprResultAt_base_result_witness
    (Σ : gmap atom ty) (T : ty) e ν (m n : WfWorld) :
  Σ ⊢ₑ e ⋮ T →
  world_dom (m : World) = dom Σ →
  world_closed_on (dom Σ) m →
  res_restrict n (dom Σ) = m →
  world_dom (n : World) = dom Σ ∪ {[ν]} →
  n ⊨ FExprResultAt (dom Σ) e ν →
  ∀ σ, (m : World) σ →
    ∃ vx, subst_map (store_restrict σ (fv_tm e)) e →* tret vx.
Proof.
  intros Hty Hdom_m Hclosed Hrestrict Hdom_n Hmodel σ Hσm.
  pose proof (basic_typing_contains_fv_tm Σ e T Hty) as Hfv.
  pose proof (typing_tm_lc Σ e T Hty) as Hlc.
  assert (Hproj : (res_restrict n (dom Σ) : World) σ).
  { rewrite Hrestrict. exact Hσm. }
  destruct Hproj as [σn [Hσn HσnΣ]].
  assert (Hproj' : (res_restrict n (dom Σ) : World) σ).
  { exists σn. split; eauto. }
  pose proof (FExprResultAt_fiber_expr_result_in_world
    (dom Σ) e ν n σ Hproj' Hlc Hdom_n Hmodel) as Hexpr.
  assert (Hfiber :
    (res_fiber_from_projection n (dom Σ) σ Hproj' : World) σn).
  { apply res_fiber_from_projection_member; eauto. }
  assert (Hνproj :
    (res_restrict
      (res_fiber_from_projection n (dom Σ) σ Hproj') {[ν]} : World)
      (store_restrict σn {[ν]})).
  { exists σn. split; eauto. }
  pose proof (expr_result_in_world_sound
    (store_restrict σ (dom Σ)) e ν
    (res_fiber_from_projection n (dom Σ) σ Hproj')
    (store_restrict σn {[ν]}) Hexpr Hνproj) as Hstore.
  destruct (expr_result_store_elim ν
    (subst_map (store_restrict σ (dom Σ)) e)
    (store_restrict σn {[ν]}) Hstore)
    as [vx [_ [_ [_ HstepsX]]]].
  exists vx.
  rewrite (subst_map_restrict_to_fv_from_superset e
    (dom Σ) σ Hfv (proj1 (Hclosed σ Hσm))).
  exact HstepsX.
Qed.

Lemma FExprResultAt_as_extend_by
    (Σ : gmap atom ty) (T : ty) e ν (m n : WfWorld)
    (Hfresh : ν ∉ world_dom (m : World)) :
  Σ ⊢ₑ e ⋮ T →
  world_dom (m : World) = dom Σ →
  world_closed_on (dom Σ) m →
  world_dom (n : World) = dom Σ ∪ {[ν]} →
  res_restrict n (dom Σ) = m →
  n ⊨ FExprResultAt (dom Σ) e ν →
  ∃ F,
    forall_extension_shape (world_dom (m : World)) ν F ∧
    m #> F ~~> n.
Proof.
  intros Hty Hdom_m Hclosed Hdom_n Hrestrict Hmodel.
  pose proof (FExprResultAt_base_result_witness
    Σ T e ν m n Hty Hdom_m Hclosed Hrestrict Hdom_n Hmodel) as Hresult.
  pose proof (FExprResultAt_unique_let_result_world
    Σ T e ν m n Hfresh Hresult Hty Hdom_m Hclosed Hdom_n Hrestrict Hmodel)
    as ->.
  apply forall_world_as_extend_by.
  - exact Hfresh.
  - apply let_result_world_on_dom.
  - apply let_result_world_on_restrict.
Qed.

Lemma FExprResultAt_as_let_result_world
    (Σ : gmap atom ty) (T : ty) e ν (m n : WfWorld)
    (Hfresh : ν ∉ world_dom (m : World)) :
  Σ ⊢ₑ e ⋮ T →
  world_dom (m : World) = dom Σ →
  world_closed_on (dom Σ) m →
  world_dom (n : World) = dom Σ ∪ {[ν]} →
  res_restrict n (dom Σ) = m →
  n ⊨ FExprResultAt (dom Σ) e ν →
  ∃ Hresult,
    n = let_result_world_on e ν m Hfresh Hresult.
Proof.
  intros Hty Hdom_m Hclosed Hdom_n Hrestrict Hmodel.
  pose proof (FExprResultAt_base_result_witness
    Σ T e ν m n Hty Hdom_m Hclosed Hrestrict Hdom_n Hmodel) as Hresult.
  exists Hresult.
  eapply FExprResultAt_unique_let_result_world; eauto.
Qed.

Lemma result_extension_as_let_result_world
    (Σ : gmap atom ty) (T : ty) e ν (m n : WfWorld) F
    (Hfresh : ν ∉ world_dom (m : World)) :
  Σ ⊢ₑ e ⋮ T →
  world_dom (m : World) = dom Σ →
  world_closed_on (dom Σ) m →
  ν ∉ dom Σ →
  forall_extension_shape (world_dom (m : World)) ν F →
  m #> F ~~> n →
  n ⊨ FExprResultAt (dom Σ) e ν →
  ∃ Hresult,
    n = let_result_world_on e ν m Hfresh Hresult.
Proof.
  intros Hty Hdom_m Hclosed HνΣ HFshape Hext Hmodel.
  destruct HFshape as [_ HFout].
  assert (Hdom_n : world_dom (n : World) = dom Σ ∪ {[ν]}).
  {
    rewrite (res_extend_by_dom _ _ _ Hext), Hdom_m, HFout.
    reflexivity.
  }
  assert (Hrestrict : res_restrict n (dom Σ) = m).
  { rewrite <- Hdom_m. eapply res_extend_by_restrict_base. exact Hext. }
  eapply FExprResultAt_as_let_result_world; eauto.
Qed.

Lemma let_result_world_as_result_extension
    (Σ : gmap atom ty) (T : ty) e ν (m : WfWorld)
    (Hfresh : ν ∉ world_dom (m : World)) Hresult :
  Σ ⊢ₑ e ⋮ T →
  world_dom (m : World) = dom Σ →
  world_closed_on (dom Σ) m →
  ν ∉ dom Σ →
  ∃ F,
    forall_extension_shape (world_dom (m : World)) ν F ∧
    m #> F ~~> let_result_world_on e ν m Hfresh Hresult ∧
    let_result_world_on e ν m Hfresh Hresult ⊨ FExprResultAt (dom Σ) e ν.
Proof.
  intros Hty Hdom_m Hclosed HνΣ.
  destruct (forall_world_as_extend_by
    m ν (let_result_world_on e ν m Hfresh Hresult) Hfresh
    ltac:(apply let_result_world_on_dom)
    ltac:(apply let_result_world_on_restrict))
    as [F [HFshape Hext]].
  exists F. split; [exact HFshape |].
  split; [exact Hext |].
  eapply let_result_world_on_models_FExprResultAt.
  - eapply basic_typing_contains_fv_tm. exact Hty.
  - eapply typing_tm_lc. exact Hty.
  - exact HνΣ.
  - rewrite Hdom_m. reflexivity.
  - exact Hclosed.
Qed.

Lemma FExprContIn_iff_result_extension
    (Σ : gmap atom ty) (T : ty) e
    (Q : FormulaQ) (m : WfWorld) :
  Σ ⊢ₑ e ⋮ T →
  world_dom (m : World) = dom Σ →
  world_closed_on (dom Σ) m →
  expr_total_on (dom Σ) e m →
  formula_fv Q ⊆ dom Σ →
  m ⊨ FExprContIn Σ e Q ↔
  ∃ L : aset,
    dom Σ ⊆ L ∧
    ∀ ν F n,
      ν ∉ L →
      forall_extension_shape (world_dom (m : World)) ν F →
      m #> F ~~> n →
      n ⊨ FExprResultAt (dom Σ) e ν →
      n ⊨ formula_open 0 ν Q.
Proof.
  intros Hty Hdom Hclosed Htotal HQfv.
  split.
  - intros Hcont.
    destruct (proj1 (FExprContIn_iff_let_result_world
      Σ T e Q m Hty Hdom Hclosed Htotal HQfv) Hcont)
      as [L [HLdom Hbody]].
    exists (L ∪ dom Σ ∪ fv_tm e ∪ formula_fv Q).
    split; [set_solver |].
    intros ν F n Hν HFshape Hext Hresult_model.
    rewrite !not_elem_of_union in Hν.
    destruct Hν as [[[HνL HνΣ] Hνe] HνQ].
    assert (Hfresh : ν ∉ world_dom (m : World)).
    { rewrite Hdom. exact HνΣ. }
    destruct (result_extension_as_let_result_world
      Σ T e ν m n F Hfresh Hty Hdom Hclosed HνΣ HFshape Hext
      Hresult_model) as [Hresult ->].
    eauto.
  - intros [L [HLdom Hbody]].
    apply (proj2 (FExprContIn_iff_let_result_world
      Σ T e Q m Hty Hdom Hclosed Htotal HQfv)).
    exists (L ∪ dom Σ ∪ fv_tm e).
    split; [set_solver |].
    intros ν Hν Hfresh Hresult.
    rewrite !not_elem_of_union in Hν.
    destruct Hν as [[HνL HνΣ] Hνe].
    destruct (let_result_world_as_result_extension
      Σ T e ν m Hfresh Hresult Hty Hdom Hclosed HνΣ)
      as [F [HFshape [Hext Hmodel]]].
    eapply Hbody; eauto.
Qed.
