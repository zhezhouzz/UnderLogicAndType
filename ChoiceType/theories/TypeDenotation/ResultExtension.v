(** * ChoiceType.TypeDenotation.ResultExtension

    Expression-result world extensions.  This layer is semantic: it talks about
    stores, operational results, and world extensions, but not typing-context
    soundness. *)

From CoreLang Require Import Instantiation InstantiationProps LocallyNamelessProps
  OperationalProps.
From ChoiceAlgebra Require Import Resource.
From ChoiceType Require Import TypeDenotation.Formula.
From Stdlib Require Import Logic.Classical_Prop.

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

Definition result_extension (X : aset) (e : tm) (x : atom) (Hfresh : x ∉ X)
    : fiber_extension :=
  mk_forall_extension X x (expr_result_extension_fiber X e x) Hfresh
    ltac:(intros; simpl; reflexivity)
    ltac:(intros σ _; destruct (world_wf (expr_result_extension_fiber X e x σ))
      as [Hne _]; exact Hne).

Lemma result_extension_proof_irrel X e x
    (H1 H2 : x ∉ X) :
  result_extension X e x H1 = result_extension X e x H2.
Proof.
  unfold result_extension, mk_forall_extension, mk_fiber_extension.
  f_equal. apply proof_irrelevance.
Qed.

Lemma result_extension_shape X (e : tm) x Hfresh :
  forall_extension_shape X x (result_extension X e x Hfresh).
Proof.
  unfold forall_extension_shape, result_extension, mk_forall_extension,
    mk_fiber_extension; simpl; eauto.
Qed.

Lemma result_extension_functional_on X e x Hfresh (m : WfWorld) :
  fv_tm e ⊆ X →
  expr_total_on e m →
  fiber_extension_functional_on m (result_extension X e x Hfresh).
Proof.
  intros HfvX [_ Htotal] σ σe1 σe2 Hmσ Hσe1 Hσe2.
  unfold result_extension,
    mk_forall_extension, mk_fiber_extension in Hσe1, Hσe2.
  simpl in Hσe1, Hσe2.
  destruct Hσe1 as [_ [[vx1 [-> Hsteps1]] | [Hnone1 ->]]].
  - destruct Hσe2 as [_ [[vx2 [-> Hsteps2]] | [Hnone2 ->]]].
    + assert (Hvx : vx1 = vx2).
      {
        eapply steps_result_unique.
        - rewrite store_restrict_twice_subset in Hsteps1 by exact HfvX.
          exact Hsteps1.
        - rewrite store_restrict_twice_subset in Hsteps2 by exact HfvX.
          exact Hsteps2.
      }
      subst. reflexivity.
    + exfalso. apply Hnone2. exists vx1.
      exact Hsteps1.
  - destruct (Htotal σ Hmσ) as [vx Hsteps].
    exfalso. apply Hnone1. exists vx.
    rewrite store_restrict_twice_subset by exact HfvX.
    exact Hsteps.
Qed.

Lemma result_extension_input_widen_to X X' e x
    (Hfresh : x ∉ X) (Hfresh' : x ∉ X') :
  fv_tm e ⊆ X →
  X ⊆ X' →
  result_extension X e x Hfresh ~>i result_extension X' e x Hfresh'.
Proof.
  intros Hfv HX.
  constructor.
  - unfold result_extension,
      mk_forall_extension, mk_fiber_extension; simpl.
    exact HX.
  - unfold result_extension,
      mk_forall_extension, mk_fiber_extension; simpl.
    reflexivity.
  - intros σ Hdomσ.
    unfold result_extension,
      mk_forall_extension, mk_fiber_extension,
      fiber_extension_input_widen_fun; simpl.
    apply wfworld_ext. apply world_ext.
    + reflexivity.
    + intros σx. simpl. split.
      * intros [Hdomx [[vx [-> Hsteps]] | [Hnone ->]]].
        -- split; [exact Hdomx |].
           left. exists vx. split; [reflexivity |].
           rewrite store_restrict_twice_subset by exact Hfv.
           exact Hsteps.
        -- split; [exact Hdomx |].
           right. split; [| reflexivity].
           intros [vx Hsteps]. apply Hnone. exists vx.
           rewrite store_restrict_twice_subset in Hsteps by exact Hfv.
           exact Hsteps.
      * intros [Hdomx [[vx [-> Hsteps]] | [Hnone ->]]].
        -- split; [exact Hdomx |].
           left. exists vx. split; [reflexivity |].
           rewrite store_restrict_twice_subset in Hsteps by exact Hfv.
           exact Hsteps.
        -- split; [exact Hdomx |].
           right. split; [| reflexivity].
           intros [vx Hsteps]. apply Hnone. exists vx.
           rewrite store_restrict_twice_subset by exact Hfv.
           exact Hsteps.
Qed.

Record result_extends
    (e : tm) (x : atom) (m : WfWorld)
    (F : fiber_extension) (mx : WfWorld) : Prop := {
  result_extends_fresh : x ∉ world_dom (m : World);
  result_extends_eq :
    F = result_extension (world_dom (m : World)) e x result_extends_fresh;
  result_extends_by : m #> F ~~> mx;
}.

Lemma result_extends_shape e x m F mx :
  result_extends e x m F mx →
  forall_extension_shape (world_dom (m : World)) x F.
Proof.
  intros Hext.
  destruct Hext as [Hfresh -> _].
  apply result_extension_shape.
Qed.

Lemma result_extends_dom e x m F mx :
  result_extends e x m F mx →
  world_dom (mx : World) = world_dom (m : World) ∪ {[x]}.
Proof.
  intros Hext.
  pose proof (result_extends_shape _ _ _ _ _ Hext) as [_ Hout].
  destruct Hext as [_ _ Hby].
  rewrite (res_extend_by_dom _ _ _ Hby), Hout.
  reflexivity.
Qed.

Lemma res_extend_by_forall_shape_dom
    (D : aset) y (m my : WfWorld) F :
  forall_extension_shape (world_dom (m : World)) y F →
  m #> F ~~> my →
  world_dom (m : World) = D →
  world_dom (my : World) = D ∪ {[y]}.
Proof.
  intros Hshape Hext Hdom.
  pose proof (res_extend_by_dom _ _ _ Hext) as Hmy.
  destruct Hshape as [_ Hout].
  rewrite Hmy, Hout, Hdom.
  reflexivity.
Qed.

Lemma world_dom_forall_extension
    (Δ : gmap atom ty) T y (m my : WfWorld) F :
  y ∉ dom Δ →
  forall_extension_shape (world_dom (m : World)) y F →
  m #> F ~~> my →
  world_dom (m : World) = dom Δ →
  world_dom (my : World) = dom (<[y := T]> Δ).
Proof.
  intros _ Hshape Hext Hdom.
  rewrite (res_extend_by_forall_shape_dom (dom Δ) y m my F Hshape Hext Hdom).
  rewrite dom_insert_L.
  set_solver.
Qed.

Lemma result_extends_widen_after_forall
    (Δ : gmap atom ty) e
    (m mx my ny : WfWorld) Fx Fy x y :
  result_extends e x m Fx mx ->
  fv_tm e ⊆ dom Δ ->
  world_dom (m : World) = dom Δ ->
  y ∉ world_dom (mx : World) ->
  forall_extension_shape (world_dom (m : World)) y Fy ->
  m #> Fy ~~> my ->
  my #> Fx ~~> ny ->
  ∃ Fx', result_extends e x my Fx' ny.
Proof.
  intros Hext Hfv Hdom Hy_mx HFyshape HmFy HmyFx.
  pose proof (result_extends_fresh _ _ _ _ _ Hext) as Hfreshx_m.
  pose proof (result_extends_eq _ _ _ _ _ Hext) as HFx_eq.
  pose proof (result_extends_dom _ _ _ _ _ Hext) as Hdom_mx.
  pose proof (res_extend_by_dom _ _ _ HmFy) as Hdom_my.
  destruct HFyshape as [_ HFy_out].
  rewrite HFy_out in Hdom_my.
  assert (Hfreshx_my : x ∉ world_dom (my : World)).
  {
    rewrite Hdom_my.
    rewrite Hdom_mx in Hy_mx.
    set_solver.
  }
  set (Fx' := result_extension (world_dom (my : World)) e x Hfreshx_my).
  exists Fx'.
  refine {| result_extends_fresh := Hfreshx_my |}.
  - subst Fx'. reflexivity.
  - subst Fx'.
    rewrite HFx_eq in HmyFx.
    assert (Hwid :
      result_extension (world_dom (m : World)) e x
        (result_extends_fresh e x m Fx mx Hext)
        ~>i result_extension (world_dom (my : World)) e x Hfreshx_my).
    {
      eapply result_extension_input_widen_to.
      - rewrite Hdom. exact Hfv.
      - rewrite Hdom_my. set_solver.
    }
    assert (Hin' :
      ext_in (result_extension (world_dom (my : World)) e x Hfreshx_my)
        ⊆ world_dom (my : World)).
    {
      pose proof (result_extension_shape
        (world_dom (my : World)) e x Hfreshx_my) as [Hin _].
      rewrite Hin. set_solver.
    }
    eapply (proj1 ((res_extend_by_input_widen_to_iff my
      (result_extension (world_dom (m : World)) e x
        (result_extends_fresh e x m Fx mx Hext))
      (result_extension (world_dom (my : World)) e x Hfreshx_my)
      ny Hwid) Hin')).
    exact HmyFx.
Qed.

Lemma result_extends_restrict e x m F mx :
  result_extends e x m F mx →
  res_restrict mx (world_dom (m : World)) = m.
Proof.
  intros Hext.
  destruct Hext as [_ _ Hby].
  eapply res_extend_by_restrict_base. exact Hby.
Qed.

Lemma result_extends_rebase_same_dom
    e x (m : WfWorld) F (mx m' mx' : WfWorld) :
  result_extends e x m F mx →
  world_dom (m' : World) = world_dom (m : World) →
  m' #> F ~~> mx' →
  result_extends e x m' F mx'.
Proof.
  intros Hext Hdom Hby'.
  destruct Hext as [Hfresh Heq _].
  destruct Hdom.
  assert (Hfresh' : x ∉ world_dom (m' : World)).
  { exact Hfresh. }
  refine {| result_extends_fresh := Hfresh' |}.
  - rewrite Heq.
    apply result_extension_proof_irrel.
  - exact Hby'.
Qed.

Lemma result_extension_applicable
    e x (m : WfWorld) (Hfresh : x ∉ world_dom (m : World)) :
  extension_applicable
    (result_extension (world_dom (m : World)) e x Hfresh) m.
Proof.
  unfold result_extension,
    mk_forall_extension, mk_fiber_extension.
  constructor; simpl; set_solver.
Qed.

Lemma result_extends_exists
    e x (m : WfWorld) (Hfresh : x ∉ world_dom (m : World)) :
  ∃ mx,
    result_extends e x m
      (result_extension (world_dom (m : World)) e x Hfresh) mx.
Proof.
  destruct (res_extend_by_exists m
    (result_extension (world_dom (m : World)) e x Hfresh))
    as [mx Hby].
  { apply result_extension_applicable. }
  exists mx.
  refine {| result_extends_fresh := Hfresh |}; eauto.
Qed.

Record result_extends_on
    (X : aset) (e : tm) (x : atom) (m : WfWorld)
    (F : fiber_extension) (mx : WfWorld) : Prop := {
  result_extends_on_fresh_input : x ∉ X;
  result_extends_on_input : X ⊆ world_dom (m : World);
  result_extends_on_fresh : x ∉ world_dom (m : World);
  result_extends_on_eq :
    F = result_extension X e x result_extends_on_fresh_input;
  result_extends_on_by : m #> F ~~> mx;
}.

Lemma result_extends_to_on e x (m mx : WfWorld) F :
  result_extends e x m F mx →
  result_extends_on (world_dom (m : World)) e x m F mx.
Proof.
  intros Hext.
  destruct Hext as [Hfresh -> Hby].
  refine {| result_extends_on_fresh_input := Hfresh |};
    simpl; eauto; reflexivity.
Qed.

Lemma result_extends_on_shape X e x m F mx :
  result_extends_on X e x m F mx →
  forall_extension_shape X x F.
Proof.
  intros Hext.
  destruct Hext as [HfreshX _ _ -> _].
  apply result_extension_shape.
Qed.

Lemma result_extends_on_dom X e x m F mx :
  result_extends_on X e x m F mx →
  world_dom (mx : World) = world_dom (m : World) ∪ {[x]}.
Proof.
  intros Hext.
  pose proof (result_extends_on_shape _ _ _ _ _ _ Hext) as [_ Hout].
  destruct Hext as [_ _ _ _ Hby].
  rewrite (res_extend_by_dom _ _ _ Hby), Hout.
  reflexivity.
Qed.

Lemma result_extends_on_restrict X e x m F mx :
  result_extends_on X e x m F mx →
  res_restrict mx (world_dom (m : World)) = m.
Proof.
  intros Hext.
  destruct Hext as [_ _ _ _ Hby].
  eapply res_extend_by_restrict_base. exact Hby.
Qed.

Lemma result_extension_on_applicable
    X e x (m : WfWorld) (HfreshX : x ∉ X) :
  X ⊆ world_dom (m : World) →
  x ∉ world_dom (m : World) →
  extension_applicable (result_extension X e x HfreshX) m.
Proof.
  intros HX Hfreshm.
  unfold result_extension,
    mk_forall_extension, mk_fiber_extension.
  constructor; simpl; set_solver.
Qed.

Lemma result_extends_on_exists
    X e x (m : WfWorld)
    (HfreshX : x ∉ X)
    (HX : X ⊆ world_dom (m : World))
    (Hfreshm : x ∉ world_dom (m : World)) :
  ∃ mx,
    result_extends_on X e x m
      (result_extension X e x HfreshX) mx.
Proof.
  destruct (res_extend_by_exists m (result_extension X e x HfreshX))
    as [mx Hby].
  { eapply result_extension_on_applicable; eauto. }
  exists mx.
  refine {| result_extends_on_fresh_input := HfreshX |};
    simpl; eauto; reflexivity.
Qed.

Lemma result_extends_on_member
    X e x (m mx : WfWorld) F σ vx :
  result_extends_on X e x m F mx →
  fv_tm e ⊆ X →
  (m : World) σ →
  subst_map (store_restrict σ (fv_tm e)) e →* tret vx →
  (mx : World) (<[x := vx]> σ).
Proof.
  intros Hext Hfv Hσ Hsteps.
  destruct Hext as [HfreshX HX Hfresh -> Hby].
  apply (proj2 (res_extend_by_store_iff _ _ _ _ Hby)).
  exists σ, ({[x := vx]} : Store).
  split; [exact Hσ |].
  split.
  - unfold result_extension,
      mk_forall_extension, mk_fiber_extension. simpl.
    split.
    + rewrite dom_singleton_L. reflexivity.
    + left. exists vx. split; [reflexivity |].
      replace (store_restrict (store_restrict σ X) (fv_tm e))
        with (store_restrict σ (fv_tm e)).
      * exact Hsteps.
      * rewrite store_restrict_twice_subset by exact Hfv.
        reflexivity.
  - symmetry.
    change ({[x := vx]} : Store) with (<[x := vx]> (∅ : Store)).
    rewrite store_insert_union_r_fresh.
    + rewrite (map_union_empty σ). reflexivity.
    + pose proof (wfworld_store_dom m σ Hσ). set_solver.
Qed.

Lemma result_extends_on_elim
    X e x (m mx : WfWorld) F σx :
  result_extends_on X e x m F mx →
  fv_tm e ⊆ X →
  (∀ σ, (m : World) σ →
    ∃ vx, subst_map (store_restrict σ (fv_tm e)) e →* tret vx) →
  (mx : World) σx →
  ∃ σ vx,
    (m : World) σ ∧
    subst_map (store_restrict σ (fv_tm e)) e →* tret vx ∧
    σx = <[x := vx]> σ.
Proof.
  intros Hext Hfv Hresult Hσx.
  destruct Hext as [HfreshX HX Hfresh -> Hby].
  apply (proj1 (res_extend_by_store_iff _ _ _ _ Hby)) in Hσx.
  destruct Hσx as [σ [σe [Hσ [Hfiber ->]]]].
  unfold result_extension,
    mk_forall_extension, mk_fiber_extension in Hfiber.
  simpl in Hfiber.
  destruct Hfiber as [_ [[vx [-> Hsteps]] | [Hnone ->]]].
  - exists σ, vx. split; [exact Hσ |].
    split.
    + replace (store_restrict σ (fv_tm e))
        with (store_restrict (store_restrict σ X) (fv_tm e)).
      * exact Hsteps.
      * rewrite store_restrict_twice_subset by exact Hfv.
        reflexivity.
    + change ({[x := vx]} : Store) with (<[x := vx]> (∅ : Store)).
      rewrite store_insert_union_r_fresh.
      * rewrite (map_union_empty σ). reflexivity.
      * pose proof (wfworld_store_dom m σ Hσ). set_solver.
  - exfalso. apply Hnone.
    destruct (Hresult σ Hσ) as [vx Hsteps].
    exists vx.
    replace (store_restrict (store_restrict σ X) (fv_tm e))
      with (store_restrict σ (fv_tm e)).
    + exact Hsteps.
    + rewrite store_restrict_twice_subset by exact Hfv.
      reflexivity.
Qed.

Lemma result_extends_elim
    e x (m mx : WfWorld) F σx :
  result_extends e x m F mx →
  expr_total_on e m →
  (mx : World) σx →
  ∃ σ vx,
    (m : World) σ ∧
    subst_map (store_restrict σ (fv_tm e)) e →* tret vx ∧
    σx = <[x := vx]> σ.
Proof.
  intros Hext [Hfv Hresult].
  eapply result_extends_on_elim.
  - exact (result_extends_to_on _ _ _ _ _ Hext).
  - exact Hfv.
  - exact Hresult.
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

Lemma result_extends_on_forall_extension_commute
    X e x (m mx : WfWorld) Fx
    y Fy my :
  result_extends_on X e x m Fx mx →
  y ∉ world_dom (mx : World) →
  forall_extension_shape (world_dom (m : World)) y Fy →
  m #> Fy ~~> my →
  ∃ n Gy,
    result_extends_on X e x my Fx n ∧
    forall_extension_shape (world_dom (mx : World)) y Gy ∧
    mx #> Gy ~~> n.
Proof.
  intros Hxext Hy_mx HFy_shape HFy.
  destruct Hxext as [HfreshX HX Hfreshx -> HFx].
  pose proof (res_extend_by_dom _ _ _ HFx) as Hdom_mx.
  pose proof (res_extend_by_dom _ _ _ HFy) as Hdom_my.
  destruct HFy_shape as [HFy_in HFy_out].
  assert (Hfreshx_my : x ∉ world_dom (my : World)).
  {
    rewrite Hdom_my, HFy_out.
    rewrite Hdom_mx in Hy_mx.
    set_solver.
  }
  assert (HX_my : X ⊆ world_dom (my : World)).
  {
    rewrite Hdom_my.
    set_solver.
  }
  destruct (result_extends_on_exists X e x my HfreshX HX_my Hfreshx_my)
    as [n Hx_my].
  destruct Hx_my as [_ _ _ _ HmyFx].
  assert (HFy_app_mx : extension_applicable Fy mx).
  {
    constructor.
    - rewrite HFy_in, Hdom_mx. set_solver.
    - rewrite HFy_out. set_solver.
  }
  destruct (res_extend_by_exists mx Fy HFy_app_mx) as [n' HmxFy].
  assert (Heq : n' = n).
  {
    eapply (res_extend_by_commute m
      (result_extension X e x HfreshX) Fy mx my n' n); eauto.
  }
  subst n'.
  assert (Hdom_n : world_dom (n : World) =
      world_dom (mx : World) ∪ {[y]}).
  {
    rewrite (res_extend_by_dom _ _ _ HmxFy), HFy_out.
    reflexivity.
  }
  assert (Hrestrict_n : res_restrict n (world_dom (mx : World)) = mx).
  { eapply res_extend_by_restrict_base. exact HmxFy. }
  destruct (forall_world_as_extend_by mx y n Hy_mx Hdom_n Hrestrict_n)
    as [Gy [HGy_shape HGy]].
  exists n, Gy. split.
  - refine {| result_extends_on_fresh_input := HfreshX |}; eauto;
      reflexivity.
  - split; eauto.
Qed.

Lemma result_extends_on_fiber_projection_elim
    X e x (m mx : WfWorld) F σXx Hproj σx :
  result_extends_on X e x m F mx →
  fv_tm e ⊆ X →
  expr_total_on e m →
  (res_fiber_from_projection mx (X ∪ {[x]}) σXx Hproj : World) σx →
  ∃ σ vx,
    (m : World) σ ∧
    subst_map (store_restrict σ (fv_tm e)) e →* tret vx ∧
    σx = <[x := vx]> σ ∧
    store_restrict σ X = store_restrict σXx X.
Proof.
  intros Hext Hfv Htotal Hfiber.
  destruct Hfiber as [Hσx Hσx_proj].
  pose proof (wfworld_store_dom (res_restrict mx (X ∪ {[x]}))
    σXx Hproj) as HdomσXx.
  simpl in HdomσXx.
  assert (HdomσXx_exact : dom σXx = X ∪ {[x]}).
  {
    rewrite HdomσXx.
    rewrite (result_extends_on_dom _ _ _ _ _ _ Hext).
    pose proof (result_extends_on_input _ _ _ _ _ _ Hext).
    set_solver.
  }
  destruct (result_extends_on_elim X e x m mx F σx
    Hext Hfv (proj2 Htotal) Hσx)
    as [σ [vx [Hσ [Hsteps Heq]]]].
  subst σx.
  exists σ, vx. repeat split; eauto.
  rewrite <- Hσx_proj.
  rewrite HdomσXx_exact.
  rewrite store_restrict_restrict.
  replace ((X ∪ {[x]}) ∩ X) with X by set_solver.
  rewrite store_restrict_insert_notin.
  - reflexivity.
  - exact (result_extends_on_fresh_input _ _ _ _ _ _ Hext).
Qed.

Lemma result_extends_on_fiber_projection_member
    X e x (m mx : WfWorld) F σ vx :
  result_extends_on X e x m F mx →
  fv_tm e ⊆ X →
  (m : World) σ →
  subst_map (store_restrict σ (fv_tm e)) e →* tret vx →
  let σXx := store_restrict (<[x := vx]> σ) (X ∪ {[x]}) in
  ∃ Hproj,
    (res_fiber_from_projection mx (X ∪ {[x]}) σXx Hproj : World)
      (<[x := vx]> σ).
Proof.
  intros Hext Hfv Hσ Hsteps σXx.
  assert (Hσx : (mx : World) (<[x := vx]> σ)).
  { eapply result_extends_on_member; eauto. }
  assert (Hproj :
    (res_restrict mx (X ∪ {[x]}) : World) σXx).
  { exists (<[x := vx]> σ). split; [exact Hσx | reflexivity]. }
  exists Hproj.
  apply res_fiber_from_projection_member; [exact Hσx | reflexivity].
Qed.
