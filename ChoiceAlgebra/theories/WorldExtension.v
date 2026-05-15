(** * ChoiceAlgebra.WorldExtension

    Fiber-wise world extensions.

    This file is purely algebraic: it turns implicit Kripke/domain extensions
    into explicit fiber algorithms.  Formula-specific transport lemmas live in
    [ChoiceLogic.FormulaWorldExtension]. *)

From ChoicePrelude Require Import Store.
From ChoiceAlgebra Require Import Resource.
From Stdlib Require Import Logic.Classical_Prop.

Section WorldExtension.

Context {V : Type} `{ValueSig V}.

Local Notation StoreT := (gmap atom V) (only parsing).
Local Notation WorldT := (World (V := V)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).

(** A fiber extension [(X, Y, f)] is an algorithm that looks only at a store's
    [X]-projection and returns a nonempty resource over [Y]. *)
Record fiber_extension := {
  ext_in : aset;
  ext_out : aset;
  ext_disjoint : ext_in ## ext_out;
  ext_fun : StoreT -> WfWorldT;

  ext_fun_dom :
    forall σ,
      dom σ = ext_in ->
      world_dom (ext_fun σ : WorldT) = ext_out;

  ext_fun_nonempty :
    forall σ,
      dom σ = ext_in ->
      exists σe, (ext_fun σ : WorldT) σe;
}.

Definition mk_fiber_extension
    (X Y : aset) (f : StoreT -> WfWorldT)
    (Hdisj : X ## Y)
    (Hdom : forall σ, dom σ = X -> world_dom (f σ : WorldT) = Y)
    (Hne : forall σ, dom σ = X -> exists σe, (f σ : WorldT) σe)
    : fiber_extension :=
  {| ext_in := X; ext_out := Y; ext_fun := f;
     ext_disjoint := Hdisj;
     ext_fun_dom := Hdom; ext_fun_nonempty := Hne |}.

Definition mk_forall_extension
    (X : aset) (y : atom) (f : StoreT -> WfWorldT)
    (Hfresh : y ∉ X)
    (Hdom : forall σ, dom σ = X -> world_dom (f σ : WorldT) = {[y]})
    (Hne : forall σ, dom σ = X -> exists σy, (f σ : WorldT) σy)
    : fiber_extension :=
  mk_fiber_extension X {[y]} f ltac:(set_solver) Hdom Hne.

Definition forall_extension_shape (X : aset) (y : atom) (F : fiber_extension) : Prop :=
  ext_in F = X /\ ext_out F = {[y]}.

Definition singleton_extension_store (y : atom) : StoreT :=
  <[y := inhabitant]> (∅ : StoreT).

Lemma singleton_extension_store_dom y :
  dom (singleton_extension_store y) = {[y]}.
Proof.
  unfold singleton_extension_store.
  rewrite dom_insert_L, dom_empty_L. set_solver.
Qed.

Local Lemma store_with_dom_exists (X : aset) :
  exists σ : StoreT, dom σ = X.
Proof.
  induction X as [|x X Hx IH] using set_ind_L.
  - exists (∅ : StoreT). rewrite dom_empty_L. reflexivity.
  - destruct IH as [σ Hdomσ].
    exists (<[x := inhabitant]> σ).
    rewrite dom_insert_L, Hdomσ. reflexivity.
Qed.

Definition default_world (X : aset) : WfWorldT.
Proof.
  refine (exist _ {|
    world_dom := X;
    world_stores := fun σ => dom σ = X
  |} _).
  constructor.
  - apply store_with_dom_exists.
  - eauto.
Defined.

Lemma default_world_dom X :
  world_dom (default_world X : WorldT) = X.
Proof. reflexivity. Qed.

Definition forall_extension_fiber
    (m mx : WfWorldT) (X : aset) (y : atom)
    (Hfresh : y ∉ X)
    (Hdom_mx : world_dom (mx : WorldT) = X ∪ {[y]})
    (Hrestrict : res_restrict mx X = m)
    (σ : StoreT) : WfWorldT.
Proof.
  refine (exist _ {|
    world_dom := {[y]};
    world_stores := fun σy =>
      dom σy = {[y]} /\
      ((dom σ = X /\ (m : WorldT) σ /\ (mx : WorldT) (σ ∪ σy)) \/
       (((dom σ <> X) \/ ~ (m : WorldT) σ) /\
        σy = singleton_extension_store y))
  |} _).
  constructor.
  - destruct (classic (dom σ = X /\ (m : WorldT) σ))
      as [[Hdomσ Hmσ] | Hnot].
    + assert (Hproj : (res_restrict mx X : WorldT) σ).
      {
        change ((res_restrict mx X : WfWorldT) σ).
        rewrite Hrestrict. exact Hmσ.
      }
      destruct Hproj as [σmx [Hmx HσmxX]].
      exists (store_restrict σmx {[y]}). split.
      * pose proof (wfworld_store_dom mx σmx Hmx) as Hdomσmx.
        change (dom (store_restrict σmx ({[y]} : aset)) = ({[y]} : aset)).
        replace (dom (store_restrict σmx ({[y]} : aset)))
          with (dom σmx ∩ ({[y]} : aset)) by (symmetry; apply store_restrict_dom).
        rewrite Hdomσmx, Hdom_mx. set_solver.
      * left. repeat split; eauto.
        replace (σ ∪ store_restrict σmx {[y]}) with σmx.
        -- exact Hmx.
        -- rewrite <- HσmxX.
           symmetry. apply store_restrict_union_partition.
           ++ pose proof (wfworld_store_dom mx σmx Hmx) as Hdomσmx.
              set_solver.
           ++ set_solver.
    + exists (singleton_extension_store y). split.
      * apply singleton_extension_store_dom.
      * right. split; [| reflexivity].
        destruct (classic (dom σ = X)) as [Hdomσ | Hdomσ].
        -- right. intros Hmσ. apply Hnot. split; eauto.
        -- left. exact Hdomσ.
  - intros σy [Hdomσy _]. exact Hdomσy.
Defined.

Definition forall_world_extension
    (m mx : WfWorldT) (y : atom)
    (Hfresh : y ∉ world_dom (m : WorldT))
    (Hdom_mx : world_dom (mx : WorldT) = world_dom (m : WorldT) ∪ {[y]})
    (Hrestrict : res_restrict mx (world_dom (m : WorldT)) = m)
    : fiber_extension :=
  mk_forall_extension (world_dom (m : WorldT)) y
    (forall_extension_fiber m mx (world_dom (m : WorldT)) y
      Hfresh Hdom_mx Hrestrict)
    Hfresh
    ltac:(intros; simpl; reflexivity)
    ltac:(intros σ _; destruct (world_wf
      (forall_extension_fiber m mx (world_dom (m : WorldT)) y
        Hfresh Hdom_mx Hrestrict σ)) as [Hne _]; exact Hne).

(** Applicability is intentionally hidden behind [m #> F ~~> n].  Callers should
    usually use the projection lemmas below rather than unfold it. *)
Record extension_applicable (F : fiber_extension) (m : WfWorldT) : Prop := {
  ext_app_in : ext_in F ⊆ world_dom (m : WorldT);
  ext_app_out : ext_out F ## world_dom (m : WorldT);
}.

(** [m #> F ~~> n] says that [n] is obtained by extending every store [σ] of [m]
    with one store from the fiber [F] computed from [σ]'s [ext_in]-projection. *)
Definition res_extend_by (m : WfWorldT) (F : fiber_extension) (n : WfWorldT) : Prop :=
  extension_applicable F m /\
  world_dom (n : WorldT) = world_dom (m : WorldT) ∪ ext_out F /\
  forall σ,
    (n : WorldT) σ <->
      exists σm σe,
        (m : WorldT) σm /\
        (ext_fun F (store_restrict σm (ext_in F)) : WorldT) σe /\
        σ = σm ∪ σe.

(** Use an arrow, not [=]: this is a proof-relevant extension relation, not
    Rocq equality.  Keeping [=] in the notation makes goals read as if they
    could be solved by rewriting, and risks confusing nearby equality
    notations/tactics even though the parser can disambiguate after [#>]. *)
Local Notation "m '#>' F '~~>' n" := (res_extend_by m F n)
  (at level 70, F at next level, n at next level).

Lemma res_extend_by_applicable m F n :
  m #> F ~~> n ->
  extension_applicable F m.
Proof.
  intros [Happ _]. eauto.
Qed.

Lemma res_extend_by_input_subset m F n :
  m #> F ~~> n ->
  ext_in F ⊆ world_dom (m : WorldT).
Proof.
  intros Hext.
  apply (ext_app_in _ _ (res_extend_by_applicable _ _ _ Hext)).
Qed.

Lemma res_extend_by_output_fresh m F n :
  m #> F ~~> n ->
  ext_out F ## world_dom (m : WorldT).
Proof.
  intros Hext.
  apply (ext_app_out _ _ (res_extend_by_applicable _ _ _ Hext)).
Qed.

Lemma res_extend_by_dom m F n :
  m #> F ~~> n ->
  world_dom (n : WorldT) = world_dom (m : WorldT) ∪ ext_out F.
Proof.
  intros [_ [Hdom _]]. eauto.
Qed.

Lemma res_extend_by_store_iff m F n σ :
  m #> F ~~> n ->
  (n : WorldT) σ <->
    exists σm σe,
      (m : WorldT) σm /\
      (ext_fun F (store_restrict σm (ext_in F)) : WorldT) σe /\
      σ = σm ∪ σe.
Proof.
  intros [_ [_ Hstores]]. eauto.
Qed.

Lemma res_extend_by_unique m F n1 n2 :
  m #> F ~~> n1 ->
  m #> F ~~> n2 ->
  n1 = n2.
Proof.
  intros H1 H2.
  apply wfworld_ext. apply world_ext.
  - rewrite (res_extend_by_dom _ _ _ H1).
    rewrite (res_extend_by_dom _ _ _ H2).
    reflexivity.
  - intros σ.
    rewrite (res_extend_by_store_iff _ _ _ σ H1).
    rewrite (res_extend_by_store_iff _ _ _ σ H2).
    reflexivity.
Qed.

Local Lemma ext_projection_dom m F σm :
  extension_applicable F m ->
  (m : WorldT) σm ->
  dom (store_restrict σm (ext_in F)) = ext_in F.
Proof.
  intros Happ Hσm.
  transitivity (world_dom (m : WorldT) ∩ ext_in F).
  - rewrite <- (wfworld_store_dom m σm Hσm).
    apply store_restrict_dom.
  - pose proof (ext_app_in _ _ Happ).
    set_solver.
Qed.

Local Lemma res_extend_store_compat m F σm σe :
  extension_applicable F m ->
  (m : WorldT) σm ->
  (ext_fun F (store_restrict σm (ext_in F)) : WorldT) σe ->
  store_compat σm σe.
Proof.
  intros Happ Hσm Hσe.
  apply disj_dom_store_compat.
  change (dom σm ∩ dom σe = ∅).
  pose proof (wfworld_store_dom m σm Hσm) as Hdomσm.
  assert (Hproj_dom : dom (store_restrict σm (ext_in F)) = ext_in F)
    by (eapply ext_projection_dom; eauto).
  assert (Hdomσe : dom σe = ext_out F).
  {
    rewrite (wfworld_store_dom
      (ext_fun F (store_restrict σm (ext_in F))) σe Hσe).
    apply ext_fun_dom. exact Hproj_dom.
  }
  rewrite Hdomσm, Hdomσe.
  pose proof (ext_app_out _ _ Happ).
  set_solver.
Qed.

Lemma res_extend_by_restrict_base m F n :
  m #> F ~~> n ->
  res_restrict n (world_dom (m : WorldT)) = m.
Proof.
  intros Hext.
  destruct Hext as [Happ [Hdom_n Hstores]].
  apply wfworld_ext. apply world_ext.
  - simpl. rewrite Hdom_n.
    pose proof (ext_app_out _ _ Happ).
    set_solver.
  - intros σ. split.
    + intros [σn [Hσn Hrestrict]].
      rewrite Hstores in Hσn.
      destruct Hσn as [σm [σe [Hσm [Hσe ->]]]].
      pose proof (res_extend_store_compat m F σm σe Happ Hσm Hσe) as Hcompat.
      pose proof (wfworld_store_dom m σm Hσm) as Hdomσm.
      assert (Hproj_dom : dom (store_restrict σm (ext_in F)) = ext_in F)
        by (eapply ext_projection_dom; eauto).
      assert (Hdomσe : dom σe = ext_out F).
      {
        rewrite (wfworld_store_dom
          (ext_fun F (store_restrict σm (ext_in F))) σe Hσe).
        apply ext_fun_dom. exact Hproj_dom.
      }
      assert (Hpiece :
        store_restrict (σm ∪ σe) (world_dom (m : WorldT)) = σm).
      {
        apply (store_restrict_union_piece_l σm σe
          (world_dom (m : WorldT)) (ext_out F)).
        - exact Hcompat.
        - change (dom σm ⊆ world_dom (m : WorldT)).
          rewrite Hdomσm. reflexivity.
        - change (dom σe ⊆ ext_out F).
          rewrite Hdomσe. reflexivity.
        - pose proof (ext_app_out _ _ Happ). set_solver.
      }
      rewrite Hpiece in Hrestrict. subst. exact Hσm.
    + intros Hσ.
      pose proof (wfworld_store_dom m σ Hσ) as Hdomσ.
      assert (Hproj_dom : dom (store_restrict σ (ext_in F)) = ext_in F)
        by (eapply ext_projection_dom; eauto).
      destruct (ext_fun_nonempty F (store_restrict σ (ext_in F)) Hproj_dom)
        as [σe Hσe].
      exists (σ ∪ σe). split.
      * rewrite Hstores.
        exists σ, σe. split; [exact Hσ |].
        split; [exact Hσe | reflexivity].
      * pose proof (res_extend_store_compat m F σ σe Happ Hσ Hσe) as Hcompat.
        assert (Hdomσe : dom σe = ext_out F).
        {
          rewrite (wfworld_store_dom
            (ext_fun F (store_restrict σ (ext_in F))) σe Hσe).
          apply ext_fun_dom. exact Hproj_dom.
        }
        apply (store_restrict_union_piece_l σ σe
          (world_dom (m : WorldT)) (ext_out F)).
        -- exact Hcompat.
        -- change (dom σ ⊆ world_dom (m : WorldT)).
          rewrite Hdomσ. reflexivity.
        -- change (dom σe ⊆ ext_out F).
          rewrite Hdomσe. reflexivity.
        -- pose proof (ext_app_out _ _ Happ). set_solver.
Qed.

Lemma res_extend_by_le_base m F n :
  m #> F ~~> n ->
  m ⊑ n.
Proof.
  intros Hext.
  pose proof (res_extend_by_restrict_base m F n Hext) as Hrestrict.
  unfold sqsubseteq, wf_world_sqsubseteq, raw_le.
  change ((m : WorldT) = (res_restrict n (world_dom (m : WorldT)) : WorldT)).
  rewrite Hrestrict. reflexivity.
Qed.

Lemma forall_world_as_extend_by (m : WfWorldT) (y : atom) (my : WfWorldT) :
  y ∉ world_dom (m : WorldT) ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  ∃ F,
    forall_extension_shape (world_dom (m : WorldT)) y F /\
    m #> F ~~> my.
Proof.
  intros Hy Hdom_my Hrestrict.
  pose (F := forall_world_extension m my y Hy Hdom_my Hrestrict).
  exists F. split.
  - subst F. unfold forall_extension_shape, forall_world_extension,
      mk_forall_extension, mk_fiber_extension. simpl. eauto.
  - subst F. unfold res_extend_by, forall_world_extension,
      mk_forall_extension, mk_fiber_extension. simpl.
    split.
    {
      constructor; simpl; set_solver.
    }
    split; [exact Hdom_my |].
    intros σ. split.
    + intros Hmyσ.
      set (σm := store_restrict σ (world_dom (m : WorldT))).
      set (σy := store_restrict σ ({[y]} : aset)).
      exists σm, σy. split.
      {
        subst σm.
        rewrite <- Hrestrict.
        simpl. exists σ. split; [exact Hmyσ |].
        rewrite Hdom_my.
        replace ((world_dom (m : WorldT) ∪ {[y]}) ∩ world_dom (m : WorldT))
          with (world_dom (m : WorldT)) by set_solver.
        reflexivity.
      }
      split.
      {
        subst σm σy.
        simpl. split.
        - change (dom (store_restrict σ ({[y]} : aset)) = ({[y]} : aset)).
          replace (dom (store_restrict σ ({[y]} : aset)))
            with (dom σ ∩ ({[y]} : aset)) by (symmetry; apply store_restrict_dom).
          rewrite (wfworld_store_dom my σ Hmyσ), Hdom_my. set_solver.
        - left. repeat split.
          + rewrite store_restrict_twice_same.
            change (dom (store_restrict σ (world_dom (m : WorldT))) =
              world_dom (m : WorldT)).
            rewrite store_restrict_dom.
            pose proof (wfworld_store_dom my σ Hmyσ) as Hdomσ.
            set_solver.
          + change ((m : WorldT)
              (store_restrict
                (store_restrict σ (world_dom (m : WorldT)))
                (world_dom (m : WorldT)))).
            rewrite store_restrict_twice_same.
            rewrite <- Hrestrict.
            simpl. exists σ. split; [exact Hmyσ |].
            rewrite Hdom_my.
            replace ((world_dom (m : WorldT) ∪ {[y]}) ∩ world_dom (m : WorldT))
              with (world_dom (m : WorldT)) by set_solver.
            reflexivity.
          + rewrite store_restrict_twice_same.
            replace (store_restrict σ (world_dom (m : WorldT)) ∪
              store_restrict σ ({[y]} : aset)) with σ.
            * exact Hmyσ.
            * symmetry. apply store_restrict_union_partition.
              -- pose proof (wfworld_store_dom my σ Hmyσ) as Hdomσ.
                 set_solver.
              -- set_solver.
      }
      {
        subst σm σy.
        symmetry. apply store_restrict_union_partition.
        - pose proof (wfworld_store_dom my σ Hmyσ) as Hdomσ.
          set_solver.
        - set_solver.
      }
    + intros [σm [σy [Hmσm [HF ->]]]].
      simpl in HF.
      destruct HF as [Hdomσy [[Hdom_input [Hm_input Hmy]] | Hbad]].
      * rewrite store_restrict_idemp_eq in Hmy.
        -- exact Hmy.
        -- exact (wfworld_store_dom m σm Hmσm).
      * destruct Hbad as [[Hdom_bad | Hm_bad] _].
        -- exfalso. apply Hdom_bad.
           rewrite store_restrict_idemp_eq.
           ++ exact (wfworld_store_dom m σm Hmσm).
           ++ exact (wfworld_store_dom m σm Hmσm).
        -- exfalso. apply Hm_bad.
           rewrite store_restrict_idemp_eq.
           ++ exact Hmσm.
           ++ exact (wfworld_store_dom m σm Hmσm).
Qed.

Lemma res_extend_by_dom_subset m F n :
  m #> F ~~> n ->
  world_dom (m : WorldT) ⊆ world_dom (n : WorldT).
Proof.
  intros Hext.
  pose proof (res_extend_by_dom _ _ _ Hext).
  set_solver.
Qed.

(** ** Canonical extensions for Kripke growth *)

Definition canonical_extension_fiber
    (m n : WfWorldT) (σ : StoreT) : WfWorldT.
Proof.
  set (X := world_dom (m : WorldT)).
  set (Y := world_dom (n : WorldT) ∖ world_dom (m : WorldT)).
  refine (exist _ {|
    world_dom := Y;
    world_stores := fun σe =>
      dom σe = Y /\
      ((exists σn,
          (n : WorldT) σn /\
          store_restrict σn X = σ /\
          σe = store_restrict σn Y) \/
       ~(exists σn,
          (n : WorldT) σn /\
          store_restrict σn X = σ))
  |} _).
  constructor.
  - destruct (classic (exists σn,
      (n : WorldT) σn /\ store_restrict σn X = σ))
      as [[σn [Hnσn HσnX]] | Hnone].
    + exists (store_restrict σn Y). split.
      * subst Y X.
        change (dom (store_restrict σn
          (world_dom (n : WorldT) ∖ world_dom (m : WorldT))) =
          world_dom (n : WorldT) ∖ world_dom (m : WorldT)).
        replace (dom (store_restrict σn
          (world_dom (n : WorldT) ∖ world_dom (m : WorldT))))
          with (dom σn ∩ (world_dom (n : WorldT) ∖ world_dom (m : WorldT)))
          by (symmetry; apply store_restrict_dom).
        pose proof (wfworld_store_dom n σn Hnσn) as Hdomσn.
        set_solver.
      * left. exists σn. repeat split; eauto.
    + destruct (store_with_dom_exists Y) as [σe Hdomσe].
      exists σe. split; [exact Hdomσe |].
      right. exact Hnone.
  - intros σe [Hdomσe _]. exact Hdomσe.
Defined.

Definition canonical_le_extension (m n : WfWorldT) : fiber_extension :=
  mk_fiber_extension
    (world_dom (m : WorldT))
    (world_dom (n : WorldT) ∖ world_dom (m : WorldT))
    (canonical_extension_fiber m n)
    ltac:(set_solver)
    ltac:(intros; simpl; reflexivity)
    ltac:(intros σ _; destruct (world_wf (canonical_extension_fiber m n σ))
      as [Hne _]; exact Hne).

Definition canonical_le_extension_spec
    (m n : WfWorldT) (F : fiber_extension) : Prop :=
  ext_in F = world_dom (m : WorldT) /\
  ext_out F = world_dom (n : WorldT) ∖ world_dom (m : WorldT) /\
  (forall σ, ext_fun F σ = ext_fun (canonical_le_extension m n) σ) /\
  m #> F ~~> n.

Definition fiber_extension_equiv_on
    (m : WfWorldT) (F G : fiber_extension) : Prop :=
  ext_in F = ext_in G /\
  forall σ σe,
    (m : WorldT) σ ->
    ((ext_fun F (store_restrict σ (ext_in F)) : WorldT) σe <->
     (ext_fun G (store_restrict σ (ext_in G)) : WorldT) σe).

Lemma canonical_le_extension_sound m n :
  m ⊑ n ->
  m #> canonical_le_extension m n ~~> n.
Proof.
  intros Hle.
  assert (Hdom_mn : world_dom (m : WorldT) ⊆ world_dom (n : WorldT)).
  {
    unfold sqsubseteq, wf_world_sqsubseteq in Hle.
    exact (raw_le_dom (m : WorldT) (n : WorldT) Hle).
  }
  unfold res_extend_by, canonical_le_extension, mk_fiber_extension. simpl.
  split.
  {
    constructor; simpl.
    - reflexivity.
    - set_solver.
  }
  split.
  {
    apply set_eq. intros z. split.
    - intros Hz. destruct (decide (z ∈ world_dom (m : WorldT))) as [Hzm | Hzm].
      + apply elem_of_union_l. exact Hzm.
      + apply elem_of_union_r. apply elem_of_difference. split; exact Hz || exact Hzm.
    - intros Hz. apply elem_of_union in Hz as [Hz | Hz].
      + exact (Hdom_mn z Hz).
      + apply elem_of_difference in Hz as [Hz _]. exact Hz.
  }
  intros σ. split.
  - intros Hnσ.
    set (σm := store_restrict σ (world_dom (m : WorldT))).
    set (σe := store_restrict σ
      (world_dom (n : WorldT) ∖ world_dom (m : WorldT))).
    exists σm, σe. split.
    {
      subst σm.
      unfold sqsubseteq, wf_world_sqsubseteq, raw_le in Hle.
      rewrite Hle. simpl. exists σ. split; [exact Hnσ |].
      replace (world_dom (n : WorldT) ∩ world_dom (m : WorldT))
        with (world_dom (m : WorldT)) by set_solver.
      reflexivity.
    }
    split.
    {
      subst σm σe. simpl. split.
      - rewrite store_restrict_dom.
        pose proof (wfworld_store_dom n σ Hnσ) as Hdomσ.
        set_solver.
      - left. exists σ. repeat split; eauto.
        rewrite store_restrict_twice_same. reflexivity.
    }
    {
      subst σm σe.
      symmetry.
      eapply (store_restrict_union_partition σ
        (world_dom (m : WorldT))
        (world_dom (n : WorldT) ∖ world_dom (m : WorldT))).
      - pose proof (wfworld_store_dom n σ Hnσ) as Hdomσ.
        intros z Hz.
        assert (Hzn : z ∈ world_dom (n : WorldT)).
        { rewrite <- Hdomσ. exact Hz. }
        destruct (decide (z ∈ world_dom (m : WorldT))) as [Hzm | Hzm].
        + apply elem_of_union_l. exact Hzm.
        + apply elem_of_union_r. apply elem_of_difference. split; exact Hzn || exact Hzm.
      - set_solver.
    }
  - intros [σm [σe [Hmσm [Hfiber ->]]]].
    simpl in Hfiber.
    destruct Hfiber as [Hdomσe [[σn [Hnσn [HσnX Hσe]]] | Hnone]].
    + subst σe.
      assert (Hdomσn : dom σn = world_dom (n : WorldT))
        by exact (wfworld_store_dom n σn Hnσn).
      assert (Hσm_eq : σm = store_restrict σn (world_dom (m : WorldT))).
      {
        pose proof (wfworld_store_dom m σm Hmσm) as Hdomσm.
        rewrite HσnX.
        symmetry. apply store_restrict_idemp_eq. exact Hdomσm.
      }
      subst σm.
      replace (store_restrict σn (world_dom (m : WorldT)) ∪
        store_restrict σn (world_dom (n : WorldT) ∖ world_dom (m : WorldT)))
        with σn.
	      * exact Hnσn.
	      * symmetry. apply store_restrict_union_partition.
	        -- intros z Hz.
	           assert (Hzn : z ∈ world_dom (n : WorldT)).
	           { rewrite <- Hdomσn. exact Hz. }
	           destruct (decide (z ∈ world_dom (m : WorldT))) as [Hzm | Hzm].
	           ++ apply elem_of_union_l. exact Hzm.
	           ++ apply elem_of_union_r. apply elem_of_difference. split; exact Hzn || exact Hzm.
	        -- set_solver.
    + exfalso. apply Hnone.
      pose proof (wfworld_store_dom m σm Hmσm) as Hdomσm.
      unfold sqsubseteq, wf_world_sqsubseteq, raw_le in Hle.
      rewrite Hle in Hmσm. simpl in Hmσm.
      destruct Hmσm as [σn [Hnσn HσnX]].
      exists σn. split; [exact Hnσn |].
      rewrite HσnX.
      rewrite store_restrict_idemp_eq; [reflexivity | exact Hdomσm].
Qed.

Lemma res_le_as_extend_by m n :
  m ⊑ n ->
  exists F, m #> F ~~> n.
Proof.
  intros Hle.
  exists (canonical_le_extension m n).
  eauto using canonical_le_extension_sound.
Qed.

Lemma canonical_le_extension_spec_self m n :
  m ⊑ n ->
  canonical_le_extension_spec m n (canonical_le_extension m n).
Proof.
  intros Hle. unfold canonical_le_extension_spec.
  split; [reflexivity |].
  split; [reflexivity |].
  split; [intros σ; reflexivity |].
  apply canonical_le_extension_sound. exact Hle.
Qed.

Lemma res_extend_by_output_unique m F G n :
  m #> F ~~> n ->
  m #> G ~~> n ->
  ext_out F = ext_out G.
Proof.
  intros HF HG.
  pose proof (res_extend_by_dom _ _ _ HF) as HFdom.
  pose proof (res_extend_by_dom _ _ _ HG) as HGdom.
  pose proof (res_extend_by_output_fresh _ _ _ HF) as HFfresh.
  pose proof (res_extend_by_output_fresh _ _ _ HG) as HGfresh.
  set_solver.
Qed.

Lemma res_extend_by_fiber_equiv_on m F G n :
  ext_in F = ext_in G ->
  m #> F ~~> n ->
  m #> G ~~> n ->
  fiber_extension_equiv_on m F G.
Proof.
  intros Hin HF HG. split; [exact Hin |].
  assert (Hdir :
    forall A B,
      ext_in A = ext_in B ->
      m #> A ~~> n ->
      m #> B ~~> n ->
      forall σ σe,
        (m : WorldT) σ ->
        (ext_fun A (store_restrict σ (ext_in A)) : WorldT) σe ->
        (ext_fun B (store_restrict σ (ext_in B)) : WorldT) σe).
  {
    intros A B HAB HA HB σ σe Hσ HAe.
    pose proof (res_extend_by_applicable _ _ _ HA) as HAppA.
    pose proof (res_extend_by_applicable _ _ _ HB) as HAppB.
    pose proof (res_extend_store_compat m A σ σe HAppA Hσ HAe)
      as HcompatA.
    assert (Hn : (n : WorldT) (σ ∪ σe)).
    {
      apply (proj2 (res_extend_by_store_iff m A n (σ ∪ σe) HA)).
      exists σ, σe. repeat split; eauto.
    }
    apply (proj1 (res_extend_by_store_iff m B n (σ ∪ σe) HB)) in Hn.
    destruct Hn as [σB [σBe [HσB [HBe Heq]]]].
    pose proof (res_extend_store_compat m B σB σBe HAppB HσB HBe)
      as HcompatB.
    assert (Hdomσ : dom σ = world_dom (m : WorldT))
      by exact (wfworld_store_dom m σ Hσ).
    assert (HdomσB : dom σB = world_dom (m : WorldT))
      by exact (wfworld_store_dom m σB HσB).
    assert (HprojA : dom (store_restrict σ (ext_in A)) = ext_in A)
      by (eapply ext_projection_dom; eauto).
    assert (HprojB : dom (store_restrict σB (ext_in B)) = ext_in B)
      by (eapply ext_projection_dom; eauto).
    assert (Hdomσe : dom σe = ext_out A).
    {
      rewrite (wfworld_store_dom (ext_fun A (store_restrict σ (ext_in A)))
        σe HAe).
      apply ext_fun_dom. exact HprojA.
    }
    assert (HdomσBe : dom σBe = ext_out B).
    {
      rewrite (wfworld_store_dom (ext_fun B (store_restrict σB (ext_in B)))
        σBe HBe).
      apply ext_fun_dom. exact HprojB.
    }
    pose proof (res_extend_by_output_unique m A B n HA HB) as Hout.
    assert (HbaseA :
      store_restrict (σ ∪ σe) (world_dom (m : WorldT)) = σ).
    {
      apply (store_restrict_union_piece_l σ σe
        (world_dom (m : WorldT)) (ext_out A)); eauto.
      - set_solver.
      - set_solver.
      - pose proof (ext_app_out _ _ HAppA). set_solver.
    }
    assert (HbaseB :
      store_restrict (σB ∪ σBe) (world_dom (m : WorldT)) = σB).
    {
      apply (store_restrict_union_piece_l σB σBe
        (world_dom (m : WorldT)) (ext_out B)); eauto.
      - set_solver.
      - set_solver.
      - pose proof (ext_app_out _ _ HAppB). set_solver.
    }
    assert (HσB_eq : σB = σ).
    {
      rewrite <- Heq in HbaseB.
      rewrite HbaseA in HbaseB. symmetry. exact HbaseB.
    }
    subst σB.
    assert (HextraA :
      store_restrict (σ ∪ σe) (ext_out A) = σe).
    {
      apply (store_restrict_union_piece_r σ σe
        (world_dom (m : WorldT)) (ext_out A)); eauto.
      - set_solver.
      - set_solver.
      - pose proof (ext_app_out _ _ HAppA). set_solver.
    }
    assert (HextraB :
      store_restrict (σ ∪ σBe) (ext_out B) = σBe).
    {
      apply (store_restrict_union_piece_r σ σBe
        (world_dom (m : WorldT)) (ext_out B)); eauto.
      - set_solver.
      - set_solver.
      - pose proof (ext_app_out _ _ HAppB). set_solver.
    }
    assert (HσBe_eq : σBe = σe).
    {
      rewrite <- Heq in HextraB.
      rewrite <- Hout in HextraB.
      rewrite HextraA in HextraB. symmetry. exact HextraB.
    }
    subst σBe.
    replace (store_restrict σ (ext_in A))
      with (store_restrict σ (ext_in B)) by (rewrite HAB; reflexivity).
    exact HBe.
  }
  intros σ σe Hσ. split.
  - eapply Hdir; eauto.
  - intros HGe.
    eapply Hdir with (A := G) (B := F) (σ := σ) (σe := σe); eauto;
      symmetry; exact Hin.
Qed.

Lemma canonical_le_extension_unique m n F G :
  canonical_le_extension_spec m n F ->
  canonical_le_extension_spec m n G ->
  fiber_extension_equiv_on m F G.
Proof.
  intros [HFin [_ [_ HFext]]] [HGin [_ [_ HGext]]].
  eapply res_extend_by_fiber_equiv_on; eauto.
  rewrite HFin, HGin. reflexivity.
Qed.

(** ** Extension interaction API *)

Local Lemma store_restrict_union_ignore_r (s1 s2 : StoreT) (X : aset) :
  dom s2 ## X ->
  store_restrict (s1 ∪ s2) X = store_restrict s1 X.
Proof.
  intros Hdisj.
  apply (map_eq (M := gmap atom)). intros z.
  rewrite !store_restrict_lookup.
  destruct (decide (z ∈ X)) as [HzX | HzX]; [| reflexivity].
  destruct (s1 !! z) as [v|] eqn:Hs1.
  - rewrite (lookup_union_l' s1 s2 z) by eauto. reflexivity.
  - rewrite (lookup_union_r s1 s2 z) by exact Hs1.
    assert (Hs2 : s2 !! z = None).
    {
      apply not_elem_of_dom. intros Hz2.
      assert (Hzempty : z ∈ (∅ : aset)) by set_solver.
      apply elem_of_empty in Hzempty. exact Hzempty.
    }
    rewrite Hs2. symmetry. exact Hs1.
Qed.

Local Lemma store_union_swap_right (s1 s2 s3 : StoreT) :
  store_compat s2 s3 ->
  (s1 ∪ s2) ∪ s3 = (s1 ∪ s3) ∪ s2.
Proof.
  intros Hcompat.
  apply (map_eq (M := gmap atom)). intros i.
  rewrite option_eq. intros v.
  setoid_rewrite lookup_union_Some_raw.
  split.
  - intros [H12 | [H12none H3]].
    + rewrite lookup_union_Some_raw in H12.
      destruct H12 as [H1 | [H1none H2]].
      * left. rewrite lookup_union_Some_raw. left. exact H1.
      * destruct (s3 !! i) as [v3|] eqn:H3i.
        -- assert (v = v3) by (eapply Hcompat; eauto).
           subst. left. rewrite lookup_union_Some_raw. right. eauto.
        -- right. split.
           ++ rewrite lookup_union_None. eauto.
           ++ exact H2.
    + rewrite lookup_union_None in H12none.
      destruct H12none as [H1none H2none].
      left. rewrite lookup_union_Some_raw. right. eauto.
  - intros [H13 | [H13none H2]].
    + rewrite lookup_union_Some_raw in H13.
      destruct H13 as [H1 | [H1none H3]].
      * left. rewrite lookup_union_Some_raw. left. exact H1.
      * destruct (s2 !! i) as [v2|] eqn:H2i.
        -- assert (v2 = v) by (eapply Hcompat; eauto).
           subst. left. rewrite lookup_union_Some_raw. right. eauto.
        -- right. split.
           ++ rewrite lookup_union_None. eauto.
           ++ exact H3.
    + rewrite lookup_union_None in H13none.
      destruct H13none as [H1none H3none].
      left. rewrite lookup_union_Some_raw. right. eauto.
Qed.

Lemma res_extend_by_commute m F G mF mG mFG mGF :
  m #> F ~~> mF ->
  m #> G ~~> mG ->
  mF #> G ~~> mFG ->
  mG #> F ~~> mGF ->
  mFG = mGF.
Proof.
  intros HF HG HFG HGF.
  pose proof (res_extend_by_dom _ _ _ HF) as Hdom_mF.
  pose proof (res_extend_by_dom _ _ _ HG) as Hdom_mG.
  pose proof (res_extend_by_output_fresh _ _ _ HF) as HFfresh_m.
  pose proof (res_extend_by_output_fresh _ _ _ HG) as HGfresh_m.
  pose proof (res_extend_by_output_fresh _ _ _ HFG) as HGfresh_mF.
  pose proof (res_extend_by_output_fresh _ _ _ HGF) as HFfresh_mG.
  assert (HFGfresh : ext_out F ## ext_out G) by set_solver.
  assert (HGFfresh : ext_out G ## ext_out F) by set_solver.
  apply wfworld_ext. apply world_ext.
  - rewrite (res_extend_by_dom _ _ _ HFG).
    rewrite (res_extend_by_dom _ _ _ HGF).
    rewrite Hdom_mF, Hdom_mG. set_solver.
  - intros σ. split.
    + intros Hσ.
      apply (proj2 (res_extend_by_store_iff _ _ _ _ HGF)).
      apply (proj1 (res_extend_by_store_iff _ _ _ _ HFG)) in Hσ.
      destruct Hσ as [σmF [σge [HmFσ [HGσge ->]]]].
      apply (proj1 (res_extend_by_store_iff _ _ _ _ HF)) in HmFσ.
      destruct HmFσ as [σm [σfe [Hmσ [HFσfe ->]]]].
      pose proof (res_extend_store_compat m F σm σfe
        (res_extend_by_applicable _ _ _ HF) Hmσ HFσfe) as HcompatF.
      assert (Hdomσfe : dom σfe = ext_out F).
      {
        rewrite (wfworld_store_dom
          (ext_fun F (store_restrict σm (ext_in F))) σfe HFσfe).
        apply ext_fun_dom.
        eapply ext_projection_dom.
        - eapply res_extend_by_applicable. exact HF.
        - exact Hmσ.
      }
      assert (HprojG :
        store_restrict (σm ∪ σfe) (ext_in G) =
        store_restrict σm (ext_in G)).
      {
        apply store_restrict_union_ignore_r.
        rewrite Hdomσfe.
        pose proof (res_extend_by_input_subset _ _ _ HG).
        set_solver.
      }
      rewrite HprojG in HGσge.
      pose proof (res_extend_store_compat m G σm σge
        (res_extend_by_applicable _ _ _ HG) Hmσ HGσge) as HcompatG.
      assert (Hdomσge : dom σge = ext_out G).
      {
        rewrite (wfworld_store_dom
          (ext_fun G (store_restrict σm (ext_in G))) σge HGσge).
        apply ext_fun_dom.
        eapply ext_projection_dom.
        - eapply res_extend_by_applicable. exact HG.
        - exact Hmσ.
      }
      exists (σm ∪ σge), σfe. split.
      * apply (proj2 (res_extend_by_store_iff _ _ _ _ HG)).
        exists σm, σge. repeat split; eauto.
      * split.
        -- assert (HprojF :
             store_restrict (σm ∪ σge) (ext_in F) =
             store_restrict σm (ext_in F)).
           {
             apply store_restrict_union_ignore_r.
             rewrite Hdomσge.
             pose proof (res_extend_by_input_subset _ _ _ HF).
             set_solver.
           }
           rewrite HprojF. exact HFσfe.
		-- assert (Hcompat_extra : store_compat σfe σge).
		   {
		     apply disj_dom_store_compat.
		     change (dom σfe ∩ dom σge = ∅).
		     rewrite Hdomσfe, Hdomσge. set_solver.
		   }
           apply store_union_swap_right. exact Hcompat_extra.
    + intros Hσ.
      apply (proj2 (res_extend_by_store_iff _ _ _ _ HFG)).
      apply (proj1 (res_extend_by_store_iff _ _ _ _ HGF)) in Hσ.
      destruct Hσ as [σmG [σfe [HmGσ [HFσfe ->]]]].
      apply (proj1 (res_extend_by_store_iff _ _ _ _ HG)) in HmGσ.
      destruct HmGσ as [σm [σge [Hmσ [HGσge ->]]]].
      pose proof (res_extend_store_compat m G σm σge
        (res_extend_by_applicable _ _ _ HG) Hmσ HGσge) as HcompatG.
      assert (Hdomσge : dom σge = ext_out G).
      {
        rewrite (wfworld_store_dom
          (ext_fun G (store_restrict σm (ext_in G))) σge HGσge).
        apply ext_fun_dom.
        eapply ext_projection_dom.
        - eapply res_extend_by_applicable. exact HG.
        - exact Hmσ.
      }
      assert (HprojF :
        store_restrict (σm ∪ σge) (ext_in F) =
        store_restrict σm (ext_in F)).
      {
        apply store_restrict_union_ignore_r.
        rewrite Hdomσge.
        pose proof (res_extend_by_input_subset _ _ _ HF).
        set_solver.
      }
      rewrite HprojF in HFσfe.
      pose proof (res_extend_store_compat m F σm σfe
        (res_extend_by_applicable _ _ _ HF) Hmσ HFσfe) as HcompatF.
      assert (Hdomσfe : dom σfe = ext_out F).
      {
        rewrite (wfworld_store_dom
          (ext_fun F (store_restrict σm (ext_in F))) σfe HFσfe).
        apply ext_fun_dom.
        eapply ext_projection_dom.
        - eapply res_extend_by_applicable. exact HF.
        - exact Hmσ.
      }
      exists (σm ∪ σfe), σge. split.
      * apply (proj2 (res_extend_by_store_iff _ _ _ _ HF)).
        exists σm, σfe. repeat split; eauto.
      * split.
        -- assert (HprojG :
             store_restrict (σm ∪ σfe) (ext_in G) =
             store_restrict σm (ext_in G)).
           {
             apply store_restrict_union_ignore_r.
             rewrite Hdomσfe.
             pose proof (res_extend_by_input_subset _ _ _ HG).
             set_solver.
           }
           rewrite HprojG. exact HGσge.
	-- assert (Hcompat_extra : store_compat σge σfe).
	   {
	     apply disj_dom_store_compat.
	     change (dom σge ∩ dom σfe = ∅).
	     rewrite Hdomσge, Hdomσfe. set_solver.
	   }
           apply store_union_swap_right. exact Hcompat_extra.
Qed.

End WorldExtension.

Notation "m '#>' F '~~>' n" := (res_extend_by m F n)
  (at level 70, F at next level, n at next level).
