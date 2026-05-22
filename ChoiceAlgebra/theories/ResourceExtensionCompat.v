(** * Compatibility wrappers for resource extensions

    The core extension interface is relation-shaped: a fiber extension relates
    an input projection to one or more extension worlds.  This file keeps the
    old proof-facing names available while routing all semantics through that
    relation-shaped core. *)

From ChoicePrelude Require Import Prelude Store.
From ChoiceAlgebra Require Import ResourceCore ResourceKeyAction ResourceRestrict
  ResourceAlgebra ResourceExtension ResourceExtensionDerived ResourceInterface.
From Stdlib Require Import Logic.ClassicalEpsilon.

Section ResourceExtensionCompat.

Context {V : Type} `{ValueSig V}.

Local Notation WorldT := (World (V := V)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation FiberExtensionT := (fiber_extension (V := V)) (only parsing).
Local Notation StoreT := (Store (V := V)) (only parsing).

Definition ext_in (F : FiberExtensionT) : aset := extA_in F.
Definition ext_out (F : FiberExtensionT) : aset := extA_out F.
Definition ext_rel (F : FiberExtensionT) : StoreT -> WfWorldT -> Prop :=
  extA_rel F.

Definition mk_fiber_extension_rel
    (X Y : aset) (R : StoreT -> WfWorldT -> Prop)
    (Hdisj : X ## Y)
    (Hdom : forall σ w, dom σ = X -> R σ w -> world_dom (w : WorldT) = Y)
    (Hne : forall σ, dom σ = X -> exists w σe, R σ w /\ (w : WorldT) σe)
    (Hext : forall σ w1 w2 σe,
      dom σ = X -> R σ w1 -> R σ w2 ->
      ((w1 : WorldT) σe <-> (w2 : WorldT) σe))
    : FiberExtensionT :=
  mk_fiber_extensionA X Y R Hdisj Hdom Hne Hext.

Definition mk_fiber_extension
    (X Y : aset) (f : StoreT -> WfWorldT)
    (Hdisj : X ## Y)
    (Hdom : forall σ, dom σ = X -> world_dom (f σ : WorldT) = Y)
    (Hne : forall σ, dom σ = X -> exists σe, (f σ : WorldT) σe)
    : FiberExtensionT :=
  mk_fiber_extension_rel X Y
    (fun σ w => w = f σ)
    Hdisj
    ltac:(intros σ w Hσ ->; apply Hdom; exact Hσ)
    ltac:(intros σ Hσ; destruct (Hne σ Hσ) as [σe Hσe];
      exists (f σ), σe; split; [reflexivity | exact Hσe])
    ltac:(intros σ w1 w2 σe _ -> ->; reflexivity).

Definition mk_forall_extension
    (X : aset) (y : atom) (f : StoreT -> WfWorldT)
    (Hfresh : y ∉ X)
    (Hdom : forall σ, dom σ = X -> world_dom (f σ : WorldT) = {[y]})
    (Hne : forall σ, dom σ = X -> exists σy, (f σ : WorldT) σy)
    : FiberExtensionT :=
  mk_fiber_extension X {[y]} f ltac:(set_solver) Hdom Hne.

Definition forall_extension_shape (X : aset) (y : atom) (F : FiberExtensionT) : Prop :=
  ext_in F = X /\ ext_out F = {[y]}.

Local Lemma ext_rel_exists (F : FiberExtensionT) σ :
  dom σ = ext_in F ->
  exists w, ext_rel F σ w.
Proof.
  intros Hdom.
  destruct (extA_rel_nonempty F σ Hdom) as [w [σe [Hrel _]]].
  exists w. exact Hrel.
Qed.

Definition ext_fun (F : FiberExtensionT) (σ : StoreT) : WfWorldT.
Proof.
  destruct (decide (dom σ = ext_in F)) as [Hdom|_].
  - exact (proj1_sig (constructive_indefinite_description _
      (ext_rel_exists F σ Hdom))).
  - exact res_unit.
Defined.

Lemma ext_fun_rel F σ :
  dom σ = ext_in F ->
  ext_rel F σ (ext_fun F σ).
Proof.
  intros Hdom. unfold ext_fun.
  destruct (decide (dom σ = ext_in F)) as [Hdom'|Hbad].
  - destruct (constructive_indefinite_description _
      (ext_rel_exists F σ Hdom')) as [w Hrel].
    exact Hrel.
  - contradiction.
Qed.

Lemma ext_fun_dom F σ :
  dom σ = ext_in F ->
  world_dom (ext_fun F σ : WorldT) = ext_out F.
Proof.
  intros Hdom.
  unfold ext_in, ext_out in *.
  eapply extA_rel_dom; [exact Hdom | apply ext_fun_rel; exact Hdom].
Qed.

Lemma ext_fun_nonempty F σ :
  dom σ = ext_in F ->
  exists σe, (ext_fun F σ : WorldT) σe.
Proof.
  intros Hdom.
  destruct (extA_rel_nonempty F σ Hdom) as [w [σe [Hrel Hσe]]].
  exists σe.
  apply (proj1 (extA_rel_extensional F σ w (ext_fun F σ) σe Hdom
    Hrel (ext_fun_rel F σ Hdom))).
  exact Hσe.
Qed.

Definition fiber_extension_input_widen
    (F : FiberExtensionT) (X' : aset)
    (Hin : ext_in F ⊆ X')
    (Hdisj : X' ## ext_out F) : FiberExtensionT :=
  mk_fiber_extension_rel X' (ext_out F)
    (fun σ w => ext_rel F (store_restrict σ (ext_in F)) w)
    Hdisj
    ltac:(intros σ w Hσ Hrel;
      eapply extA_rel_dom; [| exact Hrel];
      change (dom (store_restrict σ (ext_in F) : gmap atom V) = ext_in F);
      rewrite store_restrict_dom; set_solver)
    ltac:(intros σ Hσ;
      eapply extA_rel_nonempty;
      change (dom (store_restrict σ (ext_in F) : gmap atom V) = ext_in F);
      rewrite store_restrict_dom; set_solver)
    ltac:(intros σ w1 w2 σe Hσ Hrel1 Hrel2;
      eapply extA_rel_extensional; [| exact Hrel1 | exact Hrel2];
      change (dom (store_restrict σ (ext_in F) : gmap atom V) = ext_in F);
      rewrite store_restrict_dom; set_solver).

Record fiber_extension_input_widen_to
    (F F' : FiberExtensionT) : Prop := {
  input_widen_in : ext_in F ⊆ ext_in F';
  input_widen_out : ext_out F' = ext_out F;
  input_widen_rel :
    forall σ w,
      dom σ = ext_in F' ->
      (ext_rel F' σ w <->
       ext_rel F (store_restrict σ (ext_in F)) w);
}.

Notation "F '~>i' F'" := (fiber_extension_input_widen_to F F')
  (at level 70).

Lemma fiber_extension_input_widen_to_shape F F' :
  F ~>i F' ->
  ext_in F ⊆ ext_in F' /\ ext_out F' = ext_out F.
Proof.
  intros Hwid. split.
  - exact (input_widen_in _ _ Hwid).
  - exact (input_widen_out _ _ Hwid).
Qed.

Lemma fiber_extension_input_widen_to_refl F :
  F ~>i F.
Proof.
  constructor; [reflexivity | reflexivity |].
  intros σ w Hσ. rewrite store_restrict_idemp_eq by exact Hσ.
  reflexivity.
Qed.

Lemma fiber_extension_input_widen_to_construct F X' Hin Hdisj :
  F ~>i fiber_extension_input_widen F X' Hin Hdisj.
Proof.
  constructor; [exact Hin | reflexivity |].
  intros σ w _. reflexivity.
Qed.

Lemma fiber_extension_input_widen_to_unique F F1 F2 :
  F ~>i F1 ->
  F ~>i F2 ->
  ext_in F1 = ext_in F2 ->
  ext_out F1 = ext_out F2 /\
  forall σ w,
    dom σ = ext_in F1 ->
    (ext_rel F1 σ w <-> ext_rel F2 σ w).
Proof.
  intros H1 H2 Hin. split.
  - rewrite (input_widen_out _ _ H1), (input_widen_out _ _ H2).
    reflexivity.
  - intros σ w Hσ.
    rewrite (input_widen_rel _ _ H1 σ w Hσ).
    rewrite (input_widen_rel _ _ H2 σ w ltac:(rewrite <- Hin; exact Hσ)).
    reflexivity.
Qed.

Lemma extension_applicable_input_widen_to (m : WfWorldT) F F' :
  F ~>i F' ->
  extension_applicable F' m ->
  extension_applicable F m.
Proof.
  intros Hwid Happ.
  constructor.
  - pose proof (input_widen_in _ _ Hwid). pose proof (extA_app_in _ _ Happ).
    set_solver.
  - pose proof (input_widen_out _ _ Hwid).
    pose proof (extA_app_out _ _ Happ).
    unfold ext_out in *. set_solver.
Qed.

Local Lemma input_widen_projection_eq
    (m : WfWorldT) F F' σ :
  F ~>i F' ->
  ext_in F' ⊆ world_dom (m : WorldT) ->
  (m : WorldT) σ ->
  store_restrict (store_restrict σ (ext_in F')) (ext_in F) =
  store_restrict σ (ext_in F).
Proof.
  intros Hwid Hin' Hσ.
  rewrite store_restrict_twice_subset; [reflexivity |].
  exact (input_widen_in _ _ Hwid).
Qed.

Lemma res_extend_by_input_widen_to_iff (m : WfWorldT) F F' (n : WfWorldT) :
  F ~>i F' ->
  ext_in F' ⊆ world_dom (m : WorldT) ->
  (res_extend_by m F n <-> res_extend_by m F' n).
Proof.
  intros Hwid Hin'. split.
  - intros [Happ [Hdom Hstores]].
    split.
    + constructor; [exact Hin' |].
      pose proof (input_widen_out _ _ Hwid) as Hout.
      pose proof (extA_app_out _ _ Happ) as Hfresh.
      unfold ext_out in *. set_solver.
    + split.
      * pose proof (input_widen_out _ _ Hwid) as Hout.
        unfold ext_out in Hout. rewrite Hdom, Hout. reflexivity.
      * intros σ. rewrite Hstores. split.
        -- intros [σm [we [σe [Hσm [Hrel [Hσe ->]]]]]].
           exists σm, we, σe. repeat split; eauto.
           assert (Hproj : dom (store_restrict σm (ext_in F')) = ext_in F').
           { change (dom (store_restrict σm (ext_in F') : gmap atom V) = ext_in F').
             rewrite store_restrict_dom.
             pose proof (wfworld_store_dom m σm Hσm) as Hdomσm.
             change (dom (σm : gmap atom V) = world_dom (m : WorldT)) in Hdomσm.
             rewrite Hdomσm. set_solver. }
           apply (proj2 (input_widen_rel _ _ Hwid
             (store_restrict σm (ext_in F')) we Hproj)).
           rewrite (input_widen_projection_eq m F F' σm Hwid Hin' Hσm).
           exact Hrel.
        -- intros [σm [we [σe [Hσm [Hrel [Hσe ->]]]]]].
           exists σm, we, σe. repeat split; eauto.
           assert (Hproj : dom (store_restrict σm (ext_in F')) = ext_in F').
           { change (dom (store_restrict σm (ext_in F') : gmap atom V) = ext_in F').
             rewrite store_restrict_dom.
             pose proof (wfworld_store_dom m σm Hσm) as Hdomσm.
             change (dom (σm : gmap atom V) = world_dom (m : WorldT)) in Hdomσm.
             rewrite Hdomσm. set_solver. }
           apply (proj1 (input_widen_rel _ _ Hwid
             (store_restrict σm (ext_in F')) we Hproj)) in Hrel.
           rewrite (input_widen_projection_eq m F F' σm Hwid Hin' Hσm) in Hrel.
           exact Hrel.
  - intros [Happ' [Hdom Hstores]].
    split.
    + exact (extension_applicable_input_widen_to m F F' Hwid Happ').
    + split.
      * pose proof (input_widen_out _ _ Hwid) as Hout.
        unfold ext_out in Hout. rewrite Hdom, Hout. reflexivity.
      * intros σ. rewrite Hstores. split.
        -- intros [σm [we [σe [Hσm [Hrel [Hσe ->]]]]]].
           exists σm, we, σe. repeat split; eauto.
           assert (Hproj : dom (store_restrict σm (ext_in F')) = ext_in F').
           { change (dom (store_restrict σm (ext_in F') : gmap atom V) = ext_in F').
             rewrite store_restrict_dom.
             pose proof (wfworld_store_dom m σm Hσm) as Hdomσm.
             change (dom (σm : gmap atom V) = world_dom (m : WorldT)) in Hdomσm.
             rewrite Hdomσm. set_solver. }
           apply (proj1 (input_widen_rel _ _ Hwid
             (store_restrict σm (ext_in F')) we Hproj)) in Hrel.
           rewrite (input_widen_projection_eq m F F' σm Hwid Hin' Hσm) in Hrel.
           exact Hrel.
        -- intros [σm [we [σe [Hσm [Hrel [Hσe ->]]]]]].
           exists σm, we, σe. repeat split; eauto.
           assert (Hproj : dom (store_restrict σm (ext_in F')) = ext_in F').
           { change (dom (store_restrict σm (ext_in F') : gmap atom V) = ext_in F').
             rewrite store_restrict_dom.
             pose proof (wfworld_store_dom m σm Hσm) as Hdomσm.
             change (dom (σm : gmap atom V) = world_dom (m : WorldT)) in Hdomσm.
             rewrite Hdomσm. set_solver. }
           apply (proj2 (input_widen_rel _ _ Hwid
             (store_restrict σm (ext_in F')) we Hproj)).
           rewrite (input_widen_projection_eq m F F' σm Hwid Hin' Hσm).
           exact Hrel.
Qed.

Lemma res_extend_by_commute_input_widen
    (m n : WfWorldT) (Fx F F' : FiberExtensionT) (my ny : WfWorldT) :
  res_extend_by m Fx n ->
  res_extend_by m F my ->
  F ~>i F' ->
  ext_in F' ⊆ world_dom (n : WorldT) ->
  (res_extend_by n F' ny <-> res_extend_by my Fx ny).
Proof.
  intros Hmx Hmy Hwid Hin'. split.
  - intros HnyF'.
    assert (HnyF : res_extend_by n F ny).
    {
      apply (proj2 (res_extend_by_input_widen_to_iff n F F' ny Hwid Hin')).
      exact HnyF'.
    }
    assert (Happ : extension_applicable Fx my).
    {
      constructor.
      - pose proof (resA_extend_by_applicable _ _ _ Hmx) as Happx.
        pose proof (resA_extend_by_dom _ _ _ Hmy) as Hdom_my.
        simpl in Hdom_my. rewrite Hdom_my.
        pose proof (extA_app_in _ _ Happx). set_solver.
      - pose proof (resA_extend_by_applicable _ _ _ Hmx) as Happx.
	        pose proof (resA_extend_by_applicable _ _ _ HnyF') as HappF'.
	        pose proof (resA_extend_by_dom _ _ _ Hmy) as Hdom_my.
	        pose proof (input_widen_out _ _ Hwid) as Hout.
	        unfold ext_out in Hout.
	        simpl in Hdom_my. rewrite Hdom_my.
	        rewrite <- Hout.
	        pose proof (extA_app_out _ _ Happx) as Hfreshx.
	        pose proof (extA_app_out _ _ HappF') as HfreshF'.
	        pose proof (resA_extend_by_dom _ _ _ Hmx) as Hdom_n.
	        simpl in Hdom_n. rewrite Hdom_n in HfreshF'. set_solver.
    }
    destruct (res_extend_by_exists my Fx Happ) as [ny' Hny'].
    pose proof (res_extend_by_commute m Fx F n my ny ny' Hmx Hmy HnyF Hny') as Heq.
    subst ny'. exact Hny'.
  - intros HnyFx.
    assert (Happ : extension_applicable F n).
	    {
	      constructor.
	      - pose proof (resA_extend_by_applicable _ _ _ Hmy) as HappF.
	        pose proof (resA_extend_by_dom _ _ _ Hmx) as Hdom_n.
	        simpl in Hdom_n. rewrite Hdom_n.
	        pose proof (extA_app_in _ _ HappF) as HinF.
	        set_solver.
	      - pose proof (resA_extend_by_applicable _ _ _ Hmy) as HappF.
	        pose proof (resA_extend_by_applicable _ _ _ HnyFx) as HappFx.
	        pose proof (resA_extend_by_dom _ _ _ Hmx) as Hdom_n.
	        pose proof (resA_extend_by_dom _ _ _ Hmy) as Hdom_my.
	        simpl in Hdom_n, Hdom_my. rewrite Hdom_n.
	        pose proof (extA_app_out _ _ HappF) as HfreshF.
	        pose proof (extA_app_out _ _ HappFx) as Hfreshx.
	        rewrite Hdom_my in Hfreshx. set_solver.
    }
    destruct (res_extend_by_exists n F Happ) as [ny' Hny'].
    pose proof (res_extend_by_commute m Fx F n my ny' ny Hmx Hmy Hny' HnyFx) as Heq.
    subst ny'.
    apply (proj1 (res_extend_by_input_widen_to_iff n F F' ny Hwid Hin')).
    exact Hny'.
Qed.

End ResourceExtensionCompat.

Notation "F '~>i' F'" := (fiber_extension_input_widen_to F F')
  (at level 70).
