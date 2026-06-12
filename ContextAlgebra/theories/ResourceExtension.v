From ContextBase Require Import Prelude LogicVar BaseTactics.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceCore ResourceAlgebra.
From Stdlib Require Import Logic.ProofIrrelevance.

(** * Fiber extensions for abstract resources *)

Section ResourceExtensionA.

Context {K : Type} `{Countable K} .
Context {V : Type} `{ValueSig V}.

Local Notation StoreAT := (gmap K V) (only parsing).
Local Notation WorldAT := (@WorldA K _ _ V) (only parsing).
Local Notation WfWorldAT := (@WfWorldA K _ _ V) (only parsing).

Record fiber_extensionA := {
  extA_in : gset K;
  extA_out : gset K;
  extA_disjoint : extA_in ## extA_out;
  extA_rel : StoreAT → WfWorldAT → Prop;

  extA_rel_dom :
    ∀ σ w,
      dom σ = extA_in →
      extA_rel σ w →
      worldA_dom (w : WorldAT) = extA_out;

  extA_rel_nonempty :
    ∀ σ,
      dom σ = extA_in →
      ∃ w σe, extA_rel σ w ∧ (w : WorldAT) σe;

  extA_rel_extensional :
    ∀ σ w1 w2 σe,
      dom σ = extA_in →
      extA_rel σ w1 →
      extA_rel σ w2 →
      ((w1 : WorldAT) σe ↔ (w2 : WorldAT) σe);
}.

Definition mk_fiber_extensionA
    (X Y : gset K) (R : StoreAT → WfWorldAT → Prop)
    (Hdisj : X ## Y)
    (Hdom : ∀ σ w, dom σ = X → R σ w → worldA_dom (w : WorldAT) = Y)
    (Hne : ∀ σ, dom σ = X → ∃ w σe, R σ w ∧ (w : WorldAT) σe)
    (Hext : ∀ σ w1 w2 σe,
      dom σ = X → R σ w1 → R σ w2 →
      ((w1 : WorldAT) σe ↔ (w2 : WorldAT) σe))
    : fiber_extensionA :=
  {| extA_in := X; extA_out := Y; extA_rel := R;
     extA_disjoint := Hdisj; extA_rel_dom := Hdom;
     extA_rel_nonempty := Hne; extA_rel_extensional := Hext |}.

Definition fiber_extensionA_functional_on (m : WfWorldAT) (F : fiber_extensionA) : Prop :=
  ∀ σ w σe1 σe2,
    (m : WorldAT) σ →
    extA_rel F (storeA_restrict σ (extA_in F)) w →
    (w : WorldAT) σe1 →
    (w : WorldAT) σe2 →
    σe1 = σe2.

Record extension_applicableA (F : fiber_extensionA) (m : WfWorldAT) : Prop := {
  extA_app_in : extA_in F ⊆ worldA_dom (m : WorldAT);
  extA_app_out : extA_out F ## worldA_dom (m : WorldAT);
}.

Definition resA_extend_by (m : WfWorldAT) (F : fiber_extensionA) (n : WfWorldAT) : Prop :=
  extension_applicableA F m ∧
  worldA_dom (n : WorldAT) = worldA_dom (m : WorldAT) ∪ extA_out F ∧
  ∀ σ,
    (n : WorldAT) σ ↔
      ∃ σm we σe,
        (m : WorldAT) σm ∧
        extA_rel F (storeA_restrict σm (extA_in F)) we ∧
        (we : WorldAT) σe ∧
        σ = @union (gmap K V) _ σm σe.

Notation "m '#>' F '~~A>' n" := (resA_extend_by m F n)
  (at level 70, F at next level, n at next level).

Definition fiber_extensionA_equiv_on (m : WfWorldAT) (F G : fiber_extensionA) : Prop :=
  extA_in F = extA_in G ∧
  ∀ σ wF wG σe,
    (m : WorldAT) σ →
    extA_rel F (storeA_restrict σ (extA_in F)) wF →
    extA_rel G (storeA_restrict σ (extA_in G)) wG →
    ((wF : WorldAT) σe ↔ (wG : WorldAT) σe).

Lemma resA_extend_by_applicable m F n :
  m #> F ~~A> n →
  extension_applicableA F m.
Proof. intros [Happ _]. exact Happ. Qed.

Lemma resA_extend_by_dom m F n :
  m #> F ~~A> n →
  worldA_dom (n : WorldAT) = worldA_dom (m : WorldAT) ∪ extA_out F.
Proof. intros [_ [Hdom _]]. exact Hdom. Qed.

Lemma resA_extend_by_store_iff m F n σ :
  m #> F ~~A> n →
  (n : WorldAT) σ ↔
    ∃ σm we σe,
      (m : WorldAT) σm ∧
      extA_rel F (storeA_restrict σm (extA_in F)) we ∧
      (we : WorldAT) σe ∧
      σ = @union (gmap K V) _ σm σe.
Proof. intros [_ [_ Hstores]]. exact (Hstores σ). Qed.

Lemma extA_projection_dom m F σm :
  extension_applicableA F m →
  (m : WorldAT) σm →
  dom (storeA_restrict σm (extA_in F)) = extA_in F.
Proof.
  intros Happ Hσm.
  transitivity (worldA_dom (m : WorldAT) ∩ extA_in F).
  - rewrite <- (wfworldA_store_dom m σm Hσm).
    apply storeA_restrict_dom.
  - pose proof (extA_app_in _ _ Happ). set_solver.
Qed.

Lemma extA_output_store_dom F σ we σe :
  dom (σ : gmap K V) = extA_in F →
  extA_rel F σ we →
  (we : WorldAT) σe →
  dom (σe : gmap K V) = extA_out F.
Proof.
  intros Hdomσ HF Hσe.
  pose proof (wfworldA_store_dom we σe Hσe) as Hdom_we.
  rewrite Hdom_we.
  eapply extA_rel_dom; eauto.
Qed.

Lemma extA_output_store_dom_from_base m F σm we σe :
  extension_applicableA F m →
  (m : WorldAT) σm →
  extA_rel F (storeA_restrict σm (extA_in F)) we →
  (we : WorldAT) σe →
  dom (σe : gmap K V) = extA_out F.
Proof.
  intros Happ Hσm HF Hσe.
  eapply extA_output_store_dom; [| exact HF | exact Hσe].
  eapply extA_projection_dom; eauto.
Qed.

Lemma resA_extend_store_compat m F σm we σe :
  extension_applicableA F m →
  (m : WorldAT) σm →
  extA_rel F (storeA_restrict σm (extA_in F)) we →
  (we : WorldAT) σe →
  storeA_compat σm σe.
Proof.
  intros Happ Hσm HF Hσe.
  apply storeA_disj_dom_compat.
  change (dom (σm : gmap K V) ∩ dom (σe : gmap K V) = ∅).
  pose proof (wfworldA_store_dom m σm Hσm) as Hdomσm.
  assert (Hdomσe : dom (σe : gmap K V) = extA_out F).
  { eapply extA_output_store_dom_from_base; eauto. }
  rewrite Hdomσm, Hdomσe.
  pose proof (extA_app_out _ _ Happ). set_solver.
Qed.

Lemma resA_extend_by_exists m F :
  extension_applicableA F m →
  ∃ n, m #> F ~~A> n.
Proof.
  intros Happ.
  unshelve eexists.
  - refine (exist _ {|
      worldA_dom := worldA_dom (m : WorldAT) ∪ extA_out F;
      worldA_stores := fun σ =>
        exists σm we σe,
          (m : WorldAT) σm /\
          extA_rel F (storeA_restrict σm (extA_in F)) we /\
          (we : WorldAT) σe /\
          σ = @union (gmap K V) _ σm σe
    |} _).
    constructor.
    + destruct (worldA_wf m) as [Hne _].
      destruct Hne as [σm Hσm].
      assert (Hproj_dom :
          dom (storeA_restrict σm (extA_in F)) = extA_in F)
        by (eapply extA_projection_dom; eauto).
      destruct (extA_rel_nonempty F
        (storeA_restrict σm (extA_in F)) Hproj_dom)
        as [we [σe [HF Hσe]]].
      exists (@union (gmap K V) _ (σm : gmap K V) (σe : gmap K V)).
      exists σm, we, σe. repeat split; eauto.
    + intros σ [σm [we [σe [Hσm [HF [Hσe ->]]]]]].
      transitivity (dom (σm : gmap K V) ∪ dom (σe : gmap K V)).
      * apply storeA_union_dom.
        eapply resA_extend_store_compat; eauto.
      * pose proof (wfworldA_store_dom m σm Hσm) as Hdomσm.
        pose proof (extA_output_store_dom_from_base m F σm we σe
          Happ Hσm HF Hσe) as Hdomσe.
        rewrite Hdomσm, Hdomσe.
        set_solver.
  - split; [exact Happ |].
    split; [reflexivity |].
    intros σ. reflexivity.
Qed.

Lemma resA_extend_by_projection_eq m n F my ny :
  resA_restrict m (extA_in F) = resA_restrict n (extA_in F) →
  m #> F ~~A> my →
  n #> F ~~A> ny →
  resA_restrict my (extA_in F ∪ extA_out F) =
  resA_restrict ny (extA_in F ∪ extA_out F).
Proof.
  intros Hproj Hmy Hny.
  apply wfworldA_ext. apply worldA_ext.
  - simpl.
    rewrite (resA_extend_by_dom _ _ _ Hmy).
    rewrite (resA_extend_by_dom _ _ _ Hny).
    pose proof (resA_extend_by_applicable _ _ _ Hmy) as Happ_m.
    pose proof (resA_extend_by_applicable _ _ _ Hny) as Happ_n.
    pose proof (extA_app_in _ _ Happ_m) as Hin_m.
    pose proof (extA_app_in _ _ Happ_n) as Hin_n.
    pose proof (extA_app_out _ _ Happ_m) as Hout_m.
    pose proof (extA_app_out _ _ Happ_n) as Hout_n.
    set_solver.
  - intros σ. split.
    + intros [σmy [Hσmy Hrestrict]].
      apply (proj1 (resA_extend_by_store_iff _ _ _ _ Hmy)) in Hσmy.
      destruct Hσmy as [σm [we [σe [Hσm [HF [Hσe ->]]]]]].
      assert (Hσm_proj :
          (resA_restrict m (extA_in F) : WorldAT)
            (storeA_restrict σm (extA_in F))).
      { exists σm. split; [exact Hσm | reflexivity]. }
      rewrite Hproj in Hσm_proj.
      destruct Hσm_proj as [σn [Hσn Hσn_proj]].
      pose proof (extA_output_store_dom_from_base m F σm we σe
        (resA_extend_by_applicable _ _ _ Hmy) Hσm HF Hσe) as Hdomσe.
      exists (@union (gmap K V) _ (σn : gmap K V) (σe : gmap K V)).
      split.
      * apply (proj2 (resA_extend_by_store_iff _ _ _ _ Hny)).
        exists σn, we, σe. repeat split; eauto.
        rewrite Hσn_proj. exact HF.
      * rewrite <- Hrestrict.
        rewrite !storeA_restrict_union_cover.
        -- rewrite Hσn_proj. reflexivity.
        -- eapply (resA_extend_store_compat m F σm we σe); eauto.
           exact (resA_extend_by_applicable _ _ _ Hmy).
        -- pose proof (wfworldA_store_dom m σm Hσm) as Hdomσm.
           rewrite Hdomσm.
           exact (extA_app_in _ _ (resA_extend_by_applicable _ _ _ Hmy)).
        -- rewrite Hdomσe. set_solver.
        -- eapply (resA_extend_store_compat n F σn we σe).
           ++ exact (resA_extend_by_applicable _ _ _ Hny).
           ++ exact Hσn.
           ++ rewrite Hσn_proj. exact HF.
           ++ exact Hσe.
        -- pose proof (wfworldA_store_dom n σn Hσn) as Hdomσn.
           rewrite Hdomσn.
           exact (extA_app_in _ _ (resA_extend_by_applicable _ _ _ Hny)).
        -- rewrite Hdomσe. set_solver.
    + intros [σny [Hσny Hrestrict]].
      apply (proj1 (resA_extend_by_store_iff _ _ _ _ Hny)) in Hσny.
      destruct Hσny as [σn [we [σe [Hσn [HF [Hσe ->]]]]]].
      assert (Hσn_proj :
          (resA_restrict n (extA_in F) : WorldAT)
            (storeA_restrict σn (extA_in F))).
      { exists σn. split; [exact Hσn | reflexivity]. }
      rewrite <- Hproj in Hσn_proj.
      destruct Hσn_proj as [σm [Hσm Hσm_proj]].
      pose proof (extA_output_store_dom_from_base n F σn we σe
        (resA_extend_by_applicable _ _ _ Hny) Hσn HF Hσe) as Hdomσe.
      exists (@union (gmap K V) _ (σm : gmap K V) (σe : gmap K V)).
      split.
      * apply (proj2 (resA_extend_by_store_iff _ _ _ _ Hmy)).
        exists σm, we, σe. repeat split; eauto.
        rewrite Hσm_proj. exact HF.
      * rewrite <- Hrestrict.
        rewrite !storeA_restrict_union_cover.
        -- rewrite Hσm_proj. reflexivity.
        -- eapply (resA_extend_store_compat n F σn we σe); eauto.
           exact (resA_extend_by_applicable _ _ _ Hny).
        -- pose proof (wfworldA_store_dom n σn Hσn) as Hdomσn.
           rewrite Hdomσn.
           exact (extA_app_in _ _ (resA_extend_by_applicable _ _ _ Hny)).
        -- rewrite Hdomσe. set_solver.
        -- eapply (resA_extend_store_compat m F σm we σe).
           ++ exact (resA_extend_by_applicable _ _ _ Hmy).
           ++ exact Hσm.
           ++ rewrite Hσm_proj. exact HF.
           ++ exact Hσe.
        -- pose proof (wfworldA_store_dom m σm Hσm) as Hdomσm.
           rewrite Hdomσm.
           exact (extA_app_in _ _ (resA_extend_by_applicable _ _ _ Hmy)).
        -- rewrite Hdomσe. set_solver.
Qed.

Lemma resA_extend_by_restrict_base m F n :
  m #> F ~~A> n →
  resA_restrict n (worldA_dom (m : WorldAT)) = m.
Proof.
  intros Hext.
  destruct Hext as [Happ [Hdom_n Hstores]].
  apply wfworldA_ext. apply worldA_ext.
  - simpl. rewrite Hdom_n.
    pose proof (extA_app_out _ _ Happ). set_solver.
  - intros σ. split.
    + intros [σn [Hσn Hrestrict]].
      rewrite Hstores in Hσn.
      destruct Hσn as [σm [we [σe [Hσm [HF [Hσe ->]]]]]].
      pose proof (resA_extend_store_compat m F σm we σe Happ Hσm HF Hσe)
        as Hcompat.
      pose proof (wfworldA_store_dom m σm Hσm) as Hdomσm.
      pose proof (extA_output_store_dom_from_base m F σm we σe
        Happ Hσm HF Hσe) as Hdomσe.
      assert (Hpiece :
          storeA_restrict (@union (gmap K V) _ σm σe)
            (worldA_dom (m : WorldAT)) = σm).
      {
        apply (storeA_restrict_union_piece_l σm σe
          (worldA_dom (m : WorldAT)) (extA_out F)).
        - exact Hcompat.
        - change (dom (σm : gmap K V) ⊆ worldA_dom (m : WorldAT)).
          rewrite Hdomσm. reflexivity.
        - change (dom (σe : gmap K V) ⊆ extA_out F).
          rewrite Hdomσe. reflexivity.
        - pose proof (extA_app_out _ _ Happ). set_solver.
      }
      rewrite Hpiece in Hrestrict. subst. exact Hσm.
    + intros Hσ.
      pose proof (wfworldA_store_dom m σ Hσ) as Hdomσ.
      assert (Hproj_dom :
          dom (storeA_restrict σ (extA_in F)) = extA_in F)
        by (eapply extA_projection_dom; eauto).
      destruct (extA_rel_nonempty F
        (storeA_restrict σ (extA_in F)) Hproj_dom)
        as [we [σe [HF Hσe]]].
      exists (@union (gmap K V) _ (σ : gmap K V) (σe : gmap K V)).
      split.
      * rewrite Hstores.
        exists σ, we, σe. repeat split; eauto.
      * pose proof (resA_extend_store_compat m F σ we σe Happ Hσ HF Hσe)
          as Hcompat.
        pose proof (extA_output_store_dom_from_base m F σ we σe
          Happ Hσ HF Hσe) as Hdomσe.
        apply (storeA_restrict_union_piece_l σ σe
          (worldA_dom (m : WorldAT)) (extA_out F)).
        -- exact Hcompat.
        -- change (dom (σ : gmap K V) ⊆ worldA_dom (m : WorldAT)).
           rewrite Hdomσ. reflexivity.
        -- change (dom (σe : gmap K V) ⊆ extA_out F).
           rewrite Hdomσe. reflexivity.
        -- pose proof (extA_app_out _ _ Happ). set_solver.
Qed.

Lemma resA_extend_by_le m F n :
  m #> F ~~A> n →
  m ⊑ n.
Proof.
  intros Hext.
  unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le.
  change ((m : WorldAT) = rawA_restrict n (worldA_dom (m : WorldAT))).
  exact (f_equal (fun w : WfWorldAT => (w : WorldAT))
    (eq_sym (resA_extend_by_restrict_base m F n Hext))).
Qed.

Lemma resA_extend_by_le_mono
    (m n mx nx : WfWorldAT) (F : fiber_extensionA) :
  m ⊑ n ->
  m #> F ~~A> mx ->
  n #> F ~~A> nx ->
  mx ⊑ nx.
Proof.
  intros Hle Hmx Hnx.
  pose proof (resA_extend_by_applicable _ _ _ Hmx) as Happ_m.
  pose proof (resA_extend_by_applicable _ _ _ Hnx) as Happ_n.
  unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le.
  apply worldA_ext.
  - simpl.
    rewrite (resA_extend_by_dom _ _ _ Hmx).
    rewrite (resA_extend_by_dom _ _ _ Hnx).
    pose proof (rawA_le_dom (m : WorldAT) (n : WorldAT) Hle) as Hdom.
    set_solver.
  - intros σ. split.
    + intros Hσmx.
      apply (proj1 (resA_extend_by_store_iff _ _ _ _ Hmx)) in Hσmx.
      destruct Hσmx as [σm [we [σe [Hσm [HF [Hσe ->]]]]]].
      rewrite Hle in Hσm.
      destruct Hσm as [σn [Hσn Hproj]].
      exists (@union (gmap K V) _ σn σe). split.
      * apply (proj2 (resA_extend_by_store_iff _ _ _ _ Hnx)).
        exists σn, we, σe. repeat split; eauto.
        replace (storeA_restrict σn (extA_in F))
          with (storeA_restrict σm (extA_in F)).
        -- exact HF.
        -- rewrite <- Hproj.
           rewrite storeA_restrict_twice_subset; [reflexivity|].
           exact (extA_app_in _ _ Happ_m).
      * change (storeA_restrict (@union (gmap K V) _ σn σe)
          (worldA_dom (mx : WorldAT)) = @union (gmap K V) _ σm σe).
        assert (HFn : extA_rel F (storeA_restrict σn (extA_in F)) we).
        {
          replace (storeA_restrict σn (extA_in F))
            with (storeA_restrict σm (extA_in F)); [exact HF|].
          rewrite <- Hproj.
          rewrite storeA_restrict_twice_subset; [reflexivity|].
          exact (extA_app_in _ _ Happ_m).
        }
        rewrite (resA_extend_by_dom _ _ _ Hmx).
        rewrite storeA_restrict_union_cover.
        -- rewrite Hproj.
           pose proof (extA_output_store_dom_from_base n F σn we σe
             Happ_n Hσn HFn Hσe) as Hdomσe.
           rewrite (storeA_restrict_idemp_eq σe (extA_out F) Hdomσe).
           reflexivity.
        -- eapply resA_extend_store_compat; eauto.
        -- change (worldA_dom (m : WorldAT) ⊆ dom (σn : gmap K V)).
           pose proof (wfworldA_store_dom n σn Hσn) as Hdomσn.
           rewrite Hdomσn.
           exact (rawA_le_dom (m : WorldAT) (n : WorldAT) Hle).
        -- pose proof (extA_output_store_dom_from_base n F σn we σe
             Happ_n Hσn HFn Hσe) as Hdomσe.
           rewrite Hdomσe. set_solver.
    + intros [σnx [Hσnx Hrestrict]].
      apply (proj1 (resA_extend_by_store_iff _ _ _ _ Hnx)) in Hσnx.
      destruct Hσnx as [σn [we [σe [Hσn [HF [Hσe ->]]]]]].
      assert (Hσm :
          (m : WorldAT) (storeA_restrict σn (worldA_dom (m : WorldAT)))).
      {
        set (D := worldA_dom (m : WorldAT)).
        change ((m : WorldAT) (storeA_restrict σn D)).
        rewrite Hle. exists σn. split; [exact Hσn|reflexivity].
      }
      apply (proj2 (resA_extend_by_store_iff _ _ _ _ Hmx)).
      exists (storeA_restrict σn (worldA_dom (m : WorldAT))), we, σe.
      repeat split.
      * exact Hσm.
      * rewrite storeA_restrict_twice_subset; [exact HF|].
        exact (extA_app_in _ _ Happ_m).
      * exact Hσe.
      * rewrite <- Hrestrict.
        change (storeA_restrict (@union (gmap K V) _ σn σe)
          (worldA_dom (mx : WorldAT)) =
          @union (gmap K V) _
            (storeA_restrict σn (worldA_dom (m : WorldAT))) σe).
        rewrite (resA_extend_by_dom _ _ _ Hmx).
        rewrite storeA_restrict_union_cover.
        -- pose proof (extA_output_store_dom_from_base n F σn we σe
             Happ_n Hσn HF Hσe) as Hdomσe.
           rewrite (storeA_restrict_idemp_eq σe (extA_out F) Hdomσe).
           reflexivity.
        -- eapply resA_extend_store_compat; eauto.
        -- change (worldA_dom (m : WorldAT) ⊆ dom (σn : gmap K V)).
           pose proof (wfworldA_store_dom n σn Hσn) as Hdomσn.
           rewrite Hdomσn.
           exact (rawA_le_dom (m : WorldAT) (n : WorldAT) Hle).
        -- pose proof (extA_output_store_dom_from_base n F σn we σe
             Happ_n Hσn HF Hσe) as Hdomσe.
          rewrite Hdomσe. set_solver.
Qed.

Lemma resA_extend_by_sum
    (m1 m2 m1x m2x : WfWorldAT) (F : fiber_extensionA)
    (Hdef : rawA_sum_defined m1 m2) :
  m1 #> F ~~A> m1x ->
  m2 #> F ~~A> m2x ->
  exists Hdefx : rawA_sum_defined m1x m2x,
    resA_sum m1 m2 Hdef #> F ~~A>
      resA_sum m1x m2x Hdefx.
Proof.
  intros Hext1 Hext2.
  pose proof (resA_extend_by_applicable _ _ _ Hext1) as Happ1.
  pose proof (resA_extend_by_applicable _ _ _ Hext2) as Happ2.
  assert (Hdefx : rawA_sum_defined m1x m2x).
  {
    unfold rawA_sum_defined.
    rewrite (resA_extend_by_dom _ _ _ Hext1).
    rewrite (resA_extend_by_dom _ _ _ Hext2).
    unfold rawA_sum_defined in Hdef.
    rewrite Hdef. reflexivity.
  }
  exists Hdefx.
  split.
  - constructor.
    + cbn. exact (extA_app_in _ _ Happ1).
    + cbn. exact (extA_app_out _ _ Happ1).
  - split.
    + cbn.
      rewrite (resA_extend_by_dom _ _ _ Hext1).
      reflexivity.
    + intros σ. split.
      * intros [Hσ | Hσ].
        -- apply (proj1 (resA_extend_by_store_iff _ _ _ _ Hext1)) in Hσ.
           destruct Hσ as [σm [we [σe [Hσm [HF [Hσe ->]]]]]].
           exists σm, we, σe. repeat split; eauto.
           left. exact Hσm.
        -- apply (proj1 (resA_extend_by_store_iff _ _ _ _ Hext2)) in Hσ.
           destruct Hσ as [σm [we [σe [Hσm [HF [Hσe ->]]]]]].
           exists σm, we, σe. repeat split; eauto.
           right. exact Hσm.
      * intros [σm [we [σe [[Hσm | Hσm] [HF [Hσe ->]]]]]].
        -- left.
           apply (proj2 (resA_extend_by_store_iff _ _ _ _ Hext1)).
           exists σm, we, σe. repeat split; eauto.
        -- right.
           apply (proj2 (resA_extend_by_store_iff _ _ _ _ Hext2)).
           exists σm, we, σe. repeat split; eauto.
Qed.

Lemma resA_extend_by_product_frame_r
    (m1 m1x m2 : WfWorldAT) (F : fiber_extensionA)
    (Hc : worldA_compat m1 m2) :
  m1 #> F ~~A> m1x →
  extA_out F ## worldA_dom (m2 : WorldAT) →
  ∃ Hcx : worldA_compat m1x m2,
    resA_product m1 m2 Hc #> F ~~A>
      resA_product m1x m2 Hcx.
Proof.
  intros Hext Hout_frame.
  pose proof (resA_extend_by_applicable _ _ _ Hext) as Happ.
  assert (Hcx : worldA_compat m1x m2).
  {
    intros σ1x σ2 Hσ1x Hσ2.
    apply (proj1 (resA_extend_by_store_iff _ _ _ _ Hext)) in Hσ1x.
    destruct Hσ1x as [σ1 [we [σe [Hσ1 [HF [Hσe ->]]]]]].
    apply storeA_compat_union_intro_l.
    - exact (Hc σ1 σ2 Hσ1 Hσ2).
    - apply storeA_disj_dom_compat.
      pose proof (extA_output_store_dom_from_base m1 F σ1 we σe
        Happ Hσ1 HF Hσe) as Hdomσe.
      pose proof (wfworldA_store_dom m2 σ2 Hσ2) as Hdomσ2.
      rewrite Hdomσe, Hdomσ2. set_solver.
  }
  exists Hcx.
  split.
  - constructor.
    + cbn. pose proof (extA_app_in _ _ Happ) as Hin. set_solver.
    + cbn. pose proof (extA_app_out _ _ Happ) as Hout. set_solver.
  - split.
    + cbn. rewrite (resA_extend_by_dom _ _ _ Hext). set_solver.
    + intros σ. split.
    * intros [σ1x [σ2 [Hσ1x [Hσ2 [Hcompat_x2 ->]]]]].
      apply (proj1 (resA_extend_by_store_iff _ _ _ _ Hext)) in Hσ1x.
      destruct Hσ1x as [σ1 [we [σe [Hσ1 [HF [Hσe ->]]]]]].
      exists (@union (gmap K V) _ σ1 σ2), we, σe.
      repeat split.
      -- cbn. exists σ1, σ2. repeat split; eauto.
      -- assert (Hproj :
            (storeA_restrict (@union (gmap K V) _ σ1 σ2) (extA_in F) : gmap K V) =
            storeA_restrict σ1 (extA_in F)).
        {
          apply storeA_restrict_union_absorb_l_on.
          - exact (Hc σ1 σ2 Hσ1 Hσ2).
          - pose proof (wfworldA_store_dom m1 σ1 Hσ1) as Hdomσ1.
            pose proof (extA_app_in _ _ Happ) as Hin.
            rewrite Hdomσ1. exact Hin.
        }
        rewrite Hproj. exact HF.
      -- exact Hσe.
      -- apply storeA_union_extend_frame_r.
        apply storeA_disj_dom_compat.
        pose proof (extA_output_store_dom_from_base m1 F σ1 we σe
          Happ Hσ1 HF Hσe) as Hdomσe.
        pose proof (wfworldA_store_dom m2 σ2 Hσ2) as Hdomσ2.
        rewrite Hdomσe, Hdomσ2. set_solver.
    * intros [σ12 [we [σe [Hσ12 [HF [Hσe ->]]]]]].
      cbn in Hσ12.
      destruct Hσ12 as [σ1 [σ2 [Hσ1 [Hσ2 [Hcompat12 ->]]]]].
      assert (Hproj :
          (storeA_restrict (@union (gmap K V) _ σ1 σ2) (extA_in F) : gmap K V) =
          storeA_restrict σ1 (extA_in F)).
      {
        apply storeA_restrict_union_absorb_l_on.
        - exact Hcompat12.
        - pose proof (wfworldA_store_dom m1 σ1 Hσ1) as Hdomσ1.
          pose proof (extA_app_in _ _ Happ) as Hin.
          rewrite Hdomσ1. exact Hin.
      }
      rewrite Hproj in HF.
      exists (@union (gmap K V) _ σ1 σe), σ2.
      repeat split.
      -- apply (proj2 (resA_extend_by_store_iff _ _ _ _ Hext)).
        exists σ1, we, σe. repeat split; eauto.
      -- exact Hσ2.
      -- apply storeA_compat_union_intro_l.
        ++ exact Hcompat12.
        ++ apply storeA_disj_dom_compat.
           pose proof (extA_output_store_dom_from_base m1 F σ1 we σe
             Happ Hσ1 HF Hσe) as Hdomσe.
           pose proof (wfworldA_store_dom m2 σ2 Hσ2) as Hdomσ2.
           rewrite Hdomσe, Hdomσ2. set_solver.
      -- symmetry. apply storeA_union_extend_frame_r.
        apply storeA_disj_dom_compat.
        pose proof (extA_output_store_dom_from_base m1 F σ1 we σe
          Happ Hσ1 HF Hσe) as Hdomσe.
        pose proof (wfworldA_store_dom m2 σ2 Hσ2) as Hdomσ2.
        rewrite Hdomσe, Hdomσ2. set_solver.
Qed.

Lemma resA_extend_by_product_frame_l
    (m1 m1x m2 : WfWorldAT) (F : fiber_extensionA)
    (Hc : worldA_compat m2 m1) :
  m1 #> F ~~A> m1x →
  extA_out F ## worldA_dom (m2 : WorldAT) →
  ∃ Hcx : worldA_compat m2 m1x,
    resA_product m2 m1 Hc #> F ~~A>
      resA_product m2 m1x Hcx.
Proof.
  intros Hext Hout_frame.
  pose proof (resA_extend_by_applicable _ _ _ Hext) as Happ.
  assert (Hcx : worldA_compat m2 m1x).
  {
    intros σ2 σ1x Hσ2 Hσ1x.
    apply (proj1 (resA_extend_by_store_iff _ _ _ _ Hext)) in Hσ1x.
    destruct Hσ1x as [σ1 [we [σe [Hσ1 [HF [Hσe ->]]]]]].
    apply storeA_compat_union_intro_r.
    - exact (Hc σ2 σ1 Hσ2 Hσ1).
    - apply storeA_disj_dom_compat.
      pose proof (wfworldA_store_dom m2 σ2 Hσ2) as Hdomσ2.
      pose proof (extA_output_store_dom_from_base m1 F σ1 we σe
        Happ Hσ1 HF Hσe) as Hdomσe.
      rewrite Hdomσ2, Hdomσe. set_solver.
  }
  exists Hcx.
  split.
  - constructor.
    + cbn. pose proof (extA_app_in _ _ Happ) as Hin. set_solver.
    + cbn. pose proof (extA_app_out _ _ Happ) as Hout. set_solver.
  - split.
    + cbn. rewrite (resA_extend_by_dom _ _ _ Hext). set_solver.
    + intros σ. split.
    * intros [σ2 [σ1x [Hσ2 [Hσ1x [Hcompat_2x ->]]]]].
      apply (proj1 (resA_extend_by_store_iff _ _ _ _ Hext)) in Hσ1x.
      destruct Hσ1x as [σ1 [we [σe [Hσ1 [HF [Hσe ->]]]]]].
      exists (@union (gmap K V) _ σ2 σ1), we, σe.
      repeat split.
      -- cbn. exists σ2, σ1. repeat split; eauto.
      -- assert (Hproj :
            (storeA_restrict (@union (gmap K V) _ σ2 σ1) (extA_in F) : gmap K V) =
            storeA_restrict σ1 (extA_in F)).
        {
          apply storeA_restrict_union_absorb_r_on.
          - exact (Hc σ2 σ1 Hσ2 Hσ1).
          - pose proof (wfworldA_store_dom m1 σ1 Hσ1) as Hdomσ1.
            pose proof (extA_app_in _ _ Happ) as Hin.
            rewrite Hdomσ1. exact Hin.
        }
        rewrite Hproj. exact HF.
      -- exact Hσe.
      -- rewrite map_union_assoc. reflexivity.
    * intros [σ21 [we [σe [Hσ21 [HF [Hσe ->]]]]]].
      cbn in Hσ21.
      destruct Hσ21 as [σ2 [σ1 [Hσ2 [Hσ1 [Hcompat21 ->]]]]].
      assert (Hproj :
          (storeA_restrict (@union (gmap K V) _ σ2 σ1) (extA_in F) : gmap K V) =
          storeA_restrict σ1 (extA_in F)).
      {
        apply storeA_restrict_union_absorb_r_on.
        - exact Hcompat21.
        - pose proof (wfworldA_store_dom m1 σ1 Hσ1) as Hdomσ1.
          pose proof (extA_app_in _ _ Happ) as Hin.
          rewrite Hdomσ1. exact Hin.
      }
      rewrite Hproj in HF.
      exists σ2, (@union (gmap K V) _ σ1 σe).
      repeat split.
      -- exact Hσ2.
      -- apply (proj2 (resA_extend_by_store_iff _ _ _ _ Hext)).
        exists σ1, we, σe. repeat split; eauto.
      -- apply storeA_compat_union_intro_r.
        ++ exact Hcompat21.
        ++ apply storeA_disj_dom_compat.
           pose proof (wfworldA_store_dom m2 σ2 Hσ2) as Hdomσ2.
           pose proof (extA_output_store_dom_from_base m1 F σ1 we σe
             Happ Hσ1 HF Hσe) as Hdomσe.
           rewrite Hdomσ2, Hdomσe. set_solver.
      -- rewrite map_union_assoc. reflexivity.
Qed.

(** * Fiber extension equivalence and commuting lemmas *)


Local Notation "m '#>' F '~~A>' n" := (resA_extend_by m F n)
  (at level 70, F at next level, n at next level).

End ResourceExtensionA.
