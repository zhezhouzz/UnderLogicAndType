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

Lemma resA_extend_by_dom_subsets m F n :
  m #> F ~~A> n →
  worldA_dom (m : WorldAT) ⊆ worldA_dom (n : WorldAT) ∧
  extA_out F ⊆ worldA_dom (n : WorldAT).
Proof.
  intros Hext.
  rewrite (resA_extend_by_dom m F n Hext).
  set_solver.
Qed.

Lemma resA_extend_by_dom_base_subset m F n :
  m #> F ~~A> n →
  worldA_dom (m : WorldAT) ⊆ worldA_dom (n : WorldAT).
Proof.
  intros Hext. exact (proj1 (resA_extend_by_dom_subsets m F n Hext)).
Qed.

Lemma resA_extend_by_dom_output_subset m F n :
  m #> F ~~A> n →
  extA_out F ⊆ worldA_dom (n : WorldAT).
Proof.
  intros Hext. exact (proj2 (resA_extend_by_dom_subsets m F n Hext)).
Qed.

Lemma ext_applicableA_parallel_r
    (m mx my : WfWorldAT) (F G : fiber_extensionA) :
  m #> F ~~A> mx →
  m #> G ~~A> my →
  extA_out G ## worldA_dom (mx : WorldAT) →
  extension_applicableA F my.
Proof.
  intros HmF HmG HoutG.
  constructor.
  - pose proof (resA_extend_by_applicable m F mx HmF) as HappF.
    pose proof (resA_extend_by_dom m G my HmG) as Hdom_my.
    rewrite Hdom_my.
    pose proof (extA_app_in F m HappF). set_solver.
  - pose proof (resA_extend_by_applicable m F mx HmF) as HappF.
    pose proof (resA_extend_by_dom m F mx HmF) as Hdom_mx.
    pose proof (resA_extend_by_dom m G my HmG) as Hdom_my.
    rewrite Hdom_my.
    rewrite Hdom_mx in HoutG.
    pose proof (extA_app_out F m HappF). set_solver.
Qed.

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

Lemma resA_extend_store_restrict_base m F σm we σe :
  extension_applicableA F m →
  (m : WorldAT) σm →
  extA_rel F (storeA_restrict σm (extA_in F)) we →
  (we : WorldAT) σe →
  storeA_restrict (@union (gmap K V) _ σm σe)
    (worldA_dom (m : WorldAT)) = σm.
Proof.
  intros Happ Hσm HF Hσe.
  pose proof (resA_extend_store_compat m F σm we σe Happ Hσm HF Hσe)
    as Hcompat.
  pose proof (wfworldA_store_dom m σm Hσm) as Hdomσm.
  pose proof (extA_output_store_dom_from_base m F σm we σe
    Happ Hσm HF Hσe) as Hdomσe.
  apply (storeA_restrict_union_piece_l σm σe
    (worldA_dom (m : WorldAT)) (extA_out F)).
  - exact Hcompat.
  - change (dom (σm : gmap K V) ⊆ worldA_dom (m : WorldAT)).
    rewrite Hdomσm. reflexivity.
  - change (dom (σe : gmap K V) ⊆ extA_out F).
    rewrite Hdomσe. reflexivity.
	  - pose proof (extA_app_out _ _ Happ). set_solver.
Qed.

Lemma resA_extend_by_slice_restrict_base
    (m : WfWorldAT) F (n p : WfWorldAT)
    (Hsub : resA_subset p (resA_restrict n (worldA_dom (m : WorldAT)))) :
  m #> F ~~A> n →
  worldA_dom (p : WorldAT) = worldA_dom (m : WorldAT) →
  resA_subset p m →
  p #> F ~~A> resA_slice_restrict n (worldA_dom (m : WorldAT)) p Hsub.
Proof.
  intros Hext Hdom_p Hsub_p_m.
  pose proof (resA_extend_by_applicable _ _ _ Hext) as Happ.
  split.
  - constructor.
    + rewrite Hdom_p. exact (extA_app_in _ _ Happ).
    + rewrite Hdom_p. exact (extA_app_out _ _ Happ).
  - split.
    + simpl. rewrite (resA_extend_by_dom _ _ _ Hext), Hdom_p. reflexivity.
    + intros σ. split.
      * intros [Hσn Hσp].
      apply (proj1 (resA_extend_by_store_iff _ _ _ _ Hext)) in Hσn.
      destruct Hσn as [σm [we [σe [Hσm [HFrel [Hσe ->]]]]]].
      exists σm, we, σe. repeat split; eauto.
      replace σm with (storeA_restrict
        (@union (gmap K V) _ σm σe) (worldA_dom (m : WorldAT))).
      -- exact Hσp.
      -- exact (resA_extend_store_restrict_base m F σm we σe
          Happ Hσm HFrel Hσe).
      * intros [σp [we [σe [Hσp [HFrel [Hσe ->]]]]]].
      split.
      -- apply (proj2 (resA_extend_by_store_iff _ _ _ _ Hext)).
        exists σp, we, σe. repeat split; eauto.
        exact (proj2 Hsub_p_m σp Hσp).
      -- pose proof (proj2 Hsub_p_m σp Hσp) as Hσm.
        rewrite (resA_extend_store_restrict_base m F σp we σe
          Happ Hσm HFrel Hσe).
        exact Hσp.
Qed.

Lemma resA_extend_store_restrict_other_input m F G σm we σe :
  extension_applicableA F m →
  extension_applicableA G m →
  (m : WorldAT) σm →
  extA_rel F (storeA_restrict σm (extA_in F)) we →
  (we : WorldAT) σe →
  storeA_restrict (@union (gmap K V) _ σm σe)
    (extA_in G) =
  storeA_restrict σm (extA_in G).
Proof.
  intros HappF HappG Hσm HF Hσe.
  apply storeA_restrict_union_ignore_r.
  rewrite (extA_output_store_dom_from_base m F σm we σe
    HappF Hσm HF Hσe).
  pose proof (extA_app_in _ _ HappG).
  pose proof (extA_app_out _ _ HappF).
  set_solver.
Qed.

(** * Fiber extension equivalence and commuting lemmas *)


Local Notation "m '#>' F '~~A>' n" := (resA_extend_by m F n)
  (at level 70, F at next level, n at next level).

Lemma fiber_extensionA_functional_outputs_eq
    (m : WfWorldAT) (F : fiber_extensionA)
    (σ : StoreAT) (w1 w2 : WfWorldAT) (σe1 σe2 : StoreAT) :
  extension_applicableA F m →
  fiber_extensionA_functional_on m F →
  (m : WorldAT) σ →
  extA_rel F (storeA_restrict σ (extA_in F)) w1 →
  extA_rel F (storeA_restrict σ (extA_in F)) w2 →
  (w1 : WorldAT) σe1 →
  (w2 : WorldAT) σe2 →
  σe1 = σe2.
Proof.
  intros Happ Hfun Hσ Hw1 Hw2 Hσe1 Hσe2.
  assert (Hproj_dom :
      dom (storeA_restrict σ (extA_in F)) = extA_in F)
    by (eapply extA_projection_dom; eauto).
  pose proof (proj1 (extA_rel_extensional F
    (storeA_restrict σ (extA_in F)) w1 w2 σe1
    Hproj_dom Hw1 Hw2) Hσe1) as Hσe1_w2.
  eapply Hfun; eauto.
Qed.

Lemma extA_output_stores_compat_from_same_base
    (m : WfWorldAT) (F G : fiber_extensionA)
    (σm : StoreAT) (wF wG : WfWorldAT) (σF σG : StoreAT) :
  extension_applicableA F m →
  extension_applicableA G m →
  extA_out F ## extA_out G →
  (m : WorldAT) σm →
  extA_rel F (storeA_restrict σm (extA_in F)) wF →
  (wF : WorldAT) σF →
  extA_rel G (storeA_restrict σm (extA_in G)) wG →
  (wG : WorldAT) σG →
  storeA_compat σF σG.
Proof.
  intros HappF HappG Hdisj Hσm HFrel HFstore HGrel HGstore.
  apply storeA_disj_dom_compat.
  change (dom (σF : gmap K V) ∩ dom (σG : gmap K V) = ∅).
  rewrite (extA_output_store_dom_from_base m F σm wF σF
    HappF Hσm HFrel HFstore).
  rewrite (extA_output_store_dom_from_base m G σm wG σG
    HappG Hσm HGrel HGstore).
  set_solver.
Qed.

Lemma resA_extend_by_commute
    (m : WfWorldAT) (F G : fiber_extensionA)
    (mF mG mFG mGF : WfWorldAT) :
  m #> F ~~A> mF →
  m #> G ~~A> mG →
  mF #> G ~~A> mFG →
  mG #> F ~~A> mGF →
  mFG = mGF.
Proof.
  intros HF HG HFG HGF.
  pose proof (resA_extend_by_dom _ _ _ HF) as Hdom_mF.
  pose proof (resA_extend_by_dom _ _ _ HG) as Hdom_mG.
  pose proof (resA_extend_by_applicable _ _ _ HF) as HAppF_m.
  pose proof (resA_extend_by_applicable _ _ _ HG) as HAppG_m.
  pose proof (resA_extend_by_applicable _ _ _ HFG) as HAppG_mF.
  pose proof (resA_extend_by_applicable _ _ _ HGF) as HAppF_mG.
  pose proof (extA_app_out _ _ HAppF_m) as HFfresh_m.
  pose proof (extA_app_out _ _ HAppG_m) as HGfresh_m.
  pose proof (extA_app_out _ _ HAppG_mF) as HGfresh_mF.
  pose proof (extA_app_out _ _ HAppF_mG) as HFfresh_mG.
  assert (HFGfresh : extA_out F ## extA_out G) by set_solver.
  assert (HGFfresh : extA_out G ## extA_out F) by set_solver.
  apply wfworldA_ext. apply worldA_ext.
  - rewrite (resA_extend_by_dom _ _ _ HFG).
    rewrite (resA_extend_by_dom _ _ _ HGF).
    rewrite Hdom_mF, Hdom_mG. set_solver.
  - intros σ. split.
    + intros Hσ.
      apply (proj2 (resA_extend_by_store_iff _ _ _ _ HGF)).
      apply (proj1 (resA_extend_by_store_iff _ _ _ _ HFG)) in Hσ.
      destruct Hσ as [σmF [wG [σge [HmFσ [HGrel [HGstore ->]]]]]].
      apply (proj1 (resA_extend_by_store_iff _ _ _ _ HF)) in HmFσ.
      destruct HmFσ as [σm [wF [σfe [Hmσ [HFrel [HFstore ->]]]]]].
      assert (HprojG :
          storeA_restrict (@union (gmap K V) _ σm σfe) (extA_in G) =
          storeA_restrict σm (extA_in G)).
      {
        exact (resA_extend_store_restrict_other_input m F G σm wF σfe
          HAppF_m HAppG_m Hmσ HFrel HFstore).
      }
      rewrite HprojG in HGrel.
      exists (@union (gmap K V) _ (σm : gmap K V) (σge : gmap K V)), wF, σfe.
      split.
      * apply (proj2 (resA_extend_by_store_iff _ _ _ _ HG)).
        exists σm, wG, σge. repeat split; eauto.
      * split.
        -- assert (HprojF :
             storeA_restrict
               (@union (gmap K V) _ σm σge) (extA_in F) =
             storeA_restrict σm (extA_in F)).
           {
             exact (resA_extend_store_restrict_other_input m G F σm wG σge
               HAppG_m HAppF_m Hmσ HGrel HGstore).
           }
           rewrite HprojF. exact HFrel.
        -- split; [exact HFstore |].
           pose proof (extA_output_stores_compat_from_same_base
             m F G σm wF wG σfe σge HAppF_m HAppG_m HFGfresh
             Hmσ HFrel HFstore HGrel HGstore) as Hcompat_extra.
           apply storeA_union_swap_right. exact Hcompat_extra.
    + intros Hσ.
      apply (proj2 (resA_extend_by_store_iff _ _ _ _ HFG)).
      apply (proj1 (resA_extend_by_store_iff _ _ _ _ HGF)) in Hσ.
      destruct Hσ as [σmG [wF [σfe [HmGσ [HFrel [HFstore ->]]]]]].
      apply (proj1 (resA_extend_by_store_iff _ _ _ _ HG)) in HmGσ.
      destruct HmGσ as [σm [wG [σge [Hmσ [HGrel [HGstore ->]]]]]].
      assert (HprojF :
          storeA_restrict (@union (gmap K V) _ σm σge) (extA_in F) =
          storeA_restrict σm (extA_in F)).
      {
        exact (resA_extend_store_restrict_other_input m G F σm wG σge
          HAppG_m HAppF_m Hmσ HGrel HGstore).
      }
      rewrite HprojF in HFrel.
      exists (@union (gmap K V) _ (σm : gmap K V) (σfe : gmap K V)), wG, σge.
      split.
      * apply (proj2 (resA_extend_by_store_iff _ _ _ _ HF)).
        exists σm, wF, σfe. repeat split; eauto.
      * split.
        -- assert (HprojG :
             storeA_restrict
               (@union (gmap K V) _ σm σfe) (extA_in G) =
             storeA_restrict σm (extA_in G)).
           {
             exact (resA_extend_store_restrict_other_input m F G σm wF σfe
               HAppF_m HAppG_m Hmσ HFrel HFstore).
           }
           rewrite HprojG. exact HGrel.
        -- split; [exact HGstore |].
           pose proof (extA_output_stores_compat_from_same_base
             m G F σm wG wF σge σfe HAppG_m HAppF_m HGFfresh
             Hmσ HGrel HGstore HFrel HFstore) as Hcompat_extra.
           apply storeA_union_swap_right. exact Hcompat_extra.
Qed.

Lemma resA_extend_component_restrict_subset
    (m : WfWorldAT) F (n nsum ni : WfWorldAT) :
  resA_extend_by m F n →
  nsum ⊑ n →
  (∀ σ, (ni : WorldAT) σ → (nsum : WorldAT) σ) →
  worldA_dom (m : WorldAT) ⊆ worldA_dom (ni : WorldAT) →
  worldA_dom (m : WorldAT) ⊆ worldA_dom (nsum : WorldAT) →
  resA_subset (resA_restrict ni (worldA_dom (m : WorldAT))) m.
Proof.
  intros Hext Hsum_le Hinto Hdom_m_ni Hdom_m_sum.
  split.
  - simpl. set_solver.
  - intros σ Hσ.
    rewrite <- (resA_extend_by_restrict_base m F n Hext).
    simpl in Hσ |- *.
    destruct Hσ as [σi [Hσi Hrestrict_i]].
    unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le in Hsum_le.
    pose proof (Hinto σi Hσi) as Hsumσi.
    rewrite Hsum_le in Hsumσi. simpl in Hsumσi.
    destruct Hsumσi as [σn [Hσn Hrestrict_sum]].
    exists σn. split; [exact Hσn |].
    rewrite <- Hrestrict_i, <- Hrestrict_sum.
    rewrite storeA_restrict_restrict.
    f_equal.
    pose proof (rawA_le_dom _ _ Hsum_le) as Hdom_sum_n.
    set_solver.
Qed.

Lemma resA_extend_by_functional_store_eq_from_base
    (m : WfWorldAT) F (n : WfWorldAT) (σ1 σ2 : StoreAT) :
  resA_extend_by m F n →
  fiber_extensionA_functional_on m F →
  (n : WorldAT) σ1 →
  (n : WorldAT) σ2 →
  storeA_restrict σ1 (worldA_dom (m : WorldAT)) =
  storeA_restrict σ2 (worldA_dom (m : WorldAT)) →
  σ1 = σ2.
Proof.
  intros Hext Hfun Hσ1 Hσ2 Hbase_eq.
  pose proof (resA_extend_by_applicable _ _ _ Hext) as Happ.
  apply (proj1 (resA_extend_by_store_iff _ _ _ _ Hext)) in Hσ1.
  apply (proj1 (resA_extend_by_store_iff _ _ _ _ Hext)) in Hσ2.
  destruct Hσ1 as [σm1 [we1 [σe1 [Hσm1 [HFrel1 [Hσe1 ->]]]]]].
  destruct Hσ2 as [σm2 [we2 [σe2 [Hσm2 [HFrel2 [Hσe2 ->]]]]]].
  assert (Hbase1 :
    storeA_restrict (@union (gmap K V) _ σm1 σe1)
      (worldA_dom (m : WorldAT)) = σm1).
  { exact (resA_extend_store_restrict_base m F σm1 we1 σe1
      Happ Hσm1 HFrel1 Hσe1). }
  assert (Hbase2 :
    storeA_restrict (@union (gmap K V) _ σm2 σe2)
      (worldA_dom (m : WorldAT)) = σm2).
  { exact (resA_extend_store_restrict_base m F σm2 we2 σe2
      Happ Hσm2 HFrel2 Hσe2). }
  assert (Hσm2_eq : σm2 = σm1).
  {
    rewrite Hbase1 in Hbase_eq.
    rewrite Hbase2 in Hbase_eq.
    symmetry. exact Hbase_eq.
  }
  subst σm2.
  pose proof (fiber_extensionA_functional_outputs_eq m F σm1 we2 we1 σe2 σe1
    Happ Hfun Hσm1 HFrel2 HFrel1 Hσe2 Hσe1) as Hσe_eq.
  subst σe2. reflexivity.
Qed.

Lemma resA_extend_by_sum_pullback
    (m : WfWorldAT) F (n n1 n2 : WfWorldAT)
    (Hdef : rawA_sum_defined (n1 : WorldAT) (n2 : WorldAT)) :
  resA_extend_by m F n →
  fiber_extensionA_functional_on m F →
  worldA_dom (m : WorldAT) ⊆ worldA_dom (n1 : WorldAT) →
  worldA_dom (m : WorldAT) ⊆ worldA_dom (n2 : WorldAT) →
  resA_sum n1 n2 Hdef ⊑ n →
  ∃ (m1 m2 : WfWorldAT) (Hdefm : rawA_sum_defined m1 m2)
    (n1' n2' : WfWorldAT),
    worldA_dom (m1 : WorldAT) = worldA_dom (m : WorldAT) ∧
    worldA_dom (m2 : WorldAT) = worldA_dom (m : WorldAT) ∧
    resA_subset m1 m ∧
    resA_subset m2 m ∧
    resA_sum m1 m2 Hdefm ⊑ m ∧
    resA_extend_by m1 F n1' ∧
    n1 ⊑ n1' ∧
    resA_extend_by m2 F n2' ∧
    n2 ⊑ n2'.
Proof.
  intros Hext Hfun Hdom_m_n1 Hdom_m_n2 Hsum_le.
  set (X := worldA_dom (m : WorldAT)).
  set (m1 := resA_restrict n1 X).
  set (m2 := resA_restrict n2 X).
  assert (Hdom_m1 : worldA_dom (m1 : WorldAT) = X).
  { subst m1 X. simpl. set_solver. }
  assert (Hdom_m2 : worldA_dom (m2 : WorldAT) = X).
  { subst m2 X. simpl. set_solver. }
  assert (Hsub_m1_m : resA_subset m1 m).
  {
    subst m1 X.
    eapply resA_extend_component_restrict_subset
      with (F := F) (n := n) (nsum := resA_sum n1 n2 Hdef).
    - exact Hext.
    - exact Hsum_le.
    - intros σ Hσ. simpl. left. exact Hσ.
    - exact Hdom_m_n1.
    - simpl. set_solver.
  }
  assert (Hsub_m2_m : resA_subset m2 m).
  {
    subst m2 X.
    eapply resA_extend_component_restrict_subset
      with (F := F) (n := n) (nsum := resA_sum n1 n2 Hdef).
    - exact Hext.
    - exact Hsum_le.
    - intros σ Hσ. simpl. right. exact Hσ.
    - exact Hdom_m_n2.
    - simpl. set_solver.
  }
  assert (Hsub_m1_n : resA_subset m1 (resA_restrict n X)).
  {
    subst X. rewrite (resA_extend_by_restrict_base m F n Hext).
    exact Hsub_m1_m.
  }
  assert (Hsub_m2_n : resA_subset m2 (resA_restrict n X)).
  {
    subst X. rewrite (resA_extend_by_restrict_base m F n Hext).
    exact Hsub_m2_m.
  }
  set (n1' := resA_slice_restrict n X m1 Hsub_m1_n).
  set (n2' := resA_slice_restrict n X m2 Hsub_m2_n).
  assert (Hm1ext : resA_extend_by m1 F n1').
  {
    subst n1' X.
    eapply resA_extend_by_slice_restrict_base; eauto.
  }
  assert (Hm2ext : resA_extend_by m2 F n2').
  {
    subst n2' X.
    eapply resA_extend_by_slice_restrict_base; eauto.
  }
  assert (Hdefm : rawA_sum_defined (m1 : WorldAT) (m2 : WorldAT)).
  { unfold rawA_sum_defined. rewrite Hdom_m1, Hdom_m2. reflexivity. }
  exists m1, m2, Hdefm, n1', n2'.
  split; [subst X; exact Hdom_m1 |].
  split; [subst X; exact Hdom_m2 |].
  split; [exact Hsub_m1_m |].
  split; [exact Hsub_m2_m |].
  refine (conj _ (conj Hm1ext (conj _ (conj Hm2ext _)))).
  - subst m1 m2 X.
    rewrite (resA_restrict_sum n1 n2 (worldA_dom (m : WorldAT)) Hdef Hdefm).
    pose proof (resA_restrict_le_mono (resA_sum n1 n2 Hdef) n
      (worldA_dom (m : WorldAT)) Hsum_le) as Hle_restrict.
    rewrite (resA_extend_by_restrict_base m F n Hext) in Hle_restrict.
    exact Hle_restrict.
  - subst n1'. unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le.
    apply worldA_ext.
    + simpl.
      pose proof (rawA_le_dom _ _ Hsum_le) as Hdom_sum_n.
      simpl in Hdom_sum_n. set_solver.
    + intros σ. simpl. split.
      * intros Hσ1.
        unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le in Hsum_le.
        assert ((resA_sum n1 n2 Hdef : WorldAT) σ) as Hsumσ.
        { simpl. left. exact Hσ1. }
        rewrite Hsum_le in Hsumσ. simpl in Hsumσ.
        destruct Hsumσ as [σn [Hσn Hrestrict]].
        exists σn. split; [| exact Hrestrict].
        split; [exact Hσn |].
        subst m1. simpl.
        exists σ. split; [exact Hσ1 |].
        rewrite <- Hrestrict.
        rewrite storeA_restrict_restrict.
        replace (worldA_dom (n1 : WorldAT) ∩ X) with X by set_solver.
        reflexivity.
      * intros [σn [[Hσn Hσm1] Hrestrict]].
        subst m1. simpl in Hσm1.
        destruct Hσm1 as [σ1 [Hσ1 Hσ1_proj]].
        unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le in Hsum_le.
        assert ((resA_sum n1 n2 Hdef : WorldAT) σ1) as Hsumσ1.
        { simpl. left. exact Hσ1. }
        rewrite Hsum_le in Hsumσ1. simpl in Hsumσ1.
        destruct Hsumσ1 as [σn1 [Hσn1 Hrestrict1]].
        assert (Hbase_eq :
          storeA_restrict σn X = storeA_restrict σn1 X).
        {
          rewrite <- Hσ1_proj.
          rewrite <- Hrestrict1.
          rewrite storeA_restrict_restrict.
          replace (worldA_dom (resA_sum n1 n2 Hdef : WorldAT) ∩ X)
            with X by (simpl; set_solver).
          reflexivity.
        }
        pose proof (resA_extend_by_functional_store_eq_from_base
          m F n σn σn1 Hext Hfun Hσn Hσn1 ltac:(subst X; exact Hbase_eq))
          as ->.
        rewrite Hrestrict1 in Hrestrict.
        subst σ.
        exact Hσ1.
  - subst n2'. unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le.
    apply worldA_ext.
    + simpl.
      pose proof (rawA_le_dom _ _ Hsum_le) as Hdom_sum_n.
      simpl in Hdom_sum_n |- *. rewrite <- Hdef. set_solver.
    + intros σ. simpl. split.
      * intros Hσ2.
        unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le in Hsum_le.
        assert ((resA_sum n1 n2 Hdef : WorldAT) σ) as Hsumσ.
        { simpl. right. exact Hσ2. }
        rewrite Hsum_le in Hsumσ. simpl in Hsumσ.
        destruct Hsumσ as [σn [Hσn Hrestrict]].
        exists σn. split.
        2:{ rewrite <- Hdef. exact Hrestrict. }
        split; [exact Hσn |].
        subst m2. simpl.
        exists σ. split; [exact Hσ2 |].
        rewrite <- Hrestrict.
        rewrite storeA_restrict_restrict.
        replace (worldA_dom (n1 : WorldAT) ∩ X) with X by set_solver.
        reflexivity.
      * intros [σn [[Hσn Hσm2] Hrestrict]].
        subst m2. simpl in Hσm2.
        destruct Hσm2 as [σ2 [Hσ2 Hσ2_proj]].
        unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le in Hsum_le.
        assert ((resA_sum n1 n2 Hdef : WorldAT) σ2) as Hsumσ2.
        { simpl. right. exact Hσ2. }
        rewrite Hsum_le in Hsumσ2. simpl in Hsumσ2.
        destruct Hsumσ2 as [σn2 [Hσn2 Hrestrict2]].
        assert (Hbase_eq :
          storeA_restrict σn X = storeA_restrict σn2 X).
        {
          rewrite <- Hσ2_proj.
          rewrite <- Hrestrict2.
          rewrite storeA_restrict_restrict.
          replace (worldA_dom (resA_sum n1 n2 Hdef : WorldAT) ∩ X)
            with X by (simpl; rewrite Hdef; set_solver).
          reflexivity.
        }
        pose proof (resA_extend_by_functional_store_eq_from_base
          m F n σn σn2 Hext Hfun Hσn Hσn2 ltac:(subst X; exact Hbase_eq))
          as ->.
        assert (Hrestrict2' :
          storeA_restrict σn2 (worldA_dom (n2 : WorldAT)) = σ2).
        {
          rewrite <- Hdef. exact Hrestrict2.
        }
        rewrite Hrestrict2' in Hrestrict.
        subst σ.
        exact Hσ2.
Qed.

Lemma resA_one_point_extension_pushout
    (m n my : WfWorldAT) (y : K) :
  m ⊑ n →
  y ∉ worldA_dom (n : WorldAT) →
  worldA_dom (my : WorldAT) = worldA_dom (m : WorldAT) ∪ {[y]} →
  resA_restrict my (worldA_dom (m : WorldAT)) = m →
  ∃ ny : WfWorldAT,
    worldA_dom (ny : WorldAT) = worldA_dom (n : WorldAT) ∪ {[y]} ∧
    resA_restrict ny (worldA_dom (n : WorldAT)) = n ∧
    my ⊑ ny.
Proof.
  intros Hmn Hy_n Hdom_my Hrestr_my.
  pose proof (rawA_le_dom m n Hmn) as Hdom_m_n.
  pose (raw_ny := ({|
    worldA_dom := worldA_dom (n : WorldAT) ∪ {[y]};
    worldA_stores := λ τ,
      ∃ σn σy,
        (n : WorldAT) σn ∧
        (my : WorldAT) σy ∧
        storeA_restrict σn (worldA_dom (m : WorldAT)) =
          storeA_restrict σy (worldA_dom (m : WorldAT)) ∧
        τ = @union (gmap K V) _ σn
          (storeA_restrict σy ({[y]} : gset K))
  |} : WorldAT)).
  assert (Hwf_ny : wf_worldA raw_ny).
  {
    constructor.
    - destruct (wfA_ne _ (worldA_wf my)) as [σy Hσy].
      assert (Hm_proj :
          (m : WorldAT) (storeA_restrict σy (worldA_dom (m : WorldAT)))).
      {
        eapply resA_restrict_eq_project_store; [exact Hrestr_my | exact Hσy].
      }
      unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le in Hmn.
      rewrite Hmn in Hm_proj. simpl in Hm_proj.
      destruct Hm_proj as [σn [Hσn Hrestrict]].
      exists (@union (gmap K V) _ (σn : gmap K V)
        (storeA_restrict σy ({[y]} : gset K) : gmap K V)).
      simpl. exists σn, σy. repeat split; eauto.
      replace (worldA_dom (n : WorldAT) ∩ worldA_dom (m : WorldAT))
        with (worldA_dom (m : WorldAT)) in Hrestrict by set_solver.
      exact Hrestrict.
    - intros τ [σn [σy [Hσn [Hσy [Hagree ->]]]]].
      pose proof (wfworldA_store_dom n σn Hσn) as Hdomσn.
      pose proof (wfworldA_store_dom my σy Hσy) as Hdomσy.
      assert (Hcompat :
          storeA_compat σn (storeA_restrict σy ({[y]} : gset K))).
      {
        apply storeA_compat_restrict_singleton_fresh.
        change (y ∉ (dom (σn : gmap K V) : gset K)).
        rewrite Hdomσn. exact Hy_n.
      }
      change (dom (@union (gmap K V) _ (σn : gmap K V)
        (storeA_restrict σy ({[y]} : gset K) : gmap K V)) =
        worldA_dom (n : WorldAT) ∪ {[y]}).
      rewrite (storeA_union_dom σn
        (storeA_restrict σy ({[y]} : gset K)) Hcompat).
      pose proof (storeA_restrict_dom σy ({[y]} : gset K)) as Hdom_restr.
      change (dom (storeA_restrict σy ({[y]} : gset K) : gmap K V) =
        dom (σy : gmap K V) ∩ ({[y]} : gset K)) in Hdom_restr.
      rewrite Hdom_restr. rewrite Hdomσn.
      apply set_eq. intros z. split.
      * intros Hz.
        apply elem_of_union in Hz as [Hz|Hz]; [set_solver |].
        apply elem_of_intersection in Hz as [Hzy Hy].
        change (z ∈ (dom (σy : gmap K V) : gset K)) in Hzy.
        rewrite Hdomσy, Hdom_my in Hzy. set_solver.
      * intros Hz.
        apply elem_of_union.
        destruct (decide (z ∈ worldA_dom (n : WorldAT))) as [Hzn|Hzn].
        -- left. exact Hzn.
        -- right. apply elem_of_intersection. split.
           ++ change (z ∈ (dom (σy : gmap K V) : gset K)).
              rewrite Hdomσy, Hdom_my. set_solver.
           ++ set_solver.
  }
  exists (exist _ raw_ny Hwf_ny). split.
  - reflexivity.
  - split.
    + apply wfworldA_ext. apply worldA_ext.
      * simpl. set_solver.
      * intros τ. simpl. split.
        -- intros [τny [[σn [σy [Hσn [Hσy [Hagree ->]]]]] Hrestrict]].
           rewrite (storeA_restrict_union_piece_l
             σn (storeA_restrict σy ({[y]} : gset K))
             (worldA_dom (n : WorldAT)) ({[y]} : gset K)) in Hrestrict.
           ++ subst τ. exact Hσn.
           ++ apply storeA_compat_restrict_singleton_fresh.
              pose proof (wfworldA_store_dom n σn Hσn) as Hdomσn.
              change (y ∉ (dom (σn : gmap K V) : gset K)).
              rewrite Hdomσn. exact Hy_n.
           ++ pose proof (wfworldA_store_dom n σn Hσn) as Hdomσn.
              intros z Hz. change (z ∈ (dom (σn : gmap K V) : gset K)) in Hz.
              rewrite Hdomσn in Hz. exact Hz.
           ++ apply storeA_restrict_dom_subset.
           ++ set_solver.
        -- intros Hτn.
           assert (Hm_proj :
               (m : WorldAT) (storeA_restrict τ (worldA_dom (m : WorldAT)))).
           {
             unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le in Hmn.
             rewrite Hmn at 1. simpl. exists τ. split; [exact Hτn | reflexivity].
           }
           assert (Hraw_my :
               rawA_restrict my (worldA_dom (m : WorldAT))
                 (storeA_restrict τ (worldA_dom (m : WorldAT)))).
           {
             change ((resA_restrict my (worldA_dom (m : WorldAT)) : WorldAT)
               (storeA_restrict τ (worldA_dom (m : WorldAT)))).
             rewrite Hrestr_my. exact Hm_proj.
           }
           simpl in Hraw_my.
           destruct Hraw_my as [σy [Hσy Hσy_restrict]].
           exists (@union (gmap K V) _ (τ : gmap K V)
             (storeA_restrict σy ({[y]} : gset K) : gmap K V)).
           split.
           ++ simpl. exists τ, σy. repeat split; eauto.
           ++ apply (storeA_restrict_union_piece_l
                τ (storeA_restrict σy ({[y]} : gset K))
                (worldA_dom (n : WorldAT)) ({[y]} : gset K)).
              ** apply storeA_compat_restrict_singleton_fresh.
                 pose proof (wfworldA_store_dom n τ Hτn) as Hdomτ.
                 change (y ∉ (dom (τ : gmap K V) : gset K)).
                 rewrite Hdomτ. exact Hy_n.
              ** pose proof (wfworldA_store_dom n τ Hτn) as Hdomτ.
                 intros z Hz. change (z ∈ (dom (τ : gmap K V) : gset K)) in Hz.
                 rewrite Hdomτ in Hz. exact Hz.
              ** apply storeA_restrict_dom_subset.
              ** set_solver.
    + unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le.
      apply worldA_ext.
      * simpl. rewrite Hdom_my. set_solver.
      * intros τ. simpl. split.
        -- intros Hτmy.
           assert (Hm_proj :
               (m : WorldAT) (storeA_restrict τ (worldA_dom (m : WorldAT)))).
           {
             eapply resA_restrict_eq_project_store; [exact Hrestr_my | exact Hτmy].
           }
           unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le in Hmn.
           rewrite Hmn in Hm_proj. simpl in Hm_proj.
           destruct Hm_proj as [σn [Hσn Hrestrict]].
           exists (@union (gmap K V) _ (σn : gmap K V)
             (storeA_restrict τ ({[y]} : gset K) : gmap K V)).
           split.
           ++ simpl. exists σn, τ. repeat split; eauto.
              replace (worldA_dom (n : WorldAT) ∩ worldA_dom (m : WorldAT))
                with (worldA_dom (m : WorldAT)) in Hrestrict by set_solver.
              exact Hrestrict.
           ++ pose proof (wfworldA_store_dom n σn Hσn) as Hdomσn.
              pose proof (wfworldA_store_dom my τ Hτmy) as Hdomτ.
              rewrite Hdom_my.
              apply storeA_restrict_union_base_singleton.
              ** intros z Hz. change (z ∈ (dom (σn : gmap K V) : gset K)).
                 rewrite Hdomσn. apply Hdom_m_n. exact Hz.
              ** change ((dom (τ : gmap K V) : gset K) =
                   worldA_dom (m : WorldAT) ∪ {[y]}).
                 rewrite Hdomτ, Hdom_my. reflexivity.
              ** change (y ∉ (dom (σn : gmap K V) : gset K)).
                 rewrite Hdomσn. exact Hy_n.
              ** replace (worldA_dom (n : WorldAT) ∩ worldA_dom (m : WorldAT))
                   with (worldA_dom (m : WorldAT)) in Hrestrict by set_solver.
                 exact Hrestrict.
        -- intros [τny [[σn [σy [Hσn [Hσy [Hagree ->]]]]] Hrestrict]].
           rewrite Hdom_my in Hrestrict.
           replace ((worldA_dom (n : WorldAT) ∪ {[y]}) ∩
             (worldA_dom (m : WorldAT) ∪ {[y]}))
             with (worldA_dom (m : WorldAT) ∪ {[y]}) in Hrestrict by set_solver.
           change (storeA_restrict
             (@union (gmap K V) _ σn (storeA_restrict σy ({[y]} : gset K)))
             (worldA_dom (m : WorldAT) ∪ {[y]}) = τ) in Hrestrict.
           assert (Hglue :
             storeA_restrict
               (@union (gmap K V) _ σn (storeA_restrict σy ({[y]} : gset K)))
               (worldA_dom (m : WorldAT) ∪ {[y]}) = σy).
           {
             apply storeA_restrict_union_base_singleton.
             - pose proof (wfworldA_store_dom n σn Hσn) as Hdomσn.
               intros z Hz. change (z ∈ (dom (σn : gmap K V) : gset K)).
               rewrite Hdomσn. apply Hdom_m_n. exact Hz.
             - pose proof (wfworldA_store_dom my σy Hσy) as Hdomσy.
               change ((dom (σy : gmap K V) : gset K) =
                 worldA_dom (m : WorldAT) ∪ {[y]}).
               rewrite Hdomσy, Hdom_my. reflexivity.
             - pose proof (wfworldA_store_dom n σn Hσn) as Hdomσn.
               change (y ∉ (dom (σn : gmap K V) : gset K)).
               rewrite Hdomσn. exact Hy_n.
             - exact Hagree.
           }
           rewrite Hglue in Hrestrict. subst τ. exact Hσy.
Qed.

End ResourceExtensionA.
