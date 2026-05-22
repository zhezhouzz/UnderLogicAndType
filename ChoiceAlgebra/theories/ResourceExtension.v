From ChoicePrelude Require Import Prelude Store.
From ChoiceAlgebra Require Import ResourceCore ResourceKeyAction ResourceRestrict
  ResourceAlgebra.

(** * Fiber extensions for abstract resources *)

Section ResourceExtensionA.

Context {K : Type} `{Countable K} `{!SwapKey K}.
Context {V : Type} `{ValueSig V}.

Local Notation StoreAT := (@StoreA V K _ _) (only parsing).
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
    extA_rel F (@storeA_restrict V K _ _ σ (extA_in F)) w →
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
        extA_rel F (@storeA_restrict V K _ _ σm (extA_in F)) we ∧
        (we : WorldAT) σe ∧
        σ = @union (gmap K V) _ σm σe.

Notation "m '#>' F '~~A>' n" := (resA_extend_by m F n)
  (at level 70, F at next level, n at next level).

Definition fiber_extensionA_equiv_on (m : WfWorldAT) (F G : fiber_extensionA) : Prop :=
  extA_in F = extA_in G ∧
  ∀ σ wF wG σe,
    (m : WorldAT) σ →
    extA_rel F (@storeA_restrict V K _ _ σ (extA_in F)) wF →
    extA_rel G (@storeA_restrict V K _ _ σ (extA_in G)) wG →
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
      extA_rel F (@storeA_restrict V K _ _ σm (extA_in F)) we ∧
      (we : WorldAT) σe ∧
      σ = @union (gmap K V) _ σm σe.
Proof. intros [_ [_ Hstores]]. exact (Hstores σ). Qed.

Local Lemma extA_projection_dom m F σm :
  extension_applicableA F m →
  (m : WorldAT) σm →
  dom (@storeA_restrict V K _ _ σm (extA_in F)) = extA_in F.
Proof.
  intros Happ Hσm.
  transitivity (worldA_dom (m : WorldAT) ∩ extA_in F).
  - rewrite <- (wfworldA_store_dom m σm Hσm).
    apply storeA_restrict_dom.
  - pose proof (extA_app_in _ _ Happ). set_solver.
Qed.

Local Lemma extA_output_store_dom F σ we σe :
  dom (σ : gmap K V) = extA_in F →
  extA_rel F σ we →
  (we : WorldAT) σe →
  dom (σe : gmap K V) = extA_out F.
Proof.
  intros Hdomσ HF Hσe.
  pose proof (wfworldA_store_dom we σe Hσe) as Hdom_we.
  change (dom (σe : gmap K V) = worldA_dom (we : WorldAT)) in Hdom_we.
  rewrite Hdom_we.
  eapply extA_rel_dom; eauto.
Qed.

Local Lemma extA_output_store_dom_from_base m F σm we σe :
  extension_applicableA F m →
  (m : WorldAT) σm →
  extA_rel F (@storeA_restrict V K _ _ σm (extA_in F)) we →
  (we : WorldAT) σe →
  dom (σe : gmap K V) = extA_out F.
Proof.
  intros Happ Hσm HF Hσe.
  eapply extA_output_store_dom; [| exact HF | exact Hσe].
  eapply extA_projection_dom; eauto.
Qed.

Local Lemma resA_extend_store_compat m F σm we σe :
  extension_applicableA F m →
  (m : WorldAT) σm →
  extA_rel F (@storeA_restrict V K _ _ σm (extA_in F)) we →
  (we : WorldAT) σe →
  @storeA_compat V K _ _ σm σe.
Proof.
  intros Happ Hσm HF Hσe.
  apply storeA_disj_dom_compat.
  change (dom (σm : gmap K V) ∩ dom (σe : gmap K V) = ∅).
  pose proof (wfworldA_store_dom m σm Hσm) as Hdomσm.
  change (dom (σm : gmap K V) = worldA_dom (m : WorldAT)) in Hdomσm.
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
          extA_rel F (@storeA_restrict V K _ _ σm (extA_in F)) we /\
          (we : WorldAT) σe /\
          σ = @union (gmap K V) _ σm σe
    |} _).
    constructor.
    + destruct (worldA_wf m) as [Hne _].
      destruct Hne as [σm Hσm].
      assert (Hproj_dom :
          dom (@storeA_restrict V K _ _ σm (extA_in F)) = extA_in F)
        by (eapply extA_projection_dom; eauto).
      destruct (extA_rel_nonempty F
        (@storeA_restrict V K _ _ σm (extA_in F)) Hproj_dom)
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
        change (dom (σm : gmap K V) = worldA_dom (m : WorldAT)) in Hdomσm.
        rewrite Hdomσm, Hdomσe.
        set_solver.
  - split; [exact Happ |].
    split; [reflexivity |].
    intros σ. reflexivity.
Qed.

Lemma resA_extend_by_unique m F n1 n2 :
  m #> F ~~A> n1 →
  m #> F ~~A> n2 →
  n1 = n2.
Proof.
  intros H1 H2.
  apply wfworldA_ext. apply worldA_ext.
  - rewrite (resA_extend_by_dom _ _ _ H1).
    rewrite (resA_extend_by_dom _ _ _ H2).
    reflexivity.
  - intros σ.
    rewrite (resA_extend_by_store_iff _ _ _ σ H1).
    rewrite (resA_extend_by_store_iff _ _ _ σ H2).
    reflexivity.
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
            (@storeA_restrict V K _ _ σm (extA_in F))).
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
           change (dom (σm : gmap K V) = worldA_dom (m : WorldAT)) in Hdomσm.
           rewrite Hdomσm.
           exact (extA_app_in _ _ (resA_extend_by_applicable _ _ _ Hmy)).
        -- rewrite Hdomσe. set_solver.
        -- eapply (resA_extend_store_compat n F σn we σe).
           ++ exact (resA_extend_by_applicable _ _ _ Hny).
           ++ exact Hσn.
           ++ rewrite Hσn_proj. exact HF.
           ++ exact Hσe.
        -- pose proof (wfworldA_store_dom n σn Hσn) as Hdomσn.
           change (dom (σn : gmap K V) = worldA_dom (n : WorldAT)) in Hdomσn.
           rewrite Hdomσn.
           exact (extA_app_in _ _ (resA_extend_by_applicable _ _ _ Hny)).
        -- rewrite Hdomσe. set_solver.
    + intros [σny [Hσny Hrestrict]].
      apply (proj1 (resA_extend_by_store_iff _ _ _ _ Hny)) in Hσny.
      destruct Hσny as [σn [we [σe [Hσn [HF [Hσe ->]]]]]].
      assert (Hσn_proj :
          (resA_restrict n (extA_in F) : WorldAT)
            (@storeA_restrict V K _ _ σn (extA_in F))).
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
           change (dom (σn : gmap K V) = worldA_dom (n : WorldAT)) in Hdomσn.
           rewrite Hdomσn.
           exact (extA_app_in _ _ (resA_extend_by_applicable _ _ _ Hny)).
        -- rewrite Hdomσe. set_solver.
        -- eapply (resA_extend_store_compat m F σm we σe).
           ++ exact (resA_extend_by_applicable _ _ _ Hmy).
           ++ exact Hσm.
           ++ rewrite Hσm_proj. exact HF.
           ++ exact Hσe.
        -- pose proof (wfworldA_store_dom m σm Hσm) as Hdomσm.
           change (dom (σm : gmap K V) = worldA_dom (m : WorldAT)) in Hdomσm.
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
      change (dom (σm : gmap K V) = worldA_dom (m : WorldAT)) in Hdomσm.
      pose proof (extA_output_store_dom_from_base m F σm we σe
        Happ Hσm HF Hσe) as Hdomσe.
      assert (Hpiece :
          @storeA_restrict V K _ _ (@union (gmap K V) _ σm σe)
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
      change (dom (σ : gmap K V) = worldA_dom (m : WorldAT)) in Hdomσ.
      assert (Hproj_dom :
          dom (@storeA_restrict V K _ _ σ (extA_in F)) = extA_in F)
        by (eapply extA_projection_dom; eauto).
      destruct (extA_rel_nonempty F
        (@storeA_restrict V K _ _ σ (extA_in F)) Hproj_dom)
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
  extA_rel F (@storeA_restrict V K _ _ σm (extA_in F)) we →
  (we : WorldAT) σe →
  @storeA_restrict V K _ _ (@union (gmap K V) _ σm σe)
    (worldA_dom (m : WorldAT)) = σm.
Proof.
  intros Happ Hσm HF Hσe.
  pose proof (resA_extend_store_compat m F σm we σe Happ Hσm HF Hσe)
    as Hcompat.
  pose proof (wfworldA_store_dom m σm Hσm) as Hdomσm.
  change (dom (σm : gmap K V) = worldA_dom (m : WorldAT)) in Hdomσm.
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

Local Lemma resA_extend_store_restrict_other_input m F G σm we σe :
  extension_applicableA F m →
  extension_applicableA G m →
  (m : WorldAT) σm →
  extA_rel F (@storeA_restrict V K _ _ σm (extA_in F)) we →
  (we : WorldAT) σe →
  @storeA_restrict V K _ _ (@union (gmap K V) _ σm σe)
    (extA_in G) =
  @storeA_restrict V K _ _ σm (extA_in G).
Proof.
  intros HappF HappG Hσm HF Hσe.
  apply storeA_restrict_union_ignore_r.
  rewrite (extA_output_store_dom_from_base m F σm we σe
    HappF Hσm HF Hσe).
  pose proof (extA_app_in _ _ HappG).
  pose proof (extA_app_out _ _ HappF).
  set_solver.
Qed.

Lemma resA_extend_by_base_le m n F my ny :
  m ⊑ n →
  m #> F ~~A> my →
  n #> F ~~A> ny →
  my ⊑ ny.
Proof.
  intros Hmn Hmy Hny.
  pose proof (rawA_le_dom m n Hmn) as Hdom_mn.
  pose proof (resA_extend_by_applicable _ _ _ Hmy) as Happ_m.
  pose proof (resA_extend_by_applicable _ _ _ Hny) as Happ_n.
  unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le.
  apply worldA_ext.
  - rewrite (resA_extend_by_dom _ _ _ Hmy).
    simpl. rewrite (resA_extend_by_dom _ _ _ Hny). set_solver.
  - intros σ. split.
    + intros Hσmy.
      apply (proj1 (resA_extend_by_store_iff _ _ _ _ Hmy)) in Hσmy.
      destruct Hσmy as [σm [we [σe [Hσm [HF [Hσe ->]]]]]].
      assert (Hσn_restricted : rawA_restrict n (worldA_dom (m : WorldAT)) σm).
      {
        change ((rawA_restrict n (worldA_dom (m : WorldAT)) : WorldAT) σm).
        rewrite <- Hmn. exact Hσm.
      }
      destruct Hσn_restricted as [σn [Hσn Hrestrict_m]].
      assert (HF_n :
          extA_rel F (@storeA_restrict V K _ _ σn (extA_in F)) we).
      {
        replace (@storeA_restrict V K _ _ σn (extA_in F))
          with (@storeA_restrict V K _ _ σm (extA_in F)); [exact HF |].
        subst σm.
        rewrite storeA_restrict_twice_subset; [reflexivity |].
        exact (extA_app_in _ _ Happ_m).
      }
      exists (@union (gmap K V) _ (σn : gmap K V) (σe : gmap K V)).
      split.
      * apply (proj2 (resA_extend_by_store_iff _ _ _ _ Hny)).
        exists σn, we, σe. repeat split; eauto.
      * assert (Hcompat :
            @storeA_compat V K _ _ σn σe).
        { eapply resA_extend_store_compat; eauto. }
        pose proof (wfworldA_store_dom n σn Hσn) as Hdomσn.
        change (dom (σn : gmap K V) = worldA_dom (n : WorldAT)) in Hdomσn.
        pose proof (extA_output_store_dom_from_base n F σn we σe
          Happ_n Hσn HF_n Hσe) as Hdomσe_out.
        rewrite (resA_extend_by_dom _ _ _ Hmy).
        rewrite (storeA_restrict_union_cover σn σe
          (worldA_dom (m : WorldAT)) (extA_out F)); eauto.
        -- rewrite Hrestrict_m.
           rewrite storeA_restrict_idemp; [reflexivity |].
           rewrite Hdomσe_out. set_solver.
        -- rewrite Hdomσn. exact Hdom_mn.
        -- rewrite Hdomσe_out. set_solver.
    + intros [σny [Hσny Hrestrict]].
      apply (proj1 (resA_extend_by_store_iff _ _ _ _ Hny)) in Hσny.
      destruct Hσny as [σn [we [σe [Hσn [HF [Hσe ->]]]]]].
      assert (Hσm : (m : WorldAT)
          (@storeA_restrict V K _ _ σn (worldA_dom (m : WorldAT)))).
      {
        assert (Hraw : (rawA_restrict n (worldA_dom (m : WorldAT)) : WorldAT)
          (@storeA_restrict V K _ _ σn (worldA_dom (m : WorldAT)))).
        { exists σn. split; [exact Hσn | reflexivity]. }
        rewrite <- Hmn in Hraw. exact Hraw.
      }
      assert (HF_m :
          extA_rel F (@storeA_restrict V K _ _
            (@storeA_restrict V K _ _ σn (worldA_dom (m : WorldAT)))
            (extA_in F)) we).
      {
        rewrite storeA_restrict_twice_subset; [exact HF |].
        exact (extA_app_in _ _ Happ_m).
      }
      apply (proj2 (resA_extend_by_store_iff _ _ _ _ Hmy)).
      exists (@storeA_restrict V K _ _ σn (worldA_dom (m : WorldAT))), we, σe.
      repeat split; eauto.
      assert (Hcompat :
          @storeA_compat V K _ _ σn σe).
      { eapply resA_extend_store_compat; eauto. }
      pose proof (wfworldA_store_dom n σn Hσn) as Hdomσn.
      change (dom (σn : gmap K V) = worldA_dom (n : WorldAT)) in Hdomσn.
      pose proof (extA_output_store_dom_from_base n F σn we σe
        Happ_n Hσn HF Hσe) as Hdomσe_out.
      rewrite (resA_extend_by_dom _ _ _ Hmy) in Hrestrict.
      rewrite (storeA_restrict_union_cover σn σe
        (worldA_dom (m : WorldAT)) (extA_out F)) in Hrestrict; eauto.
      * rewrite (storeA_restrict_idemp σe (extA_out F)) in Hrestrict;
          [symmetry; exact Hrestrict |].
        rewrite Hdomσe_out. set_solver.
      * rewrite Hdomσn. exact Hdom_mn.
      * rewrite Hdomσe_out. set_solver.
Qed.

Lemma fiber_extensionA_functional_outputs_eq m F σ w1 w2 σe1 σe2 :
  extension_applicableA F m →
  fiber_extensionA_functional_on m F →
  (m : WorldAT) σ →
  extA_rel F (@storeA_restrict V K _ _ σ (extA_in F)) w1 →
  extA_rel F (@storeA_restrict V K _ _ σ (extA_in F)) w2 →
  (w1 : WorldAT) σe1 →
  (w2 : WorldAT) σe2 →
  σe1 = σe2.
Proof.
  intros Happ Hfun Hσ Hw1 Hw2 Hσe1 Hσe2.
  assert (Hproj_dom :
      dom (@storeA_restrict V K _ _ σ (extA_in F)) = extA_in F)
    by (eapply extA_projection_dom; eauto).
  pose proof (proj1 (extA_rel_extensional F
    (@storeA_restrict V K _ _ σ (extA_in F)) w1 w2 σe1
    Hproj_dom Hw1 Hw2) Hσe1) as Hσe1_w2.
  eapply Hfun; eauto.
Qed.

Lemma resA_extend_by_output_unique m F G n :
  m #> F ~~A> n →
  m #> G ~~A> n →
  extA_out F = extA_out G.
Proof.
  intros HF HG.
  pose proof (resA_extend_by_dom _ _ _ HF) as HFdom.
  pose proof (resA_extend_by_dom _ _ _ HG) as HGdom.
  pose proof (extA_app_out _ _ (resA_extend_by_applicable _ _ _ HF)) as HFfresh.
  pose proof (extA_app_out _ _ (resA_extend_by_applicable _ _ _ HG)) as HGfresh.
  set_solver.
Qed.

Lemma resA_extend_by_fiber_equiv_on m F G n :
  extA_in F = extA_in G →
  m #> F ~~A> n →
  m #> G ~~A> n →
  fiber_extensionA_equiv_on m F G.
Proof.
  intros Hin HF HG. split; [exact Hin |].
  assert (Hdir :
    forall A B,
      extA_in A = extA_in B ->
      m #> A ~~A> n ->
      m #> B ~~A> n ->
      forall σ wA wB σe,
        (m : WorldAT) σ ->
        extA_rel A (@storeA_restrict V K _ _ σ (extA_in A)) wA ->
        extA_rel B (@storeA_restrict V K _ _ σ (extA_in B)) wB ->
        (wA : WorldAT) σe ->
        (wB : WorldAT) σe).
  {
    intros A B HAB HA HB σ wA wB σe Hσ HArel HBrel HAe.
    pose proof (resA_extend_by_applicable _ _ _ HA) as HAppA.
    pose proof (resA_extend_by_applicable _ _ _ HB) as HAppB.
    pose proof (resA_extend_store_compat m A σ wA σe HAppA Hσ HArel HAe)
      as HcompatA.
    assert (Hn : (n : WorldAT) (@union (gmap K V) _ σ σe)).
    {
      apply (proj2 (resA_extend_by_store_iff m A n
        (@union (gmap K V) _ σ σe) HA)).
      exists σ, wA, σe. repeat split; eauto.
    }
    apply (proj1 (resA_extend_by_store_iff m B n
      (@union (gmap K V) _ σ σe) HB)) in Hn.
    destruct Hn as [σB [wBe [σBe [HσB [HBwe [HBe Heq]]]]]].
    pose proof (resA_extend_store_compat m B σB wBe σBe HAppB HσB HBwe HBe)
      as HcompatB.
    assert (Hdomσ : dom (σ : gmap K V) = worldA_dom (m : WorldAT)).
    { exact (wfworldA_store_dom m σ Hσ). }
    assert (HdomσB : dom (σB : gmap K V) = worldA_dom (m : WorldAT)).
    { exact (wfworldA_store_dom m σB HσB). }
    assert (HprojA :
        dom (@storeA_restrict V K _ _ σ (extA_in A)) = extA_in A)
      by (eapply extA_projection_dom; eauto).
    assert (HprojB :
        dom (@storeA_restrict V K _ _ σB (extA_in B)) = extA_in B)
      by (eapply extA_projection_dom; eauto).
    assert (Hdomσe : dom (σe : gmap K V) = extA_out A).
    {
      pose proof (wfworldA_store_dom wA σe HAe) as Hdom_wA.
      change (dom (σe : gmap K V) = worldA_dom (wA : WorldAT)) in Hdom_wA.
      rewrite Hdom_wA. eapply extA_rel_dom; eauto.
    }
    assert (HdomσBe : dom (σBe : gmap K V) = extA_out B).
    {
      pose proof (wfworldA_store_dom wBe σBe HBe) as Hdom_wBe.
      change (dom (σBe : gmap K V) = worldA_dom (wBe : WorldAT)) in Hdom_wBe.
      rewrite Hdom_wBe. eapply extA_rel_dom; eauto.
    }
    pose proof (resA_extend_by_output_unique m A B n HA HB) as Hout.
    assert (HbaseA :
        @storeA_restrict V K _ _ (@union (gmap K V) _ σ σe)
          (worldA_dom (m : WorldAT)) = σ).
    {
      apply (storeA_restrict_union_piece_l σ σe
        (worldA_dom (m : WorldAT)) (extA_out A)); eauto.
      - change (dom (σ : gmap K V) ⊆ worldA_dom (m : WorldAT)).
        rewrite Hdomσ. reflexivity.
      - change (dom (σe : gmap K V) ⊆ extA_out A).
        rewrite Hdomσe. reflexivity.
      - pose proof (extA_app_out _ _ HAppA). set_solver.
    }
    assert (HbaseB :
        @storeA_restrict V K _ _ (@union (gmap K V) _ σB σBe)
          (worldA_dom (m : WorldAT)) = σB).
    {
      apply (storeA_restrict_union_piece_l σB σBe
        (worldA_dom (m : WorldAT)) (extA_out B)); eauto.
      - change (dom (σB : gmap K V) ⊆ worldA_dom (m : WorldAT)).
        rewrite HdomσB. reflexivity.
      - change (dom (σBe : gmap K V) ⊆ extA_out B).
        rewrite HdomσBe. reflexivity.
      - pose proof (extA_app_out _ _ HAppB). set_solver.
    }
    assert (HσB_eq : σB = σ).
    {
      rewrite <- Heq in HbaseB.
      rewrite HbaseA in HbaseB. symmetry. exact HbaseB.
    }
    subst σB.
    assert (HextraA :
        @storeA_restrict V K _ _ (@union (gmap K V) _ σ σe) (extA_out A) = σe).
    {
      apply (storeA_restrict_union_piece_r σ σe
        (worldA_dom (m : WorldAT)) (extA_out A)); eauto.
      - change (dom (σ : gmap K V) ⊆ worldA_dom (m : WorldAT)).
        rewrite Hdomσ. reflexivity.
      - change (dom (σe : gmap K V) ⊆ extA_out A).
        rewrite Hdomσe. reflexivity.
      - pose proof (extA_app_out _ _ HAppA). set_solver.
    }
    assert (HextraB :
        @storeA_restrict V K _ _ (@union (gmap K V) _ σ σBe) (extA_out B) = σBe).
    {
      apply (storeA_restrict_union_piece_r σ σBe
        (worldA_dom (m : WorldAT)) (extA_out B)); eauto.
      - change (dom (σ : gmap K V) ⊆ worldA_dom (m : WorldAT)).
        rewrite Hdomσ. reflexivity.
      - change (dom (σBe : gmap K V) ⊆ extA_out B).
        rewrite HdomσBe. reflexivity.
      - pose proof (extA_app_out _ _ HAppB). set_solver.
    }
    assert (HσBe_eq : σBe = σe).
    {
      rewrite <- Heq in HextraB.
      rewrite <- Hout in HextraB.
      rewrite HextraA in HextraB. symmetry. exact HextraB.
    }
    subst σBe.
    replace (@storeA_restrict V K _ _ σ (extA_in A))
      with (@storeA_restrict V K _ _ σ (extA_in B)) in HBwe
      by (rewrite HAB; reflexivity).
    replace (@storeA_restrict V K _ _ σ (extA_in A))
      with (@storeA_restrict V K _ _ σ (extA_in B)) in HBrel
      by (rewrite HAB; reflexivity).
    apply (proj1 (extA_rel_extensional B
      (@storeA_restrict V K _ _ σ (extA_in B)) wBe wB σe
      HprojB HBwe HBrel)).
    exact HBe.
  }
  intros σ wF wG σe Hσ HFrel HGrel. split.
  - eapply Hdir; eauto.
  - intros HGe.
    eapply Hdir with (A := G) (B := F) (σ := σ) (wA := wG) (wB := wF); eauto;
      symmetry; exact Hin.
Qed.

Lemma resA_extend_by_commute m F G mF mG mFG mGF :
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
      pose proof (resA_extend_store_compat m F σm wF σfe
        HAppF_m Hmσ HFrel HFstore) as HcompatF.
      pose proof (extA_output_store_dom_from_base m F σm wF σfe
        HAppF_m Hmσ HFrel HFstore) as Hdomσfe.
      assert (HprojG :
          @storeA_restrict V K _ _ (@union (gmap K V) _ σm σfe) (extA_in G) =
          @storeA_restrict V K _ _ σm (extA_in G)).
      {
        exact (resA_extend_store_restrict_other_input m F G σm wF σfe
          HAppF_m HAppG_m Hmσ HFrel HFstore).
      }
      rewrite HprojG in HGrel.
      pose proof (resA_extend_store_compat m G σm wG σge
        HAppG_m Hmσ HGrel HGstore) as HcompatG.
      pose proof (extA_output_store_dom_from_base m G σm wG σge
        HAppG_m Hmσ HGrel HGstore) as Hdomσge.
      exists (@union (gmap K V) _ (σm : gmap K V) (σge : gmap K V)), wF, σfe.
      split.
      * apply (proj2 (resA_extend_by_store_iff _ _ _ _ HG)).
        exists σm, wG, σge. repeat split; eauto.
      * split.
        -- assert (HprojF :
             @storeA_restrict V K _ _
               (@union (gmap K V) _ σm σge) (extA_in F) =
             @storeA_restrict V K _ _ σm (extA_in F)).
           {
             exact (resA_extend_store_restrict_other_input m G F σm wG σge
               HAppG_m HAppF_m Hmσ HGrel HGstore).
           }
           rewrite HprojF. exact HFrel.
        -- split; [exact HFstore |].
           assert (Hcompat_extra : @storeA_compat V K _ _ σfe σge).
           {
             apply storeA_disj_dom_compat.
             change (dom (σfe : gmap K V) ∩ dom (σge : gmap K V) = ∅).
             rewrite Hdomσfe, Hdomσge. set_solver.
           }
           apply storeA_union_swap_right. exact Hcompat_extra.
    + intros Hσ.
      apply (proj2 (resA_extend_by_store_iff _ _ _ _ HFG)).
      apply (proj1 (resA_extend_by_store_iff _ _ _ _ HGF)) in Hσ.
      destruct Hσ as [σmG [wF [σfe [HmGσ [HFrel [HFstore ->]]]]]].
      apply (proj1 (resA_extend_by_store_iff _ _ _ _ HG)) in HmGσ.
      destruct HmGσ as [σm [wG [σge [Hmσ [HGrel [HGstore ->]]]]]].
      pose proof (resA_extend_store_compat m G σm wG σge
        HAppG_m Hmσ HGrel HGstore) as HcompatG.
      pose proof (extA_output_store_dom_from_base m G σm wG σge
        HAppG_m Hmσ HGrel HGstore) as Hdomσge.
      assert (HprojF :
          @storeA_restrict V K _ _ (@union (gmap K V) _ σm σge) (extA_in F) =
          @storeA_restrict V K _ _ σm (extA_in F)).
      {
        exact (resA_extend_store_restrict_other_input m G F σm wG σge
          HAppG_m HAppF_m Hmσ HGrel HGstore).
      }
      rewrite HprojF in HFrel.
      pose proof (resA_extend_store_compat m F σm wF σfe
        HAppF_m Hmσ HFrel HFstore) as HcompatF.
      pose proof (extA_output_store_dom_from_base m F σm wF σfe
        HAppF_m Hmσ HFrel HFstore) as Hdomσfe.
      exists (@union (gmap K V) _ (σm : gmap K V) (σfe : gmap K V)), wG, σge.
      split.
      * apply (proj2 (resA_extend_by_store_iff _ _ _ _ HF)).
        exists σm, wF, σfe. repeat split; eauto.
      * split.
        -- assert (HprojG :
             @storeA_restrict V K _ _
               (@union (gmap K V) _ σm σfe) (extA_in G) =
             @storeA_restrict V K _ _ σm (extA_in G)).
           {
             exact (resA_extend_store_restrict_other_input m F G σm wF σfe
               HAppF_m HAppG_m Hmσ HFrel HFstore).
           }
           rewrite HprojG. exact HGrel.
        -- split; [exact HGstore |].
           assert (Hcompat_extra : @storeA_compat V K _ _ σge σfe).
           {
             apply storeA_disj_dom_compat.
             change (dom (σge : gmap K V) ∩ dom (σfe : gmap K V) = ∅).
             rewrite Hdomσge, Hdomσfe. set_solver.
           }
           apply storeA_union_swap_right. exact Hcompat_extra.
Qed.

End ResourceExtensionA.
