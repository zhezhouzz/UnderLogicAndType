From ContextBase Require Import Prelude LogicVarInterface.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceCore ResourceKeyAction ResourceRestrict
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

Lemma extA_projection_dom m F σm :
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

Lemma extA_output_store_dom F σ we σe :
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

Lemma extA_output_store_dom_from_base m F σm we σe :
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

Lemma resA_extend_store_compat m F σm we σe :
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
      replace σm with (@storeA_restrict V K _ _
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

End ResourceExtensionA.
