From ContextPrelude Require Import Prelude Store.
From ContextAlgebra Require Import ResourceCore ResourceKeyAction.

(** * Restriction and fibers for abstract resources *)

Section ResourceRestrictA.

Context {K : Type} `{Countable K} `{!SwapKey K}.
Context {V : Type} `{ValueSig V}.

Local Notation StoreAT := (@StoreA V K _ _) (only parsing).
Local Notation WorldAT := (@WorldA K _ _ V) (only parsing).
Local Notation WfWorldAT := (@WfWorldA K _ _ V) (only parsing).

Definition rawA_restrict (m : WorldAT) (X : gset K) : WorldAT := {|
  worldA_dom    := worldA_dom m ∩ X;
  worldA_stores := λ σ, ∃ σ0 : StoreAT,
    m σ0 ∧ @storeA_restrict V K _ _ σ0 X = σ;
|}.

Definition resA_restrict (w : WfWorldAT) (X : gset K) : WfWorldAT.
Proof.
  refine (exist _ (rawA_restrict w X) _).
  destruct (worldA_wf w) as [Hne Hdom].
  split.
  - destruct Hne as [σ Hσ].
    exists (@storeA_restrict V K _ _ σ X). exists σ. split; [exact Hσ | reflexivity].
  - intros σ [σ0 [Hσ0 Hrestrict]]. subst σ.
    rewrite storeA_restrict_dom.
    rewrite (Hdom σ0 Hσ0). reflexivity.
Defined.

Lemma wfworldA_store_restrict_dom (w : WfWorldAT) (σ : StoreAT) (X : gset K) :
  w σ → dom (@storeA_restrict V K _ _ σ X) = worldA_dom (w : WorldAT) ∩ X.
Proof.
  intros Hσ. rewrite storeA_restrict_dom.
  rewrite (wfworldA_store_dom w σ Hσ). reflexivity.
Qed.

Lemma resA_restrict_lift_store
    (w : WfWorldAT) (X : gset K) (σ : StoreAT) :
  (resA_restrict w X : WorldAT) σ →
  ∃ σw, (w : WorldAT) σw ∧ @storeA_restrict V K _ _ σw X = σ.
Proof.
  intros Hσ. exact Hσ.
Qed.

Lemma resA_restrict_eq_lift_store
    (w wX : WfWorldAT) (X : gset K) (σ : StoreAT) :
  resA_restrict w X = wX →
  (wX : WorldAT) σ →
  ∃ σw, (w : WorldAT) σw ∧ @storeA_restrict V K _ _ σw X = σ.
Proof.
  intros <- Hσ. exact Hσ.
Qed.

Definition rawA_fiber (m : WorldAT) (σ : StoreAT) : WorldAT := {|
  worldA_dom    := worldA_dom m;
  worldA_stores := λ σ0, m σ0 ∧ @storeA_restrict V K _ _ σ0 (dom σ) = σ;
|}.

Lemma rawA_fiber_commute (m : WorldAT) (σ1 σ2 : StoreAT) :
  rawA_fiber (rawA_fiber m σ1) σ2 =
  rawA_fiber (rawA_fiber m σ2) σ1.
Proof.
  apply worldA_ext; [reflexivity |].
  intros σ. simpl. tauto.
Qed.

Definition resA_fiber (w : WfWorldAT) (σ : StoreAT)
    (Hne : ∃ σ0, (w : WorldAT) σ0 ∧ @storeA_restrict V K _ _ σ0 (dom σ) = σ)
    : WfWorldAT.
Proof.
  refine (exist _ (rawA_fiber w σ) _).
  destruct (worldA_wf w) as [_ Hdom].
  split.
  - destruct Hne as [σ0 [Hσ0 Hrestrict]].
    exists σ0. split; [exact Hσ0 | exact Hrestrict].
  - intros σ0 [Hσ0 _]. exact (Hdom σ0 Hσ0).
Defined.

Definition resA_fiber_from_projection
    (w : WfWorldAT) (X : gset K) (σ : StoreAT) (wfib : WfWorldAT) : Prop :=
  (resA_restrict w X : WorldAT) σ ∧
  (wfib : WorldAT) = rawA_fiber w σ.

Definition resA_fiber_member (w : WfWorldAT) (X : gset K) (wfib : WfWorldAT) : Prop :=
  ∃ σ, resA_fiber_from_projection w X σ wfib.

Lemma resA_fiber_commute (w : WfWorldAT) (σ1 σ2 : StoreAT)
    H1 H2 H1' H2' :
  resA_fiber (resA_fiber w σ1 H1) σ2 H2 =
  resA_fiber (resA_fiber w σ2 H1') σ1 H2'.
Proof.
  apply wfworldA_ext. apply rawA_fiber_commute.
Qed.

Lemma resA_fiber_from_projection_member
    (w wfib : WfWorldAT) (X : gset K) (σ σw : StoreAT) :
  resA_fiber_from_projection w X σ wfib →
  (w : WorldAT) σw →
  @storeA_restrict V K _ _ σw X = σ →
  (wfib : WorldAT) σw.
Proof.
  intros [Hproj Heq] Hσw Hrestrict.
  rewrite Heq. simpl. split; [exact Hσw |].
  rewrite <- Hrestrict.
  rewrite <- (storeA_restrict_idemp
    (@storeA_restrict V K _ _ σw X)
    (dom (@storeA_restrict V K _ _ σw X))) at 2 by set_solver.
  rewrite storeA_restrict_restrict.
  replace (X ∩ dom (@storeA_restrict V K _ _ σw X))
    with (dom (@storeA_restrict V K _ _ σw X)).
  - reflexivity.
  - rewrite storeA_restrict_dom. set_solver.
Qed.

Lemma resA_projection_from_fiber_projection
    (w wfib : WfWorldAT) (X Y : gset K) (σX σY : StoreAT) :
  resA_fiber_from_projection w X σX wfib →
  (resA_restrict wfib Y : WorldAT) σY →
  (resA_restrict w Y : WorldAT) σY.
Proof.
  intros [_ Heq] HprojY.
  destruct HprojY as [s [Hfib HrestrictY]].
  rewrite Heq in Hfib. destruct Hfib as [Hs _].
  exists s. split; [exact Hs | exact HrestrictY].
Qed.

Lemma resA_projection_into_other_fiber
    (w wfibX wfibY : WfWorldAT) (X Y : gset K) (σX σY : StoreAT) :
  resA_fiber_from_projection w X σX wfibX →
  resA_fiber_from_projection w Y σY wfibY →
  (resA_restrict wfibX Y : WorldAT) σY →
  (resA_restrict wfibY (dom σX) : WorldAT) σX.
Proof.
  intros [_ HeqX] [_ HeqY] HprojY.
  destruct HprojY as [s [HfibX HrestrictY]].
  rewrite HeqX in HfibX.
  destruct HfibX as [Hs HrestrictX].
  exists s. split.
  - rewrite HeqY. simpl. split; [exact Hs |].
    assert (Hrestrict_dom :
      @storeA_restrict V K _ _ s (dom σY) =
      @storeA_restrict V K _ _ s Y).
    {
      rewrite <- (storeA_restrict_idemp
        (@storeA_restrict V K _ _ s Y) (dom σY)).
      - rewrite storeA_restrict_restrict.
        replace (Y ∩ dom σY) with (dom σY) by
          (rewrite <- HrestrictY; rewrite storeA_restrict_dom; set_solver).
        reflexivity.
      - rewrite HrestrictY. set_solver.
    }
    rewrite Hrestrict_dom. exact HrestrictY.
  - exact HrestrictX.
Qed.

Lemma resA_restrict_rekey
    (f : K → K) (Hf : Inj (=) (=) f) (w : WfWorldAT) (X : gset K) :
  resA_restrict (resA_rekey f Hf w) (set_map f X) =
  resA_rekey f Hf (resA_restrict w X).
Proof.
  apply wfworldA_ext. apply worldA_ext.
  - simpl. apply set_eq. intros z. rewrite elem_of_intersection. split.
    + intros [HzD HzX].
      apply elem_of_map in HzD as [u [-> HuD]].
      apply elem_of_map in HzX as [v [Hv HuX]].
      apply Hf in Hv. subst v.
      apply elem_of_map. exists u. split; [reflexivity | set_solver].
    + intros [u [-> Hu]]%elem_of_map.
      apply elem_of_intersection in Hu as [HuD HuX].
      split; apply elem_of_map; eexists; split; eauto.
  - intros σ. simpl. split.
    + intros [σr [[σw [Hσw Hrekey]] Hrestrict]].
      exists (@storeA_restrict V K _ _ σw X). split.
      * exists σw. split; [exact Hσw | reflexivity].
      * rewrite <- Hrestrict, <- Hrekey.
        symmetry. apply storeA_restrict_rekey. exact Hf.
    + intros [σx [[σw [Hσw Hrestrict]] Hrekey]].
      exists (@storeA_rekey V K _ _ f σw). split.
      * exists σw. split; [exact Hσw | reflexivity].
      * rewrite <- Hrekey, <- Hrestrict.
        apply storeA_restrict_rekey. exact Hf.
Qed.

Lemma resA_restrict_swap (x y : K) (w : WfWorldAT) (X : gset K) :
  resA_restrict (resA_swap x y w) (gset_swap x y X) =
  resA_swap x y (resA_restrict w X).
Proof.
  apply resA_restrict_rekey.
Qed.

Lemma resA_restrict_swap_projection x y (w : WfWorldAT) (X : gset K) (σ : StoreAT) :
  (resA_restrict w X : WorldAT) σ →
  (resA_restrict (resA_swap x y w) (gset_swap x y X) : WorldAT)
    (@storeA_swap V K _ _ _ x y σ).
Proof.
  intros Hproj.
  change ((resA_restrict (resA_swap x y w) (gset_swap x y X) : WorldAT)
    (@storeA_swap V K _ _ _ x y σ)).
  rewrite resA_restrict_swap. simpl.
  exists σ. split; [exact Hproj | reflexivity].
Qed.

Lemma resA_swap_extension_dom (x y : K) (m my : WfWorldAT) (z : K) :
  worldA_dom (my : WorldAT) = worldA_dom (m : WorldAT) ∪ {[z]} →
  worldA_dom (resA_swap x y my : WorldAT) =
  worldA_dom (resA_swap x y m : WorldAT) ∪ {[key_swap x y z]}.
Proof.
  intros Hdom. simpl.
  change (gset_swap x y (worldA_dom (my : WorldAT)) =
    gset_swap x y (worldA_dom (m : WorldAT)) ∪ {[key_swap x y z]}).
  rewrite Hdom, gset_swap_union, gset_swap_singleton.
  reflexivity.
Qed.

Lemma resA_swap_extension_dom_cancel
    (x y : K) (m my : WfWorldAT) (z : K) :
  worldA_dom (my : WorldAT) = worldA_dom (resA_swap x y m : WorldAT) ∪ {[z]} →
  worldA_dom (resA_swap x y my : WorldAT) =
  worldA_dom (m : WorldAT) ∪ {[key_swap x y z]}.
Proof.
  intros Hdom. simpl in Hdom |- *.
  change (worldA_dom (my : WorldAT) =
    gset_swap x y (worldA_dom (m : WorldAT)) ∪ {[z]}) in Hdom.
  change (gset_swap x y (worldA_dom (my : WorldAT)) =
    worldA_dom (m : WorldAT) ∪ {[key_swap x y z]}).
  rewrite Hdom, gset_swap_union, gset_swap_involutive, gset_swap_singleton.
  reflexivity.
Qed.

Lemma resA_swap_restrict_extension
    (x y : K) (m my : WfWorldAT) :
  resA_restrict my (worldA_dom (m : WorldAT)) = m →
  resA_restrict (resA_swap x y my) (worldA_dom (resA_swap x y m : WorldAT)) =
  resA_swap x y m.
Proof.
  intros Hrestr.
  change (resA_restrict (resA_swap x y my)
    (gset_swap x y (worldA_dom (m : WorldAT))) = resA_swap x y m).
  rewrite resA_restrict_swap, Hrestr. reflexivity.
Qed.

Lemma resA_swap_restrict_extension_cancel
    (x y : K) (m my : WfWorldAT) :
  resA_restrict my (worldA_dom (resA_swap x y m : WorldAT)) = resA_swap x y m →
  resA_restrict (resA_swap x y my) (worldA_dom (m : WorldAT)) = m.
Proof.
  intros Hrestr.
  change (resA_restrict my (gset_swap x y (worldA_dom (m : WorldAT))) =
    resA_swap x y m) in Hrestr.
  rewrite <- (gset_swap_involutive x y (worldA_dom (m : WorldAT))).
  rewrite resA_restrict_swap, Hrestr, resA_swap_involutive. reflexivity.
Qed.

Lemma resA_restrict_restrict_eq (w : WfWorldAT) (X Y : gset K) :
  resA_restrict (resA_restrict w X) Y =
  resA_restrict w (X ∩ Y).
Proof.
  apply wfworldA_ext. apply worldA_ext.
  - simpl. set_solver.
  - intros σ. simpl. split.
    + intros [σx [[σw [Hσw Hx]] Hy]]. subst σx σ.
      exists σw. split; [exact Hσw |].
      rewrite storeA_restrict_restrict. reflexivity.
    + intros [σw [Hσw Hxy]]. subst σ.
      exists (@storeA_restrict V K _ _ σw X). split.
      * exists σw. split; [exact Hσw | reflexivity].
      * rewrite storeA_restrict_restrict. reflexivity.
Qed.

Lemma resA_restrict_self (w : WfWorldAT) :
  resA_restrict w (worldA_dom (w : WorldAT)) = w.
Proof.
  apply wfworldA_ext. apply worldA_ext.
  - simpl. set_solver.
  - intros σ. simpl. split.
    + intros [σw [Hσw Hrestrict]]. subst σ.
      rewrite storeA_restrict_idemp; [exact Hσw |].
      pose proof (wfworldA_store_dom w σw Hσw) as Hdom.
      change (dom (σw : gmap K V) = worldA_dom (w : WorldAT)) in Hdom.
      rewrite Hdom. set_solver.
    + intros Hσ.
      exists σ. split; [exact Hσ |].
      apply storeA_restrict_idemp.
      pose proof (wfworldA_store_dom w σ Hσ) as Hdom.
      change (dom (σ : gmap K V) = worldA_dom (w : WorldAT)) in Hdom.
      rewrite Hdom. set_solver.
Qed.

Lemma resA_fiber_swap (x y : K) (w : WfWorldAT) (σ : StoreAT)
    (Hne : ∃ σ0, (w : WorldAT) σ0 ∧
      @storeA_restrict V K _ _ σ0 (dom σ) = σ)
    (Hne' : ∃ σ0, (resA_swap x y w : WorldAT) σ0 ∧
      @storeA_restrict V K _ _ σ0 (dom (@storeA_swap V K _ _ _ x y σ)) =
        @storeA_swap V K _ _ _ x y σ) :
  resA_swap x y (resA_fiber w σ Hne) =
  resA_fiber (resA_swap x y w) (@storeA_swap V K _ _ _ x y σ) Hne'.
Proof.
  apply wfworldA_ext. apply worldA_ext.
  - simpl. reflexivity.
  - intros τ. simpl. split.
    + intros [τ0 [[Hτ0 Hrestr] Hswap]].
      rewrite <- Hswap.
      split.
      * exists τ0. split; [exact Hτ0 | reflexivity].
      * change (@storeA_restrict V K _ _
          (@storeA_swap V K _ _ _ x y τ0)
          (dom (@storeA_swap V K _ _ _ x y σ)) =
          @storeA_swap V K _ _ _ x y σ).
        rewrite (storeA_swap_dom x y σ), storeA_restrict_swap. f_equal.
        exact Hrestr.
    + intros [[τ0 [Hτ0 Hswap]] Hrestr].
      rewrite <- Hswap in Hrestr |- *.
      exists τ0. split.
      * split; [exact Hτ0 |].
        change (@storeA_restrict V K _ _
          (@storeA_swap V K _ _ _ x y τ0)
          (dom (@storeA_swap V K _ _ _ x y σ)) =
          @storeA_swap V K _ _ _ x y σ) in Hrestr.
        rewrite storeA_swap_dom, storeA_restrict_swap in Hrestr.
        apply (f_equal (@storeA_swap V K _ _ _ x y)) in Hrestr.
        rewrite !storeA_swap_involutive in Hrestr. exact Hrestr.
      * reflexivity.
Qed.

Lemma resA_fiber_from_projection_swap x y (w wfib wfib' : WfWorldAT)
    (X : gset K) (σ : StoreAT) :
  resA_fiber_from_projection w X σ wfib →
  resA_fiber_from_projection (resA_swap x y w) (gset_swap x y X)
    (@storeA_swap V K _ _ _ x y σ) wfib' →
  resA_swap x y wfib = wfib'.
Proof.
  intros [Hproj Heq] [Hproj' Heq'].
  apply wfworldA_ext.
  change (rawA_swap x y (wfib : WorldAT) = (wfib' : WorldAT)).
  rewrite Heq, Heq'. apply worldA_ext.
  - simpl. reflexivity.
  - intros τ. simpl. split.
    + intros [τ0 [[Hτ0 Hrestr] Hswap]].
      rewrite <- Hswap.
      split.
      * exists τ0. split; [exact Hτ0 | reflexivity].
      * change (@storeA_restrict V K _ _
          (@storeA_swap V K _ _ _ x y τ0)
          (dom (@storeA_swap V K _ _ _ x y σ)) =
          @storeA_swap V K _ _ _ x y σ).
        rewrite (storeA_swap_dom x y σ), storeA_restrict_swap. f_equal.
        exact Hrestr.
    + intros [[τ0 [Hτ0 Hswap]] Hrestr].
      rewrite <- Hswap in Hrestr |- *.
      exists τ0. split.
      * split; [exact Hτ0 |].
        change (@storeA_restrict V K _ _
          (@storeA_swap V K _ _ _ x y τ0)
          (dom (@storeA_swap V K _ _ _ x y σ)) =
          @storeA_swap V K _ _ _ x y σ) in Hrestr.
        rewrite storeA_swap_dom, storeA_restrict_swap in Hrestr.
        apply (f_equal (@storeA_swap V K _ _ _ x y)) in Hrestr.
        rewrite !storeA_swap_involutive in Hrestr. exact Hrestr.
      * reflexivity.
Qed.

Context `{!ShiftKey K}.

Lemma resA_restrict_shift (k : nat) (w : WfWorldAT) (X : gset K) :
  resA_restrict (resA_shift k w) (set_map (key_shift k) X) =
  resA_shift k (resA_restrict w X).
Proof.
  apply resA_restrict_rekey.
Qed.

End ResourceRestrictA.

Section ResourceOpenRestrictA.

Context {V : Type} `{ValueSig V}.

Lemma resA_restrict_open (k : nat) (x : atom)
    (w : @WfWorldA logic_var _ _ V) (X : gset logic_var) :
  resA_restrict (resA_open k x w) (gset_swap (LVBound k) (LVFree x) X) =
  resA_open k x (resA_restrict w X).
Proof.
  apply resA_restrict_swap.
Qed.

End ResourceOpenRestrictA.
