From CoreLang Require Import BasicTyping LocallyNamelessProps LocallyNamelessExtra.
From ContextBase Require Import BaseTactics.
From ContextStore Require Import StoreCore.

(** * Basic typing facts for CoreLang

    These mirror the basic typing facts in HATs/UnderType, specialized to the
    direct-style CoreLang syntax. *)

Lemma basic_typing_contains_fv_mut :
  (∀ Γ v T, Γ ⊢ᵥ v ⋮ T → fv_value v ⊆ dom Γ) ∧
  (∀ Γ e T, Γ ⊢ₑ e ⋮ T → fv_tm e ⊆ dom Γ).
Proof.
  apply has_type_mutind with
      (P := fun Γ v T _ => fv_value v ⊆ dom Γ)
      (P0 := fun Γ e T _ => fv_tm e ⊆ dom Γ);
      simpl; try set_solver.
  - intros Γ x T Hlookup.
    apply elem_of_dom_2 in Hlookup. set_solver.
  - intros Γ s T e L Hty IH.
    pose (x := fresh_for (L ∪ fv_tm e)).
    assert (Hx : x ∉ L ∪ fv_tm e) by (subst x; apply fresh_for_not_in).
    specialize (IH x ltac:(set_solver)).
    pose proof (open_fv_tm' e (vfvar x) 0) as Hopen.
    rewrite dom_insert in IH. set_solver.
  - intros Γ sx T vf L Hty IH.
    pose (x := fresh_for (L ∪ fv_value vf)).
    assert (Hx : x ∉ L ∪ fv_value vf) by (subst x; apply fresh_for_not_in).
    specialize (IH x ltac:(set_solver)).
    pose proof (open_fv_value' vf (vfvar x) 0) as Hopen.
    rewrite dom_insert in IH. set_solver.
  - intros Γ T1 T2 e1 e2 L Hty1 IH1 Hty2 IH2.
    pose (x := fresh_for (L ∪ fv_tm e2)).
    assert (Hx : x ∉ L ∪ fv_tm e2) by (subst x; apply fresh_for_not_in).
    specialize (IH2 x ltac:(set_solver)).
    rewrite dom_insert in IH2.
    pose proof (open_fv_tm' e2 (vfvar x) 0) as Hopen.
    set_solver.
  - intros Γ v T eleaf enode L Htyv IHv Hleaf IHleaf Hnode IHnode.
    pose (root := fresh_for (L ∪ fv_tm enode)).
    assert (Hroot : root ∉ L ∪ fv_tm enode)
      by (subst root; apply fresh_for_not_in).
    pose (left := fresh_for (L ∪ fv_tm enode ∪ {[root]})).
    assert (Hleft : left ∉ L ∪ fv_tm enode ∪ {[root]})
      by (subst left; apply fresh_for_not_in).
    pose (right := fresh_for (L ∪ fv_tm enode ∪ {[root]} ∪ {[left]})).
    assert (Hright : right ∉ L ∪ fv_tm enode ∪ {[root]} ∪ {[left]})
      by (subst right; apply fresh_for_not_in).
    specialize (IHnode root left right ltac:(set_solver) ltac:(set_solver) ltac:(set_solver)).
    rewrite !dom_insert in IHnode.
    unfold open_tree_node_branch, open_tree_node_branch_value in IHnode.
    pose proof (open_fv_tm' enode (vfvar root) 0) as Hopen_root.
    pose proof (open_fv_tm'
      (open_tm 0 (vfvar root) enode) (vfvar left) 1) as Hopen_left.
    pose proof (open_fv_tm'
      (open_tm 1 (vfvar left) (open_tm 0 (vfvar root) enode))
      (vfvar right) 2) as Hopen_right.
    simpl in Hopen_root, Hopen_left, Hopen_right.
    set_solver.
  - intros Γ v T enil econs L Htyv IHv Hnil IHnil Hcons IHcons.
    pose (hd := fresh_for (L ∪ fv_tm econs)).
    assert (Hhd : hd ∉ L ∪ fv_tm econs)
      by (subst hd; apply fresh_for_not_in).
    pose (tl := fresh_for (L ∪ fv_tm econs ∪ {[hd]})).
    assert (Htl : tl ∉ L ∪ fv_tm econs ∪ {[hd]})
      by (subst tl; apply fresh_for_not_in).
    specialize (IHcons hd tl ltac:(set_solver) ltac:(set_solver)).
    rewrite !dom_insert in IHcons.
    unfold open_list_cons_branch, open_list_cons_branch_value in IHcons.
    pose proof (open_fv_tm' econs (vfvar hd) 0) as Hopen_hd.
    pose proof (open_fv_tm'
      (open_tm 0 (vfvar hd) econs) (vfvar tl) 1) as Hopen_tl.
    simpl in Hopen_hd, Hopen_tl.
    set_solver.
Qed.

Lemma basic_typing_contains_fv_value Γ v T :
  Γ ⊢ᵥ v ⋮ T → fv_value v ⊆ dom Γ.
Proof. exact (proj1 basic_typing_contains_fv_mut Γ v T). Qed.

Lemma basic_typing_contains_fv_tm Γ e T :
  Γ ⊢ₑ e ⋮ T → fv_tm e ⊆ dom Γ.
Proof. exact (proj2 basic_typing_contains_fv_mut Γ e T). Qed.

Class FvSubsetGamma (E : Type) `{Stale E} `{Typing (gmap atom ty) E ty} :=
  fv_subset_gamma : ∀ Γ (e : E) T, Γ ⊢ e ⋮ T → stale e ⊆ dom Γ.

#[global] Instance FvSubsetGamma_value : FvSubsetGamma value.
Proof. intros Γ v T Hty. exact (basic_typing_contains_fv_value Γ v T Hty). Qed.

#[global] Instance FvSubsetGamma_tm : FvSubsetGamma tm.
Proof. intros Γ e T Hty. exact (basic_typing_contains_fv_tm Γ e T Hty). Qed.

Lemma basic_typing_closed_value v T :
  ∅ ⊢ᵥ v ⋮ T → fv_value v = ∅.
Proof.
  intros Hty. apply basic_typing_contains_fv_value in Hty. set_solver.
Qed.

Lemma basic_typing_closed_tm e T :
  ∅ ⊢ₑ e ⋮ T → fv_tm e = ∅.
Proof.
  intros Hty. apply basic_typing_contains_fv_tm in Hty. set_solver.
Qed.

Lemma basic_typing_regular_value Γ v T :
  Γ ⊢ᵥ v ⋮ T → lc_value v.
Proof. apply typing_value_lc. Qed.

Lemma basic_typing_regular_tm Γ e T :
  Γ ⊢ₑ e ⋮ T → lc_tm e.
Proof. apply typing_tm_lc. Qed.

Class TypingLc (E : Type) `{Lc E} `{Typing (gmap atom ty) E ty} :=
  typing_lc : ∀ Γ (e : E) T, Γ ⊢ e ⋮ T → is_lc e.

#[global] Instance TypingLc_value : TypingLc value.
Proof. intros Γ v T Hty. exact (basic_typing_regular_value Γ v T Hty). Qed.

#[global] Instance TypingLc_tm : TypingLc tm.
Proof. intros Γ e T Hty. exact (basic_typing_regular_tm Γ e T Hty). Qed.

Lemma basic_typing_base_canonical_form v b :
  ∅ ⊢ᵥ v ⋮ TBase b →
  ∃ c, v = vconst c ∧ base_ty_of_const c = b.
Proof.
  intros Hty. inversion Hty; subst; eauto.
  all: try match goal with
  | Hlookup : ∅ !! _ = Some _ |- _ =>
      rewrite lookup_empty in Hlookup; discriminate
  end.
Qed.

Lemma basic_typing_bool_canonical_form v :
  ∅ ⊢ᵥ v ⋮ TBase TBool →
  v = vconst (cbool true) ∨ v = vconst (cbool false).
Proof.
  intros Hty.
  destruct (basic_typing_base_canonical_form v TBool Hty) as [[b|n|t|xs] [-> Hbase]];
    simpl in Hbase.
  - destruct b; auto.
  - discriminate.
  - discriminate.
  - discriminate.
Qed.

Lemma basic_typing_nat_canonical_form v :
  ∅ ⊢ᵥ v ⋮ TBase TNat →
  ∃ n, v = vconst (cnat n).
Proof.
  intros Hty.
  destruct (basic_typing_base_canonical_form v TNat Hty) as [[b|n|t|xs] [-> Hbase]];
    simpl in Hbase.
  - discriminate.
  - eauto.
  - discriminate.
  - discriminate.
Qed.

Lemma basic_typing_tree_canonical_form v :
  ∅ ⊢ᵥ v ⋮ TBase TTree →
  ∃ t, v = vconst (ctree t).
Proof.
  intros Hty.
  destruct (basic_typing_base_canonical_form v TTree Hty) as [[b|n|t|xs] [-> Hbase]];
    simpl in Hbase.
  - discriminate.
  - discriminate.
  - eauto.
  - discriminate.
Qed.

Lemma basic_typing_list_canonical_form v :
  ∅ ⊢ᵥ v ⋮ TBase TList →
  ∃ xs, v = vconst (clist xs).
Proof.
  intros Hty.
  destruct (basic_typing_base_canonical_form v TList Hty) as [[b|n|t|xs] [-> Hbase]];
    simpl in Hbase.
  - discriminate.
  - discriminate.
  - discriminate.
  - eauto.
Qed.

Lemma basic_typing_arrow_canonical_form v s T :
  ∅ ⊢ᵥ v ⋮ (s →ₜ T) →
  (∃ s' e, v = vlam s' e) ∨ (∃ Tf vf, v = vfix Tf vf).
Proof.
  intros Hty. inversion Hty; subst; eauto.
  all: try match goal with
  | Hlookup : ∅ !! _ = Some _ |- _ =>
      rewrite lookup_empty in Hlookup; discriminate
  end.
Qed.

(** ** Structural typing lemmas *)

Lemma basic_typing_weaken_value Γ Γ' v T :
  Γ ⊢ᵥ v ⋮ T → Γ ⊆ Γ' → Γ' ⊢ᵥ v ⋮ T.
Proof. apply weakening_value. Qed.

Lemma basic_typing_weaken_tm Γ Γ' e T :
  Γ ⊢ₑ e ⋮ T → Γ ⊆ Γ' → Γ' ⊢ₑ e ⋮ T.
Proof. apply weakening_tm. Qed.

Class BasicTypingWeaken (E : Type) `{Typing (gmap atom ty) E ty} :=
  basic_typing_weaken :
    ∀ Γ Γ' (e : E) T, Γ ⊆ Γ' → Γ ⊢ e ⋮ T → Γ' ⊢ e ⋮ T.

#[global] Instance BasicTypingWeaken_value : BasicTypingWeaken value.
Proof. intros Γ Γ' v T Hsub Hty. exact (basic_typing_weaken_value Γ Γ' v T Hty Hsub). Qed.

#[global] Instance BasicTypingWeaken_tm : BasicTypingWeaken tm.
Proof. intros Γ Γ' e T Hsub Hty. exact (basic_typing_weaken_tm Γ Γ' e T Hty Hsub). Qed.

Lemma basic_typing_weaken_insert_value Γ v T x U :
  x ∉ dom Γ →
  Γ ⊢ᵥ v ⋮ T →
  <[x := U]> Γ ⊢ᵥ v ⋮ T.
Proof.
  intros Hfresh Hty. eapply basic_typing_weaken_value; eauto.
  apply insert_subseteq. by apply not_elem_of_dom.
Qed.

Lemma basic_typing_weaken_insert_tm Γ e T x U :
  x ∉ dom Γ →
  Γ ⊢ₑ e ⋮ T →
  <[x := U]> Γ ⊢ₑ e ⋮ T.
Proof.
  intros Hfresh Hty. eapply basic_typing_weaken_tm; eauto.
  apply insert_subseteq. by apply not_elem_of_dom.
Qed.

Lemma swap_tree_branch_env_commute
    (Γ : gmap atom ty) (x y root left right : atom) :
  <[right := TBase TTree]>
    (<[left := TBase TTree]>
      (<[root := TBase TNat]>
        (@storeA_swap ty atom _ _ x y Γ : gmap atom ty))) =
  (@storeA_swap ty atom _ _ x y
    (<[swap x y right := TBase TTree]>
      (<[swap x y left := TBase TTree]>
        (<[swap x y root := TBase TNat]> Γ))) : gmap atom ty).
Proof.
  unfold storeA_swap.
  rewrite !kmap_insert by apply swap_inj.
  replace (swap x y (swap x y root)) with root by better_base_solver.
  replace (swap x y (swap x y left)) with left by better_base_solver.
  replace (swap x y (swap x y right)) with right by better_base_solver.
  reflexivity.
Qed.

Lemma swap_list_branch_env_commute
    (Γ : gmap atom ty) (x y hd tl : atom) :
  <[tl := TBase TList]>
    (<[hd := TBase TNat]>
      (@storeA_swap ty atom _ _ x y Γ : gmap atom ty)) =
  (@storeA_swap ty atom _ _ x y
    (<[swap x y tl := TBase TList]>
      (<[swap x y hd := TBase TNat]> Γ)) : gmap atom ty).
Proof.
  unfold storeA_swap.
  rewrite !kmap_insert by apply swap_inj.
  replace (swap x y (swap x y hd)) with hd by better_base_solver.
  replace (swap x y (swap x y tl)) with tl by better_base_solver.
  reflexivity.
Qed.

(** Typing depends only on the entries for the free variables of the
    expression/value being typed.  This is the convenient contraction principle
    used when a fresh environment coordinate is semantically irrelevant. *)
Lemma basic_typing_env_agree_value Γ Γ' v T :
  Γ ⊢ᵥ v ⋮ T →
  (∀ x, x ∈ fv_value v → Γ' !! x = Γ !! x) →
  Γ' ⊢ᵥ v ⋮ T.
Proof.
  intros Hty. revert Γ'.
  induction Hty using value_has_type_mut with
    (P := fun Γ v T _ =>
      ∀ Γ', (∀ x, x ∈ fv_value v → Γ' !! x = Γ !! x) → Γ' ⊢ᵥ v ⋮ T)
    (P0 := fun Γ e T _ =>
      ∀ Γ', (∀ x, x ∈ fv_tm e → Γ' !! x = Γ !! x) → Γ' ⊢ₑ e ⋮ T);
    intros Γ0 Hagree; simpl in *.
  - constructor.
  - econstructor. rewrite Hagree; [exact e | set_solver].
  - eapply VT_Lam with (L := L ∪ fv_tm e).
    intros y Hy.
    eapply H; [set_solver |].
    intros z Hz.
    destruct (decide (z = y)) as [->|Hne].
    + rewrite !lookup_insert. destruct (decide (y = y)); [reflexivity | congruence].
    + rewrite !lookup_insert_ne by congruence.
      assert (Hzfv : z ∈ fv_tm e).
      {
        pose proof (open_fv_tm e (vfvar y) 0) as Hopen.
        simpl in Hopen. set_solver.
      }
      rewrite Hagree by exact Hzfv. reflexivity.
  - eapply VT_Fix with (L := L ∪ fv_value vf).
    intros y Hy.
    eapply H; [set_solver |].
    intros z Hz.
    destruct (decide (z = y)) as [->|Hne].
    + rewrite !lookup_insert. destruct (decide (y = y)); [reflexivity | congruence].
    + rewrite !lookup_insert_ne by congruence.
      assert (Hzfv : z ∈ fv_value vf).
      {
        pose proof (open_fv_value vf (vfvar y) 0) as Hopen.
        simpl in Hopen. set_solver.
      }
      rewrite Hagree by exact Hzfv. reflexivity.
  - constructor. eapply IHHty. intros z Hz. apply Hagree. set_solver.
  - eapply TT_Let with (L := L ∪ fv_tm e2).
    + eapply IHHty. intros z Hz. apply Hagree. set_solver.
    + intros y Hy.
      eapply H; [set_solver |].
      intros z Hz.
      destruct (decide (z = y)) as [->|Hne].
      * rewrite !lookup_insert. destruct (decide (y = y)); [reflexivity | congruence].
      * rewrite !lookup_insert_ne by congruence.
        assert (Hzfv : z ∈ fv_tm e2).
        {
          pose proof (open_fv_tm e2 (vfvar y) 0) as Hopen.
          simpl in Hopen. set_solver.
        }
        rewrite Hagree by (simpl; set_solver). reflexivity.
  - econstructor; eauto.
  - eapply TT_BinOp; [eassumption| |];
      match goal with
      | IH : ∀ Γ', (∀ z, z ∈ fv_value _ → Γ' !! z = _ !! z) → Γ' ⊢ᵥ _ ⋮ _ |- _ =>
          eapply IH; intros z Hz; apply Hagree; set_solver
      end.
  - eapply TT_App;
      match goal with
      | |- _ ⊢ᵥ _ ⋮ _ =>
          match goal with
          | IH : ∀ Γ', (∀ z, z ∈ fv_value _ → Γ' !! z = _ !! z) → Γ' ⊢ᵥ _ ⋮ _ |- _ =>
              eapply IH; intros z Hz; apply Hagree; set_solver
          end
      | |- _ ⊢ₑ _ ⋮ _ =>
          match goal with
          | IH : ∀ Γ', (∀ z, z ∈ fv_tm _ → Γ' !! z = _ !! z) → Γ' ⊢ₑ _ ⋮ _ |- _ =>
              eapply IH; intros z Hz; apply Hagree; set_solver
          end
      end.
  - eapply TT_Match;
      match goal with
      | |- _ ⊢ᵥ _ ⋮ _ =>
          match goal with
          | IH : ∀ Γ', (∀ z, z ∈ fv_value _ → Γ' !! z = _ !! z) → Γ' ⊢ᵥ _ ⋮ _ |- _ =>
              eapply IH; intros z Hz; apply Hagree; set_solver
          end
      | |- _ ⊢ₑ _ ⋮ _ =>
          match goal with
          | IH : ∀ Γ', (∀ z, z ∈ fv_tm _ → Γ' !! z = _ !! z) → Γ' ⊢ₑ _ ⋮ _ |- _ =>
              eapply IH; intros z Hz; apply Hagree; set_solver
          end
      end.
  - econstructor;
      match goal with
      | IH : ∀ Γ', (∀ z, z ∈ fv_value _ → Γ' !! z = _ !! z) → Γ' ⊢ᵥ _ ⋮ _ |- _ =>
          eapply IH; intros z Hz; apply Hagree; set_solver
      end.
  - eapply TT_TreeMatch with (L := L ∪ fv_value v ∪ fv_tm eleaf ∪ fv_tm enode).
    + match goal with
      | IH : ∀ Γ', (∀ z, z ∈ fv_value v → Γ' !! z = _ !! z) → Γ' ⊢ᵥ v ⋮ _ |- _ =>
          eapply IH; intros z Hz; apply Hagree; set_solver
      end.
    + match goal with
      | IH : ∀ Γ', (∀ z, z ∈ fv_tm eleaf → Γ' !! z = _ !! z) → Γ' ⊢ₑ eleaf ⋮ _ |- _ =>
          eapply IH; intros z Hz; apply Hagree; set_solver
      end.
    + intros root left right Hroot Hleft Hright.
      eapply H; [set_solver | set_solver | set_solver |].
      intros z Hz.
      repeat rewrite lookup_insert.
      repeat case_decide; subst; try reflexivity.
      assert (Hzfv : z ∈ fv_tm enode).
      {
        unfold open_tree_node_branch, open_tree_node_branch_value in Hz.
        pose proof (open_fv_tm enode (vfvar root) 0) as Hopen_root.
        pose proof (open_fv_tm
          (open_tm 0 (vfvar root) enode) (vfvar left) 1) as Hopen_left.
        pose proof (open_fv_tm
          (open_tm 1 (vfvar left) (open_tm 0 (vfvar root) enode))
          (vfvar right) 2) as Hopen_right.
        simpl in Hopen_root, Hopen_left, Hopen_right.
        set_solver.
	      }
	      rewrite Hagree by (simpl; set_solver). reflexivity.
  - econstructor;
      match goal with
      | |- _ ⊢ᵥ _ ⋮ _ =>
          match goal with
          | IH : ∀ Γ', (∀ z, z ∈ fv_value _ → Γ' !! z = _ !! z) → Γ' ⊢ᵥ _ ⋮ _ |- _ =>
              eapply IH; intros z Hz; apply Hagree; set_solver
          end
      end.
  - eapply TT_ListMatch with (L := L ∪ fv_value v ∪ fv_tm enil ∪ fv_tm econs).
    + match goal with
      | IH : ∀ Γ', (∀ z, z ∈ fv_value v → Γ' !! z = _ !! z) → Γ' ⊢ᵥ v ⋮ _ |- _ =>
          eapply IH; intros z Hz; apply Hagree; set_solver
      end.
    + match goal with
      | IH : ∀ Γ', (∀ z, z ∈ fv_tm enil → Γ' !! z = _ !! z) → Γ' ⊢ₑ enil ⋮ _ |- _ =>
          eapply IH; intros z Hz; apply Hagree; set_solver
      end.
    + intros hd tl Hhd Htl.
      eapply H; [set_solver | set_solver |].
      intros z Hz.
      repeat rewrite lookup_insert.
      repeat case_decide; subst; try reflexivity.
      assert (Hzfv : z ∈ fv_tm econs).
      {
        unfold open_list_cons_branch, open_list_cons_branch_value in Hz.
        pose proof (open_fv_tm econs (vfvar hd) 0) as Hopen_hd.
        pose proof (open_fv_tm
          (open_tm 0 (vfvar hd) econs) (vfvar tl) 1) as Hopen_tl.
        simpl in Hopen_hd, Hopen_tl.
        set_solver.
	      }
	      rewrite Hagree by (simpl; set_solver). reflexivity.
Qed.

Lemma basic_typing_swap_value Γ v T x y :
  Γ ⊢ᵥ v ⋮ T →
  (@storeA_swap ty atom _ _ x y Γ : gmap atom ty) ⊢ᵥ
    value_swap_atom x y v ⋮ T
with basic_typing_swap_tm Γ e T x y :
  Γ ⊢ₑ e ⋮ T →
  (@storeA_swap ty atom _ _ x y Γ : gmap atom ty) ⊢ₑ
    tm_swap_atom x y e ⋮ T.
Proof.
  - intros Hty.
    induction Hty using value_has_type_mut with
      (P0 := fun Γ e T _ =>
        (@storeA_swap ty atom _ _ x y Γ : gmap atom ty) ⊢ₑ
          tm_swap_atom x y e ⋮ T);
      simpl.
    + constructor.
    + econstructor. rewrite storeA_swap_lookup. exact e.
    + eapply VT_Lam with (L := set_swap x y L).
      intros z Hz.
      change (<[z:=s]>
        ((@storeA_swap ty atom _ _ x y Γ : gmap atom ty)) ⊢ₑ
          open_tm 0 (vfvar z) (tm_swap_atom x y e) ⋮ T).
      rewrite open_tm_swap_atom.
      replace (<[z:=s]> ((@storeA_swap ty atom _ _ x y Γ : gmap atom ty)))
        with ((@storeA_swap ty atom _ _ x y
          (<[swap x y z := s]> Γ) : gmap atom ty)).
      * apply H. intros Hin. apply Hz.
        rewrite elem_of_set_swap. exact Hin.
      * change ((@storeA_swap ty atom _ _ x y (<[swap x y z := s]> Γ)
            : gmap atom ty) =
          <[z := s]> (@storeA_swap ty atom _ _ x y Γ : gmap atom ty)).
        unfold storeA_swap.
        rewrite kmap_insert by apply swap_inj.
        replace (swap x y (swap x y z)) with z by better_base_solver.
        reflexivity.
    + eapply VT_Fix with (L := set_swap x y L).
      intros z Hz.
      change (<[z:=sx]>
        ((@storeA_swap ty atom _ _ x y Γ : gmap atom ty)) ⊢ᵥ
          open_value 0 (vfvar z) (value_swap_atom x y vf) ⋮
            ((sx →ₜ T) →ₜ T)).
      rewrite open_value_swap_atom.
      replace (<[z:=sx]> ((@storeA_swap ty atom _ _ x y Γ : gmap atom ty)))
        with ((@storeA_swap ty atom _ _ x y
          (<[swap x y z := sx]> Γ) : gmap atom ty)).
      * apply H. intros Hin. apply Hz.
        rewrite elem_of_set_swap. exact Hin.
      * change ((@storeA_swap ty atom _ _ x y (<[swap x y z := sx]> Γ)
            : gmap atom ty) =
          <[z := sx]> (@storeA_swap ty atom _ _ x y Γ : gmap atom ty)).
        unfold storeA_swap.
        rewrite kmap_insert by apply swap_inj.
        replace (swap x y (swap x y z)) with z by better_base_solver.
        reflexivity.
    + econstructor; eauto.
    + eapply TT_Let; [eauto |].
      intros z Hz.
      change (<[z:=T1]>
        ((@storeA_swap ty atom _ _ x y Γ : gmap atom ty)) ⊢ₑ
          open_tm 0 (vfvar z) (tm_swap_atom x y e2) ⋮ T2).
      rewrite open_tm_swap_atom.
      replace (<[z:=T1]> ((@storeA_swap ty atom _ _ x y Γ : gmap atom ty)))
        with ((@storeA_swap ty atom _ _ x y
          (<[swap x y z := T1]> Γ) : gmap atom ty)).
      * apply H. intros Hin. apply Hz.
        rewrite elem_of_set_swap. exact Hin.
      * change ((@storeA_swap ty atom _ _ x y (<[swap x y z := T1]> Γ)
            : gmap atom ty) =
          <[z := T1]> (@storeA_swap ty atom _ _ x y Γ : gmap atom ty)).
        unfold storeA_swap.
        rewrite kmap_insert by apply swap_inj.
        replace (swap x y (swap x y z)) with z by better_base_solver.
        reflexivity.
	    + econstructor; eauto.
	    + econstructor; eauto.
	    + econstructor; eauto.
	    + econstructor; eauto.
	    + econstructor; eauto.
	    + eapply TT_TreeMatch with (L := set_swap x y L).
      * eauto.
      * eauto.
      * intros root left right Hroot Hleft Hright.
        change (<[right := TBase TTree]>
          (<[left := TBase TTree]>
            (<[root := TBase TNat]>
              (@storeA_swap ty atom _ _ x y Γ : gmap atom ty))) ⊢ₑ
            open_tree_node_branch root left right (tm_swap_atom x y enode) ⋮ T).
        rewrite open_tree_node_branch_swap_atom.
	        rewrite swap_tree_branch_env_commute.
	        apply H.
	        -- intros Hin. apply Hroot. rewrite elem_of_set_swap. exact Hin.
	        -- intros Hin. apply Hleft.
	           apply elem_of_union in Hin as [Hin|Hin].
	           ++ apply elem_of_union_l. rewrite elem_of_set_swap. exact Hin.
	           ++ apply elem_of_union_r.
	              rewrite !elem_of_singleton in Hin |- *.
	              apply (swap_inj x y) in Hin. exact Hin.
	        -- intros Hin. apply Hright.
	           apply elem_of_union in Hin as [Hin|Hin].
	           ++ apply elem_of_union in Hin as [Hin|Hin].
	              ** apply elem_of_union_l. apply elem_of_union_l.
	                 rewrite elem_of_set_swap. exact Hin.
	              ** apply elem_of_union_l. apply elem_of_union_r.
	                 rewrite !elem_of_singleton in Hin |- *.
	                 apply (swap_inj x y) in Hin. exact Hin.
		           ++ apply elem_of_union_r.
		              rewrite !elem_of_singleton in Hin |- *.
		              apply (swap_inj x y) in Hin. exact Hin.
	    + econstructor; eauto.
	    + eapply TT_ListMatch with (L := set_swap x y L).
	      * eauto.
	      * eauto.
	      * intros hd tl Hhd Htl.
	        change (<[tl := TBase TList]>
	          (<[hd := TBase TNat]>
	            (@storeA_swap ty atom _ _ x y Γ : gmap atom ty)) ⊢ₑ
	            open_list_cons_branch hd tl (tm_swap_atom x y econs) ⋮ T).
	        rewrite open_list_cons_branch_swap_atom.
	        rewrite swap_list_branch_env_commute.
	        apply H.
	        -- intros Hin. apply Hhd. rewrite elem_of_set_swap. exact Hin.
	        -- intros Hin. apply Htl.
	           apply elem_of_union in Hin as [Hin|Hin].
	           ++ apply elem_of_union_l. rewrite elem_of_set_swap. exact Hin.
	           ++ apply elem_of_union_r.
	              rewrite !elem_of_singleton in Hin |- *.
	              apply (swap_inj x y) in Hin. exact Hin.
  - intros Hty.
    induction Hty using tm_has_type_mut with
      (P := fun Γ v T _ =>
        (@storeA_swap ty atom _ _ x y Γ : gmap atom ty) ⊢ᵥ
          value_swap_atom x y v ⋮ T);
      simpl.
    + constructor.
    + econstructor. rewrite storeA_swap_lookup. exact e.
    + eapply VT_Lam with (L := set_swap x y L).
      intros z Hz.
      change (<[z:=s]>
        ((@storeA_swap ty atom _ _ x y Γ : gmap atom ty)) ⊢ₑ
          open_tm 0 (vfvar z) (tm_swap_atom x y e) ⋮ T).
      rewrite open_tm_swap_atom.
      replace (<[z:=s]> ((@storeA_swap ty atom _ _ x y Γ : gmap atom ty)))
        with ((@storeA_swap ty atom _ _ x y
          (<[swap x y z := s]> Γ) : gmap atom ty)).
      * apply H. intros Hin. apply Hz.
        rewrite elem_of_set_swap. exact Hin.
      * change ((@storeA_swap ty atom _ _ x y (<[swap x y z := s]> Γ)
            : gmap atom ty) =
          <[z := s]> (@storeA_swap ty atom _ _ x y Γ : gmap atom ty)).
        unfold storeA_swap.
        rewrite kmap_insert by apply swap_inj.
        replace (swap x y (swap x y z)) with z by better_base_solver.
        reflexivity.
    + eapply VT_Fix with (L := set_swap x y L).
      intros z Hz.
      change (<[z:=sx]>
        ((@storeA_swap ty atom _ _ x y Γ : gmap atom ty)) ⊢ᵥ
          open_value 0 (vfvar z) (value_swap_atom x y vf) ⋮
            ((sx →ₜ T) →ₜ T)).
      rewrite open_value_swap_atom.
      replace (<[z:=sx]> ((@storeA_swap ty atom _ _ x y Γ : gmap atom ty)))
        with ((@storeA_swap ty atom _ _ x y
          (<[swap x y z := sx]> Γ) : gmap atom ty)).
      * apply H. intros Hin. apply Hz.
        rewrite elem_of_set_swap. exact Hin.
      * change ((@storeA_swap ty atom _ _ x y (<[swap x y z := sx]> Γ)
            : gmap atom ty) =
          <[z := sx]> (@storeA_swap ty atom _ _ x y Γ : gmap atom ty)).
        unfold storeA_swap.
        rewrite kmap_insert by apply swap_inj.
        replace (swap x y (swap x y z)) with z by better_base_solver.
        reflexivity.
    + econstructor; eauto.
    + eapply TT_Let; [eauto |].
      intros z Hz.
      change (<[z:=T1]>
        ((@storeA_swap ty atom _ _ x y Γ : gmap atom ty)) ⊢ₑ
          open_tm 0 (vfvar z) (tm_swap_atom x y e2) ⋮ T2).
      rewrite open_tm_swap_atom.
      replace (<[z:=T1]> ((@storeA_swap ty atom _ _ x y Γ : gmap atom ty)))
        with ((@storeA_swap ty atom _ _ x y
          (<[swap x y z := T1]> Γ) : gmap atom ty)).
      * apply H. intros Hin. apply Hz.
        rewrite elem_of_set_swap. exact Hin.
      * change ((@storeA_swap ty atom _ _ x y (<[swap x y z := T1]> Γ)
            : gmap atom ty) =
          <[z := T1]> (@storeA_swap ty atom _ _ x y Γ : gmap atom ty)).
        unfold storeA_swap.
        rewrite kmap_insert by apply swap_inj.
        replace (swap x y (swap x y z)) with z by better_base_solver.
        reflexivity.
    + econstructor; eauto.
    + econstructor; eauto.
    + econstructor; eauto.
    + econstructor; eauto.
    + econstructor; eauto.
    + eapply TT_TreeMatch with (L := set_swap x y L).
      * eauto.
      * eauto.
      * intros root left right Hroot Hleft Hright.
        change (<[right := TBase TTree]>
          (<[left := TBase TTree]>
            (<[root := TBase TNat]>
              (@storeA_swap ty atom _ _ x y Γ : gmap atom ty))) ⊢ₑ
            open_tree_node_branch root left right (tm_swap_atom x y enode) ⋮ T).
        rewrite open_tree_node_branch_swap_atom.
	        rewrite swap_tree_branch_env_commute.
	        apply H.
	        -- intros Hin. apply Hroot. rewrite elem_of_set_swap. exact Hin.
	        -- intros Hin. apply Hleft.
	           apply elem_of_union in Hin as [Hin|Hin].
	           ++ apply elem_of_union_l. rewrite elem_of_set_swap. exact Hin.
	           ++ apply elem_of_union_r.
	              rewrite !elem_of_singleton in Hin |- *.
	              apply (swap_inj x y) in Hin. exact Hin.
	        -- intros Hin. apply Hright.
	           apply elem_of_union in Hin as [Hin|Hin].
	           ++ apply elem_of_union in Hin as [Hin|Hin].
	              ** apply elem_of_union_l. apply elem_of_union_l.
	                 rewrite elem_of_set_swap. exact Hin.
	              ** apply elem_of_union_l. apply elem_of_union_r.
	                 rewrite !elem_of_singleton in Hin |- *.
	                 apply (swap_inj x y) in Hin. exact Hin.
		           ++ apply elem_of_union_r.
		              rewrite !elem_of_singleton in Hin |- *.
		              apply (swap_inj x y) in Hin. exact Hin.
	    + econstructor; eauto.
	    + eapply TT_ListMatch with (L := set_swap x y L).
	      * eauto.
	      * eauto.
	      * intros hd tl Hhd Htl.
	        change (<[tl := TBase TList]>
	          (<[hd := TBase TNat]>
	            (@storeA_swap ty atom _ _ x y Γ : gmap atom ty)) ⊢ₑ
	            open_list_cons_branch hd tl (tm_swap_atom x y econs) ⋮ T).
	        rewrite open_list_cons_branch_swap_atom.
	        rewrite swap_list_branch_env_commute.
	        apply H.
	        -- intros Hin. apply Hhd. rewrite elem_of_set_swap. exact Hin.
	        -- intros Hin. apply Htl.
	           apply elem_of_union in Hin as [Hin|Hin].
	           ++ apply elem_of_union_l. rewrite elem_of_set_swap. exact Hin.
	           ++ apply elem_of_union_r.
	              rewrite !elem_of_singleton in Hin |- *.
	              apply (swap_inj x y) in Hin. exact Hin.
Qed.

Lemma basic_typing_env_agree_tm Γ Γ' e T :
  Γ ⊢ₑ e ⋮ T →
  (∀ x, x ∈ fv_tm e → Γ' !! x = Γ !! x) →
  Γ' ⊢ₑ e ⋮ T.
Proof.
  intros Hty. revert Γ'.
  induction Hty using tm_has_type_mut with
    (P := fun Γ v T _ =>
      ∀ Γ', (∀ x, x ∈ fv_value v → Γ' !! x = Γ !! x) → Γ' ⊢ᵥ v ⋮ T)
    (P0 := fun Γ e T _ =>
      ∀ Γ', (∀ x, x ∈ fv_tm e → Γ' !! x = Γ !! x) → Γ' ⊢ₑ e ⋮ T);
    intros Γ0 Hagree; simpl in *.
  - constructor.
  - econstructor. rewrite Hagree; [exact e | set_solver].
  - eapply VT_Lam with (L := L ∪ fv_tm e).
    intros y Hy.
    eapply H; [set_solver |].
    intros z Hz.
    destruct (decide (z = y)) as [->|Hne].
    + rewrite !lookup_insert. destruct (decide (y = y)); [reflexivity | congruence].
    + rewrite !lookup_insert_ne by congruence.
      assert (Hzfv : z ∈ fv_tm e).
      {
        pose proof (open_fv_tm e (vfvar y) 0) as Hopen.
        simpl in Hopen. set_solver.
      }
      rewrite Hagree by exact Hzfv. reflexivity.
  - eapply VT_Fix with (L := L ∪ fv_value vf).
    intros y Hy.
    eapply H; [set_solver |].
    intros z Hz.
    destruct (decide (z = y)) as [->|Hne].
    + rewrite !lookup_insert. destruct (decide (y = y)); [reflexivity | congruence].
    + rewrite !lookup_insert_ne by congruence.
      assert (Hzfv : z ∈ fv_value vf).
      {
        pose proof (open_fv_value vf (vfvar y) 0) as Hopen.
        simpl in Hopen. set_solver.
      }
      rewrite Hagree by exact Hzfv. reflexivity.
  - constructor. eapply IHHty. intros z Hz. apply Hagree. set_solver.
  - eapply TT_Let with (L := L ∪ fv_tm e2).
    + eapply IHHty. intros z Hz. apply Hagree. set_solver.
    + intros y Hy.
      eapply H; [set_solver |].
      intros z Hz.
      destruct (decide (z = y)) as [->|Hne].
      * rewrite !lookup_insert. destruct (decide (y = y)); [reflexivity | congruence].
      * rewrite !lookup_insert_ne by congruence.
        assert (Hzfv : z ∈ fv_tm e2).
        {
          pose proof (open_fv_tm e2 (vfvar y) 0) as Hopen.
          simpl in Hopen. set_solver.
        }
        rewrite Hagree by (simpl; set_solver). reflexivity.
  - econstructor; eauto.
  - eapply TT_BinOp; [eassumption| |];
      match goal with
      | IH : ∀ Γ', (∀ z, z ∈ fv_value _ → Γ' !! z = _ !! z) → Γ' ⊢ᵥ _ ⋮ _ |- _ =>
          eapply IH; intros z Hz; apply Hagree; set_solver
      end.
  - eapply TT_App;
      match goal with
      | IH : ∀ Γ', (∀ z, z ∈ fv_value _ → Γ' !! z = _ !! z) → Γ' ⊢ᵥ _ ⋮ _ |- _ =>
          eapply IH; intros z Hz; apply Hagree; set_solver
      end.
  - eapply TT_Match;
      match goal with
      | |- _ ⊢ᵥ _ ⋮ _ =>
          match goal with
          | IH : ∀ Γ', (∀ z, z ∈ fv_value _ → Γ' !! z = _ !! z) → Γ' ⊢ᵥ _ ⋮ _ |- _ =>
              eapply IH; intros z Hz; apply Hagree; set_solver
          end
      | |- _ ⊢ₑ _ ⋮ _ =>
          match goal with
          | IH : ∀ Γ', (∀ z, z ∈ fv_tm _ → Γ' !! z = _ !! z) → Γ' ⊢ₑ _ ⋮ _ |- _ =>
              eapply IH; intros z Hz; apply Hagree; set_solver
          end
      end.
  - econstructor;
      match goal with
      | IH : ∀ Γ', (∀ z, z ∈ fv_value _ → Γ' !! z = _ !! z) → Γ' ⊢ᵥ _ ⋮ _ |- _ =>
          eapply IH; intros z Hz; apply Hagree; set_solver
      end.
  - eapply TT_TreeMatch with (L := L ∪ fv_value v ∪ fv_tm eleaf ∪ fv_tm enode).
    + match goal with
      | IH : ∀ Γ', (∀ z, z ∈ fv_value v → Γ' !! z = _ !! z) → Γ' ⊢ᵥ v ⋮ _ |- _ =>
          eapply IH; intros z Hz; apply Hagree; set_solver
      end.
    + match goal with
      | IH : ∀ Γ', (∀ z, z ∈ fv_tm eleaf → Γ' !! z = _ !! z) → Γ' ⊢ₑ eleaf ⋮ _ |- _ =>
          eapply IH; intros z Hz; apply Hagree; set_solver
      end.
    + intros root left right Hroot Hleft Hright.
      eapply H; [set_solver | set_solver | set_solver |].
      intros z Hz.
      repeat rewrite lookup_insert.
      repeat case_decide; subst; try reflexivity.
      assert (Hzfv : z ∈ fv_tm enode).
      {
        unfold open_tree_node_branch, open_tree_node_branch_value in Hz.
        pose proof (open_fv_tm enode (vfvar root) 0) as Hopen_root.
        pose proof (open_fv_tm
          (open_tm 0 (vfvar root) enode) (vfvar left) 1) as Hopen_left.
        pose proof (open_fv_tm
          (open_tm 1 (vfvar left) (open_tm 0 (vfvar root) enode))
          (vfvar right) 2) as Hopen_right.
        simpl in Hopen_root, Hopen_left, Hopen_right.
        set_solver.
	      }
	      rewrite Hagree by (simpl; set_solver). reflexivity.
  - econstructor;
      match goal with
      | |- _ ⊢ᵥ _ ⋮ _ =>
          match goal with
          | IH : ∀ Γ', (∀ z, z ∈ fv_value _ → Γ' !! z = _ !! z) → Γ' ⊢ᵥ _ ⋮ _ |- _ =>
              eapply IH; intros z Hz; apply Hagree; set_solver
          end
      end.
  - eapply TT_ListMatch with (L := L ∪ fv_value v ∪ fv_tm enil ∪ fv_tm econs).
    + match goal with
      | IH : ∀ Γ', (∀ z, z ∈ fv_value v → Γ' !! z = _ !! z) → Γ' ⊢ᵥ v ⋮ _ |- _ =>
          eapply IH; intros z Hz; apply Hagree; set_solver
      end.
    + match goal with
      | IH : ∀ Γ', (∀ z, z ∈ fv_tm enil → Γ' !! z = _ !! z) → Γ' ⊢ₑ enil ⋮ _ |- _ =>
          eapply IH; intros z Hz; apply Hagree; set_solver
      end.
    + intros hd tl Hhd Htl.
      eapply H; [set_solver | set_solver |].
      intros z Hz.
      repeat rewrite lookup_insert.
      repeat case_decide; subst; try reflexivity.
      assert (Hzfv : z ∈ fv_tm econs).
      {
        unfold open_list_cons_branch, open_list_cons_branch_value in Hz.
        pose proof (open_fv_tm econs (vfvar hd) 0) as Hopen_hd.
        pose proof (open_fv_tm
          (open_tm 0 (vfvar hd) econs) (vfvar tl) 1) as Hopen_tl.
        simpl in Hopen_hd, Hopen_tl.
        set_solver.
      }
      rewrite Hagree by (simpl; set_solver). reflexivity.
Qed.

Lemma basic_typing_drop_insert_fresh_value Γ v T x U :
  x ∉ fv_value v →
  <[x := U]> Γ ⊢ᵥ v ⋮ T →
  Γ ⊢ᵥ v ⋮ T.
Proof.
  intros Hfresh Hty.
  eapply basic_typing_env_agree_value; [exact Hty |].
  intros z Hz.
  rewrite lookup_insert_ne; [reflexivity | set_solver].
Qed.

Lemma basic_typing_drop_insert_fresh_tm Γ e T x U :
  x ∉ fv_tm e →
  <[x := U]> Γ ⊢ₑ e ⋮ T →
  Γ ⊢ₑ e ⋮ T.
Proof.
  intros Hfresh Hty.
  eapply basic_typing_env_agree_tm; [exact Hty |].
  intros z Hz.
  rewrite lookup_insert_ne; [reflexivity | set_solver].
Qed.

Lemma basic_typing_subst_value Γ x s v T vx :
  Γ ⊢ᵥ v ⋮ T →
  ∅ ⊢ᵥ vx ⋮ s →
  Γ !! x = Some s →
  delete x Γ ⊢ᵥ ({x := vx} v) ⋮ T.
Proof. apply subst_typing_value. Qed.

Lemma basic_typing_subst_tm Γ x s e T vx :
  Γ ⊢ₑ e ⋮ T →
  ∅ ⊢ᵥ vx ⋮ s →
  Γ !! x = Some s →
  delete x Γ ⊢ₑ ({x := vx} e) ⋮ T.
Proof. apply subst_typing_tm. Qed.

Class BasicTypingSubst (E : Type) `{Typing (gmap atom ty) E ty} `{SubstV value E} :=
  basic_typing_subst :
    ∀ Γ x s (e : E) T vx,
      Γ ⊢ e ⋮ T →
      ∅ ⊢ᵥ vx ⋮ s →
      Γ !! x = Some s →
      delete x Γ ⊢ ({x := vx} e) ⋮ T.

#[global] Instance BasicTypingSubst_value : BasicTypingSubst value.
Proof. intros Γ x s v T vx Hty Hv Hlook. exact (basic_typing_subst_value Γ x s v T vx Hty Hv Hlook). Qed.

#[global] Instance BasicTypingSubst_tm : BasicTypingSubst tm.
Proof. intros Γ x s e T vx Hty Hv Hlook. exact (basic_typing_subst_tm Γ x s e T vx Hty Hv Hlook). Qed.

(** Opening with a typed value, via a fresh variable.  This is the shape used
    pervasively in the reference developments; its proof depends on the
    stronger substitution lemma over [<[x:=U]> Γ], so it is recorded here as a
    target for the substitution pass. *)
Lemma basic_typing_open_value Γ x u U v T :
  x ∉ fv_value v →
  Γ ⊢ᵥ u ⋮ U →
  <[x := U]> Γ ⊢ᵥ v ^^ x ⋮ T →
  Γ ⊢ᵥ open_value 0 u v ⋮ T.
Proof.
  intros Hfresh Hu Hopen.
  assert (Hlc_u : lc_value u) by exact (typing_value_lc _ _ _ Hu).
  rewrite <- (subst_intro_value x u 0 v Hfresh Hlc_u).
  eapply subst_typing_insert_value; eauto.
Qed.

Lemma basic_typing_open_tm Γ x u U e T :
  x ∉ fv_tm e →
  Γ ⊢ᵥ u ⋮ U →
  <[x := U]> Γ ⊢ₑ e ^^ x ⋮ T →
  Γ ⊢ₑ open_tm 0 u e ⋮ T.
Proof.
  intros Hfresh Hu Hopen.
  assert (Hlc_u : lc_value u) by exact (typing_value_lc _ _ _ Hu).
  rewrite <- (subst_intro_tm x u 0 e Hfresh Hlc_u).
  eapply subst_typing_insert_tm; eauto.
Qed.

Class BasicTypingOpen (E : Type)
    `{Stale E} `{Typing (gmap atom ty) E ty} `{Open value E} :=
  basic_typing_open :
    ∀ Γ x u U (e : E) T,
      x ∉ stale e →
      Γ ⊢ᵥ u ⋮ U →
      <[x := U]> Γ ⊢ open_one 0 (vfvar x) e ⋮ T →
      Γ ⊢ open_one 0 u e ⋮ T.

#[global] Instance BasicTypingOpen_value : BasicTypingOpen value.
Proof. intros Γ x u U v T Hfresh Hu Hopen. exact (basic_typing_open_value Γ x u U v T Hfresh Hu Hopen). Qed.

#[global] Instance BasicTypingOpen_tm : BasicTypingOpen tm.
Proof. intros Γ x u U e T Hfresh Hu Hopen. exact (basic_typing_open_tm Γ x u U e T Hfresh Hu Hopen). Qed.

Lemma basic_typing_open_tree_node_branch_const
    Γ root left right n tl tr enode T :
  root ∉ fv_tm enode →
  left ∉ fv_tm enode →
  right ∉ fv_tm enode →
  root <> left →
  root <> right →
  left <> right →
  <[right := TBase TTree]>
    (<[left := TBase TTree]>
      (<[root := TBase TNat]> Γ))
    ⊢ₑ open_tree_node_branch root left right enode ⋮ T →
  Γ ⊢ₑ open_tree_node_branch_value
    (vconst (cnat n)) (vconst (ctree tl)) (vconst (ctree tr)) enode ⋮ T.
Proof.
  intros Hroot_fv Hleft_fv Hright_fv Hroot_left Hroot_right Hleft_right Hbranch.
  pose (vr := vconst (cnat n)).
  pose (vl := vconst (ctree tl)).
  pose (vt := vconst (ctree tr)).
  pose (Γroot := <[root := TBase TNat]> Γ).
  pose (Γleft := <[left := TBase TTree]> Γroot).
  assert (Hright :
    Γleft ⊢ₑ ({right := vt} open_tree_node_branch root left right enode) ⋮ T).
  {
    subst Γleft Γroot vt.
    eapply subst_typing_insert_tm; [exact Hbranch | constructor].
  }
  assert (Hleft :
    Γroot ⊢ₑ ({left := vl} ({right := vt}
      open_tree_node_branch root left right enode)) ⋮ T).
  {
    subst Γleft Γroot vl.
    eapply subst_typing_insert_tm; [exact Hright | constructor].
  }
  assert (Hroot :
    Γ ⊢ₑ ({root := vr} ({left := vl} ({right := vt}
      open_tree_node_branch root left right enode))) ⋮ T).
  {
    subst Γroot vr.
    eapply subst_typing_insert_tm; [exact Hleft | constructor].
  }
  subst vr vl vt.
  replace ({root := vconst (cnat n)}
    ({left := vconst (ctree tl)}
      ({right := vconst (ctree tr)}
        open_tree_node_branch root left right enode))) with
    (open_tree_node_branch_value
      (vconst (cnat n)) (vconst (ctree tl)) (vconst (ctree tr)) enode)
    in Hroot.
  - exact Hroot.
  - symmetry.
    apply subst_tree_node_branch_value; simpl; try set_solver; constructor.
Qed.

Lemma basic_typing_open_list_cons_branch_const
    Γ hd tl n xs econs T :
  hd ∉ fv_tm econs →
  tl ∉ fv_tm econs →
  hd <> tl →
  <[tl := TBase TList]>
    (<[hd := TBase TNat]> Γ)
    ⊢ₑ open_list_cons_branch hd tl econs ⋮ T →
  Γ ⊢ₑ open_list_cons_branch_value
    (vconst (cnat n)) (vconst (clist xs)) econs ⋮ T.
Proof.
  intros Hhd_fv Htl_fv Hhd_tl Hbranch.
  pose (vh := vconst (cnat n)).
  pose (vt := vconst (clist xs)).
  pose (Γhd := <[hd := TBase TNat]> Γ).
  assert (Htl :
    Γhd ⊢ₑ ({tl := vt} open_list_cons_branch hd tl econs) ⋮ T).
  {
    subst Γhd vt.
    eapply subst_typing_insert_tm; [exact Hbranch | constructor].
  }
  assert (Hhd :
    Γ ⊢ₑ ({hd := vh} ({tl := vt}
      open_list_cons_branch hd tl econs)) ⋮ T).
  {
    subst Γhd vh.
    eapply subst_typing_insert_tm; [exact Htl | constructor].
  }
  subst vh vt.
  replace ({hd := vconst (cnat n)}
    ({tl := vconst (clist xs)}
      open_list_cons_branch hd tl econs)) with
    (open_list_cons_branch_value
      (vconst (cnat n)) (vconst (clist xs)) econs)
    in Hhd.
  - exact Hhd.
  - symmetry.
    apply subst_list_cons_branch_value; simpl; try set_solver; constructor.
Qed.

Lemma basic_typing_unique_value Γ v T1 T2 :
  Γ ⊢ᵥ v ⋮ T1 → Γ ⊢ᵥ v ⋮ T2 → T1 = T2.
Proof.
  intros Hty.
  revert T2.
  induction Hty using value_has_type_mut with
      (P0 := fun Γ e T1 _ => ∀ T2, Γ ⊢ₑ e ⋮ T2 → T1 = T2);
      intros T2' Hother; inversion Hother; subst; eauto.
  - simplify_eq. reflexivity.
  - f_equal.
    pose (x := fresh_for (L ∪ L0)).
    assert (Hx : x ∉ L ∪ L0) by (subst x; apply fresh_for_not_in).
    specialize (H x ltac:(set_solver)).
    eapply H.
    match goal with
    | Hopen : ∀ y : atom, y ∉ L0 → <[y:=s]> Γ ⊢ₑ e ^^ y ⋮ _ |- _ =>
        eapply Hopen; set_solver
    end.
  - pose (x := fresh_for (L ∪ L0)).
    assert (Hx : x ∉ L ∪ L0) by (subst x; apply fresh_for_not_in).
    assert (T1 = T0) by eauto. subst T0.
    match goal with
    | IH : ∀ y : atom, y ∉ L → ∀ T2, _ ⊢ₑ (e2 ^^ y) ⋮ T2 → _ = T2,
      Hopen : ∀ y : atom, y ∉ L0 → _ ⊢ₑ (e2 ^^ y) ⋮ _ |- _ =>
        specialize (IH x ltac:(set_solver));
        eapply IH; eapply Hopen; set_solver
    end.
	  - rewrite e in H2. simplify_eq. reflexivity.
  - match goal with
    | H1 : bin_op_type ?op = _, H2 : bin_op_type ?op = _ |- _ =>
        rewrite H1 in H2; simplify_eq; reflexivity
    end.
			  - match goal with
		    | IH : ∀ T2, Γ ⊢ᵥ v1 ⋮ T2 → TArrow _ _ = T2,
      Hfun : Γ ⊢ᵥ v1 ⋮ TArrow _ _ |- _ =>
        specialize (IH _ Hfun); simplify_eq; reflexivity
    end.
Qed.

Lemma basic_typing_unique_tm Γ e T1 T2 :
  Γ ⊢ₑ e ⋮ T1 → Γ ⊢ₑ e ⋮ T2 → T1 = T2.
Proof.
  intros Hty.
  revert T2.
  induction Hty using tm_has_type_mut with
      (P := fun Γ v T1 _ => ∀ T2, Γ ⊢ᵥ v ⋮ T2 → T1 = T2);
      intros T2' Hother; inversion Hother; subst; eauto.
  - simplify_eq. reflexivity.
  - f_equal.
    pose (x := fresh_for (L ∪ L0)).
    assert (Hx : x ∉ L ∪ L0) by (subst x; apply fresh_for_not_in).
    specialize (H x ltac:(set_solver)).
    eapply H.
    match goal with
    | Hopen : ∀ y : atom, y ∉ L0 → <[y:=s]> Γ ⊢ₑ e ^^ y ⋮ _ |- _ =>
        eapply Hopen; set_solver
    end.
  - pose (x := fresh_for (L ∪ L0)).
    assert (Hx : x ∉ L ∪ L0) by (subst x; apply fresh_for_not_in).
    assert (T1 = T0) by eauto. subst T0.
    match goal with
    | IH : ∀ y : atom, y ∉ L → ∀ T2, _ ⊢ₑ (e2 ^^ y) ⋮ T2 → _ = T2,
      Hopen : ∀ y : atom, y ∉ L0 → _ ⊢ₑ (e2 ^^ y) ⋮ _ |- _ =>
        specialize (IH x ltac:(set_solver));
        eapply IH; eapply Hopen; set_solver
    end.
  - rewrite e in H2. simplify_eq. reflexivity.
  - match goal with
    | H1 : bin_op_type ?op = _, H2 : bin_op_type ?op = _ |- _ =>
        rewrite H1 in H2; simplify_eq; reflexivity
    end.
  - match goal with
    | IH : ∀ T2, Γ ⊢ᵥ v1 ⋮ T2 → TArrow _ _ = T2,
      Hfun : Γ ⊢ᵥ v1 ⋮ TArrow _ _ |- _ =>
        specialize (IH _ Hfun); simplify_eq; reflexivity
    end.
Qed.

Lemma basic_typing_strengthen_value Γ x Tx v T :
  <[x := Tx]> Γ ⊢ᵥ v ⋮ T →
  x ∉ fv_value v →
  Γ ⊢ᵥ v ⋮ T.
Proof.
  intros Hty Hfresh.
  remember (<[x := Tx]> Γ) as Γx.
  revert Γ HeqΓx Hfresh.
  induction Hty using value_has_type_mut with
      (P0 := fun Γx e T _ =>
        ∀ Γ, Γx = <[x := Tx]> Γ → x ∉ fv_tm e → Γ ⊢ₑ e ⋮ T);
      intros Γ0 Heq Hfresh; subst; simpl in Hfresh; eauto.
  - econstructor.
    rewrite lookup_insert_ne in e by set_solver.
    exact e.
  - apply VT_Lam with (L := L ∪ {[x]}). intros y Hy.
    eapply H; [set_solver | |].
    + rewrite insert_insert_ne by set_solver. reflexivity.
    + pose proof (open_fv_tm e (vfvar y) 0) as Hfv.
      simpl in Hfv. set_solver.
  - apply VT_Fix with (L := L ∪ {[x]}). intros y Hy.
    eapply H; [set_solver | |].
    + rewrite insert_insert_ne by set_solver. reflexivity.
    + pose proof (open_fv_value vf (vfvar y) 0) as Hfv.
      simpl in Hfv. set_solver.
  - eapply TT_Let with (T1 := T1) (L := L ∪ {[x]}).
    + match goal with
      | IH : ∀ Γ, _ = <[x:=Tx]> Γ → x ∉ fv_tm e1 → Γ ⊢ₑ e1 ⋮ _ |- _ =>
          eapply IH; [reflexivity | set_solver]
      end.
    + intros y Hy.
    match goal with
    | IH : ∀ y : atom, y ∉ _ → ∀ Γ, _ = <[x:=Tx]> Γ → x ∉ fv_tm (e2 ^^ y) → Γ ⊢ₑ e2 ^^ y ⋮ _ |- _ =>
        eapply IH; [set_solver | |]
    end.
	    * rewrite insert_insert_ne by set_solver. reflexivity.
	    * pose proof (open_fv_tm e2 (vfvar y) 0) as Hfv.
	      simpl in Hfv. set_solver.
  - eapply TT_BinOp; [eassumption| |];
      match goal with
      | IH : ∀ Γ, _ = <[x:=Tx]> Γ → x ∉ fv_value _ → Γ ⊢ᵥ _ ⋮ _ |- _ =>
          eapply IH; [reflexivity | set_solver]
      end.
  - eapply TT_App;
      match goal with
      | IH : ∀ Γ, _ = <[x:=Tx]> Γ → x ∉ fv_value _ → Γ ⊢ᵥ _ ⋮ _ |- _ =>
          eapply IH; [reflexivity | set_solver]
      end.
  - eapply TT_Match.
    + match goal with
      | IH : ∀ Γ, _ = <[x:=Tx]> Γ → x ∉ fv_value _ → Γ ⊢ᵥ _ ⋮ _ |- _ =>
          eapply IH; [reflexivity | set_solver]
      end.
    + match goal with
      | IH : ∀ Γ, _ = <[x:=Tx]> Γ → x ∉ fv_tm _ → Γ ⊢ₑ _ ⋮ _ |- _ =>
          eapply IH; [reflexivity | set_solver]
      end.
    + match goal with
      | IH : ∀ Γ, _ = <[x:=Tx]> Γ → x ∉ fv_tm _ → Γ ⊢ₑ _ ⋮ _ |- _ =>
          eapply IH; [reflexivity | set_solver]
      end.
  - econstructor.
    + match goal with
      | IH : ∀ Γ, _ = <[x:=Tx]> Γ → x ∉ fv_value root → Γ ⊢ᵥ root ⋮ _ |- _ =>
          eapply IH; [reflexivity | set_solver]
      end.
    + match goal with
      | IH : ∀ Γ, _ = <[x:=Tx]> Γ → x ∉ fv_value left → Γ ⊢ᵥ left ⋮ _ |- _ =>
          eapply IH; [reflexivity | set_solver]
      end.
    + match goal with
      | IH : ∀ Γ, _ = <[x:=Tx]> Γ → x ∉ fv_value right → Γ ⊢ᵥ right ⋮ _ |- _ =>
          eapply IH; [reflexivity | set_solver]
      end.
  - eapply TT_TreeMatch with (L := L ∪ {[x]}).
    + match goal with
      | IH : ∀ Γ, _ = <[x:=Tx]> Γ → x ∉ fv_value v → Γ ⊢ᵥ v ⋮ _ |- _ =>
          eapply IH; [reflexivity | set_solver]
      end.
    + match goal with
      | IH : ∀ Γ, _ = <[x:=Tx]> Γ → x ∉ fv_tm eleaf → Γ ⊢ₑ eleaf ⋮ _ |- _ =>
          eapply IH; [reflexivity | set_solver]
      end.
    + intros root left right Hroot Hleft Hright.
	      match goal with
	      | IH : ∀ root left right : atom,
	          root ∉ L →
	          left ∉ L ∪ {[root]} →
	          right ∉ L ∪ {[root]} ∪ {[left]} →
	          ∀ Γ, _ = <[x:=Tx]> Γ →
	            x ∉ fv_tm (open_tree_node_branch root left right enode) →
	            Γ ⊢ₑ open_tree_node_branch root left right enode ⋮ _ |- _ =>
	          eapply IH; [set_solver | set_solver | set_solver | |]
      end.
      * apply insert_tree_branch_subst_commute; set_solver.
	      * unfold open_tree_node_branch, open_tree_node_branch_value.
	        pose proof (open_fv_tm enode (vfvar root) 0) as Hopen_root.
	        pose proof (open_fv_tm
	          (open_tm 0 (vfvar root) enode) (vfvar left) 1) as Hopen_left.
	        pose proof (open_fv_tm
	          (open_tm 1 (vfvar left) (open_tm 0 (vfvar root) enode))
	          (vfvar right) 2) as Hopen_right.
	        simpl in Hopen_root, Hopen_left, Hopen_right.
	        set_solver.
  - econstructor.
    + match goal with
      | IH : ∀ Γ, _ = <[x:=Tx]> Γ → x ∉ fv_value hd → Γ ⊢ᵥ hd ⋮ _ |- _ =>
          eapply IH; [reflexivity | set_solver]
      end.
    + match goal with
      | IH : ∀ Γ, _ = <[x:=Tx]> Γ → x ∉ fv_value tl → Γ ⊢ᵥ tl ⋮ _ |- _ =>
          eapply IH; [reflexivity | set_solver]
      end.
  - eapply TT_ListMatch with (L := L ∪ {[x]}).
    + match goal with
      | IH : ∀ Γ, _ = <[x:=Tx]> Γ → x ∉ fv_value v → Γ ⊢ᵥ v ⋮ _ |- _ =>
          eapply IH; [reflexivity | set_solver]
      end.
    + match goal with
      | IH : ∀ Γ, _ = <[x:=Tx]> Γ → x ∉ fv_tm enil → Γ ⊢ₑ enil ⋮ _ |- _ =>
          eapply IH; [reflexivity | set_solver]
      end.
    + intros hd tl Hhd Htl.
      match goal with
      | IH : ∀ hd tl : atom,
          hd ∉ L →
          tl ∉ L ∪ {[hd]} →
          ∀ Γ, _ = <[x:=Tx]> Γ →
            x ∉ fv_tm (open_list_cons_branch hd tl econs) →
            Γ ⊢ₑ open_list_cons_branch hd tl econs ⋮ _ |- _ =>
          eapply IH; [set_solver | set_solver | |]
      end.
      * apply insert_list_branch_subst_commute; set_solver.
      * unfold open_list_cons_branch, open_list_cons_branch_value.
        pose proof (open_fv_tm econs (vfvar hd) 0) as Hopen_hd.
        pose proof (open_fv_tm
          (open_tm 0 (vfvar hd) econs) (vfvar tl) 1) as Hopen_tl.
        simpl in Hopen_hd, Hopen_tl.
        set_solver.
Qed.

Lemma basic_typing_strengthen_tm Γ x Tx e T :
  <[x := Tx]> Γ ⊢ₑ e ⋮ T →
  x ∉ fv_tm e →
  Γ ⊢ₑ e ⋮ T.
Proof.
  intros Hty Hfresh.
  remember (<[x := Tx]> Γ) as Γx.
  revert Γ HeqΓx Hfresh.
  induction Hty using tm_has_type_mut with
      (P := fun Γx v T _ =>
        ∀ Γ, Γx = <[x := Tx]> Γ → x ∉ fv_value v → Γ ⊢ᵥ v ⋮ T);
      intros Γ0 Heq Hfresh; subst; simpl in Hfresh; eauto.
  - econstructor.
    rewrite lookup_insert_ne in e by set_solver.
    exact e.
  - apply VT_Lam with (L := L ∪ {[x]}). intros y Hy.
    eapply H; [set_solver | |].
    + rewrite insert_insert_ne by set_solver. reflexivity.
    + pose proof (open_fv_tm e (vfvar y) 0) as Hfv.
      simpl in Hfv. set_solver.
  - apply VT_Fix with (L := L ∪ {[x]}). intros y Hy.
    eapply H; [set_solver | |].
    + rewrite insert_insert_ne by set_solver. reflexivity.
    + pose proof (open_fv_value vf (vfvar y) 0) as Hfv.
      simpl in Hfv. set_solver.
  - eapply TT_Let with (T1 := T1) (L := L ∪ {[x]}).
    + match goal with
      | IH : ∀ Γ, _ = <[x:=Tx]> Γ → x ∉ fv_tm e1 → Γ ⊢ₑ e1 ⋮ _ |- _ =>
          eapply IH; [reflexivity | set_solver]
      end.
    + intros y Hy.
    match goal with
    | IH : ∀ y : atom, y ∉ _ → ∀ Γ, _ = <[x:=Tx]> Γ → x ∉ fv_tm (e2 ^^ y) → Γ ⊢ₑ e2 ^^ y ⋮ _ |- _ =>
        eapply IH; [set_solver | |]
    end.
	    * rewrite insert_insert_ne by set_solver. reflexivity.
	    * pose proof (open_fv_tm e2 (vfvar y) 0) as Hfv.
	      simpl in Hfv. set_solver.
  - eapply TT_BinOp; [eassumption| |];
      match goal with
      | IH : ∀ Γ, _ = <[x:=Tx]> Γ → x ∉ fv_value _ → Γ ⊢ᵥ _ ⋮ _ |- _ =>
          eapply IH; [reflexivity | set_solver]
      end.
  - eapply TT_App;
      match goal with
      | IH : ∀ Γ, _ = <[x:=Tx]> Γ → x ∉ fv_value _ → Γ ⊢ᵥ _ ⋮ _ |- _ =>
          eapply IH; [reflexivity | set_solver]
      end.
  - eapply TT_Match.
    + match goal with
      | IH : ∀ Γ, _ = <[x:=Tx]> Γ → x ∉ fv_value _ → Γ ⊢ᵥ _ ⋮ _ |- _ =>
          eapply IH; [reflexivity | set_solver]
      end.
    + match goal with
      | IH : ∀ Γ, _ = <[x:=Tx]> Γ → x ∉ fv_tm _ → Γ ⊢ₑ _ ⋮ _ |- _ =>
          eapply IH; [reflexivity | set_solver]
      end.
    + match goal with
      | IH : ∀ Γ, _ = <[x:=Tx]> Γ → x ∉ fv_tm _ → Γ ⊢ₑ _ ⋮ _ |- _ =>
          eapply IH; [reflexivity | set_solver]
      end.
  - econstructor.
    + match goal with
      | IH : ∀ Γ, _ = <[x:=Tx]> Γ → x ∉ fv_value root → Γ ⊢ᵥ root ⋮ _ |- _ =>
          eapply IH; [reflexivity | set_solver]
      end.
    + match goal with
      | IH : ∀ Γ, _ = <[x:=Tx]> Γ → x ∉ fv_value left → Γ ⊢ᵥ left ⋮ _ |- _ =>
          eapply IH; [reflexivity | set_solver]
      end.
    + match goal with
      | IH : ∀ Γ, _ = <[x:=Tx]> Γ → x ∉ fv_value right → Γ ⊢ᵥ right ⋮ _ |- _ =>
          eapply IH; [reflexivity | set_solver]
      end.
  - eapply TT_TreeMatch with (L := L ∪ {[x]}).
    + match goal with
      | IH : ∀ Γ, _ = <[x:=Tx]> Γ → x ∉ fv_value v → Γ ⊢ᵥ v ⋮ _ |- _ =>
          eapply IH; [reflexivity | set_solver]
      end.
    + match goal with
      | IH : ∀ Γ, _ = <[x:=Tx]> Γ → x ∉ fv_tm eleaf → Γ ⊢ₑ eleaf ⋮ _ |- _ =>
          eapply IH; [reflexivity | set_solver]
      end.
    + intros root left right Hroot Hleft Hright.
	      match goal with
	      | IH : ∀ root left right : atom,
	          root ∉ L →
	          left ∉ L ∪ {[root]} →
	          right ∉ L ∪ {[root]} ∪ {[left]} →
	          ∀ Γ, _ = <[x:=Tx]> Γ →
	            x ∉ fv_tm (open_tree_node_branch root left right enode) →
	            Γ ⊢ₑ open_tree_node_branch root left right enode ⋮ _ |- _ =>
	          eapply IH; [set_solver | set_solver | set_solver | |]
      end.
      * apply insert_tree_branch_subst_commute; set_solver.
	      * unfold open_tree_node_branch, open_tree_node_branch_value.
	        pose proof (open_fv_tm enode (vfvar root) 0) as Hopen_root.
	        pose proof (open_fv_tm
	          (open_tm 0 (vfvar root) enode) (vfvar left) 1) as Hopen_left.
	        pose proof (open_fv_tm
	          (open_tm 1 (vfvar left) (open_tm 0 (vfvar root) enode))
	          (vfvar right) 2) as Hopen_right.
	        simpl in Hopen_root, Hopen_left, Hopen_right.
	        set_solver.
  - econstructor.
    + match goal with
      | IH : ∀ Γ, _ = <[x:=Tx]> Γ → x ∉ fv_value hd → Γ ⊢ᵥ hd ⋮ _ |- _ =>
          eapply IH; [reflexivity | set_solver]
      end.
    + match goal with
      | IH : ∀ Γ, _ = <[x:=Tx]> Γ → x ∉ fv_value tl → Γ ⊢ᵥ tl ⋮ _ |- _ =>
          eapply IH; [reflexivity | set_solver]
      end.
  - eapply TT_ListMatch with (L := L ∪ {[x]}).
    + match goal with
      | IH : ∀ Γ, _ = <[x:=Tx]> Γ → x ∉ fv_value v → Γ ⊢ᵥ v ⋮ _ |- _ =>
          eapply IH; [reflexivity | set_solver]
      end.
    + match goal with
      | IH : ∀ Γ, _ = <[x:=Tx]> Γ → x ∉ fv_tm enil → Γ ⊢ₑ enil ⋮ _ |- _ =>
          eapply IH; [reflexivity | set_solver]
      end.
    + intros hd tl Hhd Htl.
      match goal with
      | IH : ∀ hd tl : atom,
          hd ∉ L →
          tl ∉ L ∪ {[hd]} →
          ∀ Γ, _ = <[x:=Tx]> Γ →
            x ∉ fv_tm (open_list_cons_branch hd tl econs) →
            Γ ⊢ₑ open_list_cons_branch hd tl econs ⋮ _ |- _ =>
          eapply IH; [set_solver | set_solver | |]
      end.
      * apply insert_list_branch_subst_commute; set_solver.
      * unfold open_list_cons_branch, open_list_cons_branch_value.
        pose proof (open_fv_tm econs (vfvar hd) 0) as Hopen_hd.
        pose proof (open_fv_tm
          (open_tm 0 (vfvar hd) econs) (vfvar tl) 1) as Hopen_tl.
        simpl in Hopen_hd, Hopen_tl.
        set_solver.
Qed.
