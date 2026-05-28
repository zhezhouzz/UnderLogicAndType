(** * ContextTypeLanguage.SyntaxLvars

    Lvar support computations for context syntax. *)

From ContextTypeLanguage Require Export SyntaxCore.

Lemma lvars_at_depth_elem d D u :
  u ∈ lvars_at_depth d D <->
  exists v, v ∈ D /\ logic_var_at_depth d v = Some u.
Proof.
  unfold lvars_at_depth.
  refine (set_fold_ind_L
    (fun acc D => forall u, u ∈ acc <->
      exists v, v ∈ D /\ logic_var_at_depth d v = Some u)
    (fun v acc =>
      match logic_var_at_depth d v with
      | Some u => {[u]} ∪ acc
      | None => acc
      end) ∅ _ _ D u).
  - intros y. set_solver.
  - intros v D' acc Hfresh IH z.
    destruct (logic_var_at_depth d v) as [a|] eqn:Hv.
    + pose proof (IH z) as Hz. split.
      * intros Hx.
        apply elem_of_union in Hx as [Hx|Hx].
        -- apply elem_of_singleton in Hx. subst z.
           exists v. split; [set_solver | exact Hv].
        -- apply Hz in Hx as [w [Hw Hwx]].
           exists w. split; [set_solver | exact Hwx].
      * intros [w [Hw Hwx]].
        apply elem_of_union.
        apply elem_of_union in Hw as [Hw|Hw].
        -- apply elem_of_singleton in Hw. subst w.
           rewrite Hv in Hwx. inversion Hwx. subst z.
           left. set_solver.
        -- right. apply Hz. exists w. split; [exact Hw | exact Hwx].
    + pose proof (IH z) as Hz. split.
      * intros Hx.
        apply Hz in Hx as [w [Hw Hwx]].
        exists w. split; [set_solver | exact Hwx].
      * intros [w [Hw Hwx]].
        apply elem_of_union in Hw as [Hw|Hw].
        -- apply elem_of_singleton in Hw. subst w.
           rewrite Hv in Hwx. discriminate.
        -- apply Hz. exists w. split; [exact Hw | exact Hwx].
Qed.

Lemma lvars_at_depth_0 D :
  lvars_at_depth 0 D = D.
Proof.
  apply set_eq. intros u.
  rewrite lvars_at_depth_elem.
  split.
  - intros [v [Hv Hvu]].
    destruct v as [n|x]; cbn [logic_var_at_depth] in Hvu.
    + destruct (decide (0 <= n)); inversion Hvu. subst u.
      replace (n - 0) with n by lia. exact Hv.
    + inversion Hvu. subst u. exact Hv.
  - intros Hu.
    exists u. split; [exact Hu|].
    destruct u as [n|x]; cbn [logic_var_at_depth].
    + rewrite decide_True by lia. replace (n - 0) with n by lia. reflexivity.
    + reflexivity.
Qed.

Lemma lvars_at_depth_empty d :
  lvars_at_depth d ∅ = ∅.
Proof.
  apply set_eq. intros u. rewrite lvars_at_depth_elem. set_solver.
Qed.

Lemma lvars_at_depth_union d D E :
  lvars_at_depth d (D ∪ E) =
  lvars_at_depth d D ∪ lvars_at_depth d E.
Proof.
  apply set_eq. intros u.
  rewrite elem_of_union, !lvars_at_depth_elem.
  split.
  - intros [v [Hv Hvu]].
    apply elem_of_union in Hv as [Hv|Hv].
    + left. exists v. split; [exact Hv | exact Hvu].
    + right. exists v. split; [exact Hv | exact Hvu].
  - intros Hu.
    destruct Hu as [[v [Hv Hvu]]|[v [Hv Hvu]]].
    + exists v. split; [set_solver | exact Hvu].
    + exists v. split; [set_solver | exact Hvu].
Qed.

Lemma lvars_at_depth_singleton_free d x :
  lvars_at_depth d ({[LVFree x]} : lvset) = {[LVFree x]}.
Proof.
  apply set_eq. intros u. rewrite lvars_at_depth_elem.
  split.
  - intros [v [Hv Hvu]].
    rewrite elem_of_singleton in Hv. subst v.
    inversion Hvu. subst u. set_solver.
  - intros Hu.
    rewrite elem_of_singleton in Hu. subst u.
    exists (LVFree x). split; [set_solver | reflexivity].
Qed.

Lemma lvars_at_depth_singleton_bound0_succ d :
  lvars_at_depth (S d) ({[LVBound 0]} : lvset) = ∅.
Proof.
  apply set_eq. intros u.
  rewrite lvars_at_depth_elem.
  split.
  - intros [v [Hv Hvu]].
    rewrite elem_of_singleton in Hv. subst v.
    cbn [logic_var_at_depth] in Hvu.
    destruct (decide (S d <= 0)); [lia|discriminate].
  - set_solver.
Qed.

Lemma lvars_at_depth_mono d D E :
  D ⊆ E ->
  lvars_at_depth d D ⊆ lvars_at_depth d E.
Proof.
  intros Hsub u Hu.
  apply lvars_at_depth_elem in Hu as [v [Hv Hvu]].
  apply lvars_at_depth_elem.
  exists v. split; [set_solver | exact Hvu].
Qed.

Lemma lvars_at_depth_difference_subset d D E :
  lvars_at_depth d (D ∖ E) ⊆ lvars_at_depth d D.
Proof.
  apply lvars_at_depth_mono. set_solver.
Qed.

Lemma logic_var_at_depth_open d k x v :
  logic_var_at_depth d (logic_var_open (d + k) x v) =
  option_map (logic_var_open k x) (logic_var_at_depth d v).
Proof.
  destruct v as [n|y]; cbn [logic_var_at_depth option_map].
  - destruct (decide (d + k = n)) as [Heq|Hneq].
    + subst n.
      unfold swap.
      destruct (decide (LVBound (d + k) = LVBound (d + k))) as [_|Hbad];
        [|congruence].
      cbn [logic_var_at_depth].
      destruct (decide (d <= d + k)) as [_|Hbad]; [|lia].
      cbn [option_map].
      unfold swap.
      replace (d + k - d) with k by lia.
      destruct (decide (LVBound k = LVBound k)) as [_|Hbad]; [reflexivity|congruence].
    + unfold swap.
      destruct (decide (LVBound n = LVBound (d + k))) as [Heq|_];
        [inversion Heq; lia|].
      destruct (decide (LVBound n = LVFree x)) as [Hbad|_]; [discriminate|].
      cbn [logic_var_at_depth].
      destruct (decide (d <= n)) as [Hdn|Hdn].
      * cbn [option_map].
        unfold swap.
        destruct (decide (LVBound (n - d) = LVBound k)) as [Heq|_].
        -- inversion Heq. lia.
        -- destruct (decide (LVBound (n - d) = LVFree x)) as [Hbad|_];
             [discriminate|reflexivity].
      * reflexivity.
  - destruct (decide (x = y)) as [->|Hxy].
    + unfold swap.
      destruct (decide (LVFree y = LVBound (d + k))) as [Hbad|_];
        [discriminate|].
      destruct (decide (LVFree y = LVFree y)) as [_|Hbad]; [|congruence].
      cbn [logic_var_at_depth option_map].
      destruct (decide (d <= d + k)) as [_|Hbad]; [|lia].
      unfold swap.
      replace (d + k - d) with k by lia.
      destruct (decide (LVFree y = LVBound k)) as [Hbad|_]; [discriminate|].
      destruct (decide (LVFree y = LVFree y)) as [_|Hbad]; [reflexivity|congruence].
    + unfold swap.
      destruct (decide (LVFree y = LVBound (d + k))) as [Hbad|_];
        [discriminate|].
      destruct (decide (LVFree y = LVFree x)) as [Heq|_];
        [inversion Heq; congruence|].
      cbn [logic_var_at_depth option_map].
      unfold swap.
      destruct (decide (LVFree y = LVBound k)) as [Hbad|_]; [discriminate|].
      destruct (decide (LVFree y = LVFree x)) as [Heq|_];
        [inversion Heq; congruence|reflexivity].
Qed.

Lemma lvars_at_depth_open d k x D :
  lvars_at_depth d (lvars_open (d + k) x D) =
  lvars_open k x (lvars_at_depth d D).
Proof.
  apply set_eq. intros u.
  split.
  - intros Hu.
    apply lvars_at_depth_elem in Hu as [v [Hv Hvu]].
    apply elem_of_set_swap in Hv.
    change (swap (LVBound (d + k)) (LVFree x) v ∈ D) with
      (logic_var_open (d + k) x v ∈ D) in Hv.
apply elem_of_set_swap.
    change (swap (LVBound k) (LVFree x) u ∈ lvars_at_depth d D) with
      (logic_var_open k x u ∈ lvars_at_depth d D).
    apply lvars_at_depth_elem. exists (logic_var_open (d + k) x v).
    split; [exact Hv|].
    rewrite logic_var_at_depth_open, Hvu. reflexivity.
  - intros Hu.
    apply elem_of_set_swap in Hu.
    change (swap (LVBound k) (LVFree x) u ∈ lvars_at_depth d D) with
      (logic_var_open k x u ∈ lvars_at_depth d D) in Hu.
    apply lvars_at_depth_elem in Hu as [v [Hv Hvu]].
    apply lvars_at_depth_elem.
    exists (logic_var_open (d + k) x v).
    split.
    + apply elem_of_set_swap.
      change (swap (LVBound (d + k)) (LVFree x)
        (logic_var_open (d + k) x v) ∈ D) with
        (logic_var_open (d + k) x (logic_var_open (d + k) x v) ∈ D).
      rewrite logic_var_open_involutive. exact Hv.
    + rewrite logic_var_at_depth_open, Hvu.
      cbn [option_map]. rewrite logic_var_open_involutive. reflexivity.
Qed.

Lemma context_ty_lvars_at_open d k x τ :
  context_ty_lvars_at d ({d + k ~> x} τ) =
  lvars_open k x (context_ty_lvars_at d τ).
Proof.
  induction τ in d, k |- *; cbn [context_ty_lvars_at].
  - change ({d + k ~> x} CTOver b φ) with (cty_open (d + k) x (CTOver b φ)).
    cbn [cty_open context_ty_lvars_at].
    replace (S (d + k)) with (S d + k) by lia.
    rewrite qual_open_atom_vars.
    apply lvars_at_depth_open.
  - change ({d + k ~> x} CTUnder b φ) with (cty_open (d + k) x (CTUnder b φ)).
    cbn [cty_open context_ty_lvars_at].
    replace (S (d + k)) with (S d + k) by lia.
    rewrite qual_open_atom_vars.
    apply lvars_at_depth_open.
  - change ({d + k ~> x} CTInter τ1 τ2) with
      (cty_open (d + k) x (CTInter τ1 τ2)).
    cbn [cty_open context_ty_lvars_at].
    rewrite IHτ1, IHτ2.
    symmetry. rewrite set_swap_union. reflexivity.
  - change ({d + k ~> x} CTUnion τ1 τ2) with
      (cty_open (d + k) x (CTUnion τ1 τ2)).
    cbn [cty_open context_ty_lvars_at].
    rewrite IHτ1, IHτ2.
    symmetry. rewrite set_swap_union. reflexivity.
  - change ({d + k ~> x} CTSum τ1 τ2) with
      (cty_open (d + k) x (CTSum τ1 τ2)).
    cbn [cty_open context_ty_lvars_at].
    rewrite IHτ1, IHτ2.
    symmetry. rewrite set_swap_union. reflexivity.
  - change ({d + k ~> x} CTArrow τ1 τ2) with
      (cty_open (d + k) x (CTArrow τ1 τ2)).
    cbn [cty_open context_ty_lvars_at].
    rewrite IHτ1.
    replace (S (d + k)) with (S d + k) by lia.
    rewrite IHτ2.
    symmetry. rewrite set_swap_union. reflexivity.
  - change ({d + k ~> x} CTWand τ1 τ2) with
      (cty_open (d + k) x (CTWand τ1 τ2)).
    cbn [cty_open context_ty_lvars_at].
    rewrite IHτ1.
    replace (S (d + k)) with (S d + k) by lia.
    rewrite IHτ2.
    symmetry. rewrite set_swap_union. reflexivity.
Qed.

Lemma cty_open_vars k x τ :
  context_ty_lvars ({k ~> x} τ) = context_ty_open_lvars k x τ.
Proof.
  unfold context_ty_lvars, context_ty_open_lvars.
  replace k with (0 + k) at 1 by lia.
  apply context_ty_lvars_at_open.
Qed.

Lemma lvars_fv_lvars_at_depth d D :
  lvars_fv (lvars_at_depth d D) = lvars_fv D.
Proof.
  apply set_eq. intros x.
  rewrite !lvars_fv_elem, lvars_at_depth_elem.
  split.
  - intros [v [Hv Hdepth]].
    destruct v as [k|y]; cbn [logic_var_at_depth] in Hdepth.
    + destruct (decide (d <= k)); discriminate.
    + inversion Hdepth. subst. exact Hv.
  - intros Hx.
    exists (LVFree x). split; [exact Hx | reflexivity].
Qed.

Lemma context_ty_lvars_fv_at d τ :
  lvars_fv (context_ty_lvars_at d τ) = fv_cty τ.
Proof.
  induction τ in d |- *; unfold fv_cty, context_ty_lvars in *;
    cbn [context_ty_lvars_at] in *.
  - rewrite lvars_fv_lvars_at_depth, lvars_fv_lvars_at_depth. reflexivity.
  - rewrite lvars_fv_lvars_at_depth, lvars_fv_lvars_at_depth. reflexivity.
  - rewrite !lvars_fv_union, IHτ1, IHτ2. reflexivity.
  - rewrite !lvars_fv_union, IHτ1, IHτ2. reflexivity.
  - rewrite !lvars_fv_union, IHτ1, IHτ2. reflexivity.
  - rewrite !lvars_fv_union, IHτ1, (IHτ2 (S d)), <- (IHτ2 1). reflexivity.
  - rewrite !lvars_fv_union, IHτ1, (IHτ2 (S d)), <- (IHτ2 1). reflexivity.
Qed.

Lemma context_ty_lvars_fv τ :
  lvars_fv (context_ty_lvars τ) = fv_cty τ.
Proof.
  apply context_ty_lvars_fv_at.
Qed.

Lemma context_ty_lvars_over_fv b q :
  lvars_fv (context_ty_lvars (CTOver b q)) = qual_dom q.
Proof.
  cbn [context_ty_lvars context_ty_lvars_at].
  rewrite lvars_fv_lvars_at_depth. reflexivity.
Qed.

Lemma context_ty_lvars_under_fv b q :
  lvars_fv (context_ty_lvars (CTUnder b q)) = qual_dom q.
Proof.
  cbn [context_ty_lvars context_ty_lvars_at].
  rewrite lvars_fv_lvars_at_depth. reflexivity.
Qed.

Lemma context_ty_over_fresh_open_qual_dom x y b q :
  LVFree x ∉ context_ty_lvars (CTOver b q) ->
  x <> y ->
  x ∉ qual_dom (q ^q^ y).
Proof.
  intros Hx Hxy.
  apply qual_open_atom_dom_fresh_ne; [|exact Hxy].
  intros Hbad. apply Hx. apply lvars_fv_elem.
  rewrite context_ty_lvars_over_fv. exact Hbad.
Qed.

Lemma context_ty_under_fresh_open_qual_dom x y b q :
  LVFree x ∉ context_ty_lvars (CTUnder b q) ->
  x <> y ->
  x ∉ qual_dom (q ^q^ y).
Proof.
  intros Hx Hxy.
  apply qual_open_atom_dom_fresh_ne; [|exact Hxy].
  intros Hbad. apply Hx. apply lvars_fv_elem.
  rewrite context_ty_lvars_under_fv. exact Hbad.
Qed.

Lemma lvars_at_depth_succ_body d D :
  lvars_at_depth d D ⊆
  lvars_shift_from 0 (lvars_at_depth (S d) D) ∪ {[LVBound 0]}.
Proof.
  intros u Hu.
  apply lvars_at_depth_elem in Hu as [v [Hv Hdepth]].
  destruct v as [n|x]; cbn [logic_var_at_depth] in Hdepth.
  - destruct (decide (d <= n)) as [Hdn|Hdn]; [|discriminate].
    inversion Hdepth; subst u.
    destruct (decide (S d <= n)) as [Hsdn|Hsdn].
    + apply elem_of_union_l.
      unfold lvars_shift_from. apply elem_of_map.
      exists (LVBound (n - S d)). split.
      * cbn [logic_var_shift_from].
        destruct (decide (0 <= n - S d)) as [_|Hbad]; [|lia].
        f_equal. lia.
      * apply lvars_at_depth_elem.
        exists (LVBound n). split; [exact Hv |].
        cbn [logic_var_at_depth].
        destruct (decide (S d <= n)) as [_|Hbad]; [reflexivity | lia].
    + apply elem_of_union_r.
      assert (n = d) by lia. subst n.
      replace (d - d) with 0 by lia.
      apply elem_of_singleton. reflexivity.
  - inversion Hdepth; subst u.
    apply elem_of_union_l.
    unfold lvars_shift_from. apply elem_of_map.
    exists (LVFree x). split; [reflexivity |].
    apply lvars_at_depth_elem.
    exists (LVFree x). split; [exact Hv | reflexivity].
Qed.

Lemma lvars_bv_at_depth_succ_empty_of_open0 x D :
  lvars_bv (lvars_open 0 x D) = ∅ ->
  lvars_bv (lvars_at_depth 1 D) = ∅.
Proof.
  intros Hopen.
  apply set_eq. intros n.
  rewrite elem_of_empty.
  split; [|set_solver].
  intros Hn.
  rewrite lvars_bv_elem in Hn.
  apply lvars_at_depth_elem in Hn as [v [Hv Hdepth]].
  destruct v as [m|y]; cbn [logic_var_at_depth] in Hdepth; [|discriminate].
  destruct (decide (1 <= m)) as [Hm|Hm]; [|discriminate].
  inversion Hdepth. subst n.
  assert (LVBound m ∈ lvars_open 0 x D) as Hopened.
  {
unfold set_swap.
    apply elem_of_map. exists (LVBound m). split; [|exact Hv].
    symmetry. apply swap_fresh.
    - intros Heq. inversion Heq. lia.
    - discriminate.
  }
  assert (m ∈ lvars_bv (lvars_open 0 x D)).
  { rewrite lvars_bv_elem. exact Hopened. }
  change (lvars_bv (set_swap (LVBound 0) (LVFree x) D) = ∅) in Hopen.
  change (m ∈ lvars_bv (set_swap (LVBound 0) (LVFree x) D)) in H.
  rewrite Hopen in H. set_solver.
Qed.

Lemma logic_var_at_depth_shift_from d k v :
  logic_var_at_depth d (logic_var_shift_from (d + k) v) =
  option_map (logic_var_shift_from k) (logic_var_at_depth d v).
Proof.
  destruct v as [n|x]; cbn [logic_var_shift_from logic_var_at_depth].
  - destruct (decide (d <= n)) as [Hdn|Hdn].
    + destruct (decide (d + k <= n)) as [Hdkn|Hdkn].
      * destruct (decide (d <= S n)) as [_|Hbad]; [|lia].
        cbn [option_map logic_var_shift_from].
        destruct (decide (k <= n - d)) as [_|Hbad]; [|lia].
        cbn [logic_var_at_depth].
        destruct (decide (d <= S n)) as [_|Hbad]; [|lia].
        replace (S n - d) with (S (n - d)) by lia.
        reflexivity.
      * destruct (decide (d <= n)) as [_|Hbad]; [|lia].
        cbn [option_map logic_var_shift_from].
        destruct (decide (k <= n - d)) as [Hbad|_]; [lia|].
        cbn [logic_var_at_depth].
        destruct (decide (d <= n)) as [_|Hbad]; [reflexivity|lia].
    + destruct (decide (d + k <= n)) as [Hdkn|_]; [lia|].
      destruct (decide (d <= n)) as [Hbad|_]; [lia|].
      cbn [logic_var_at_depth option_map].
      destruct (decide (d <= n)) as [Hbad|_]; [lia|reflexivity].
  - reflexivity.
Qed.

Lemma lvars_at_depth_shift_from d k D :
  lvars_at_depth d (lvars_shift_from (d + k) D) =
  lvars_shift_from k (lvars_at_depth d D).
Proof.
  apply set_eq. intros u.
  split.
  - intros Hu.
    apply lvars_at_depth_elem in Hu as [v [Hv Hvu]].
    unfold lvars_shift_from in Hv.
    apply elem_of_map in Hv as [w [-> Hw]].
    rewrite logic_var_at_depth_shift_from in Hvu.
    destruct (logic_var_at_depth d w) as [w'|] eqn:Hw'; [|discriminate].
    inversion Hvu. subst u.
    unfold lvars_shift_from. apply elem_of_map.
    exists w'. split; [reflexivity|].
    apply lvars_at_depth_elem. exists w. split; [exact Hw|exact Hw'].
  - intros Hu.
    unfold lvars_shift_from in Hu.
    apply elem_of_map in Hu as [v [-> Hv]].
    apply lvars_at_depth_elem in Hv as [w [Hw Hwv]].
    apply lvars_at_depth_elem.
    exists (logic_var_shift_from (d + k) w). split.
    + unfold lvars_shift_from. apply elem_of_map. exists w.
      split; [reflexivity|exact Hw].
    + rewrite logic_var_at_depth_shift_from, Hwv. reflexivity.
Qed.

Lemma logic_var_at_depth_shift_under d k v :
  k <= d ->
  logic_var_at_depth (S d) (logic_var_shift_from k v) =
  logic_var_at_depth d v.
Proof.
  intros Hkd.
  destruct v as [n|x]; cbn [logic_var_shift_from logic_var_at_depth].
  - destruct (decide (k <= n)) as [Hkn|Hkn].
    + cbn [logic_var_at_depth].
      destruct (decide (S d <= S n)) as [Hsdn|Hsdn].
      * destruct (decide (d <= n)) as [_|Hbad]; [|lia].
        replace (S n - S d) with (n - d) by lia. reflexivity.
      * destruct (decide (d <= n)) as [Hbad|_]; [lia|reflexivity].
    + cbn [logic_var_at_depth].
      destruct (decide (S d <= n)) as [Hsdn|Hsdn].
      * lia.
      * destruct (decide (d <= n)) as [Hdn|Hdn].
        -- assert (n = d) by lia. subst n. lia.
        -- reflexivity.
  - reflexivity.
Qed.

Lemma lvars_at_depth_shift_under d k D :
  k <= d ->
  lvars_at_depth (S d) (lvars_shift_from k D) =
  lvars_at_depth d D.
Proof.
  intros Hkd. apply set_eq. intros u.
  split.
  - intros Hu.
    apply lvars_at_depth_elem in Hu as [v [Hv Hvu]].
    unfold lvars_shift_from in Hv.
    apply elem_of_map in Hv as [w [-> Hw]].
    rewrite logic_var_at_depth_shift_under in Hvu by exact Hkd.
    apply lvars_at_depth_elem. exists w. split; [exact Hw | exact Hvu].
  - intros Hu.
    apply lvars_at_depth_elem in Hu as [v [Hv Hvu]].
    apply lvars_at_depth_elem.
    exists (logic_var_shift_from k v). split.
    + unfold lvars_shift_from. apply elem_of_map. exists v.
      split; [reflexivity | exact Hv].
    + rewrite logic_var_at_depth_shift_under by exact Hkd. exact Hvu.
Qed.

Lemma context_ty_lvars_at_shift_under d k τ :
  k <= d ->
  context_ty_lvars_at (S d) (cty_shift k τ) =
  context_ty_lvars_at d τ.
Proof.
  induction τ in d, k |- *; cbn [context_ty_lvars_at cty_shift]; intros Hkd.
  - rewrite qual_shift_from_vars.
    apply lvars_at_depth_shift_under. lia.
  - rewrite qual_shift_from_vars.
    apply lvars_at_depth_shift_under. lia.
  - rewrite IHτ1, IHτ2 by exact Hkd. reflexivity.
  - rewrite IHτ1, IHτ2 by exact Hkd. reflexivity.
  - rewrite IHτ1, IHτ2 by exact Hkd. reflexivity.
  - rewrite IHτ1 by exact Hkd.
    rewrite IHτ2 by lia. reflexivity.
  - rewrite IHτ1 by exact Hkd.
    rewrite IHτ2 by lia. reflexivity.
Qed.

Lemma lvars_shift_from_succ_body_union D1 D1' D2 D2' :
  D1 ⊆ lvars_shift_from 0 D1' ∪ {[LVBound 0]} ->
  D2 ⊆ lvars_shift_from 0 D2' ∪ {[LVBound 0]} ->
  D1 ∪ D2 ⊆ lvars_shift_from 0 (D1' ∪ D2') ∪ {[LVBound 0]}.
Proof.
  intros H1 H2 u Hu.
  apply elem_of_union in Hu as [Hu | Hu].
  - specialize (H1 u Hu).
    apply elem_of_union in H1 as [Hshift | Hzero].
    + apply elem_of_union_l.
      eapply lvars_shift_from_mono; [|exact Hshift]. set_solver.
    + apply elem_of_union_r. exact Hzero.
  - specialize (H2 u Hu).
    apply elem_of_union in H2 as [Hshift | Hzero].
    + apply elem_of_union_l.
      eapply lvars_shift_from_mono; [|exact Hshift]. set_solver.
    + apply elem_of_union_r. exact Hzero.
Qed.

Lemma context_ty_lvars_at_succ_body d τ :
  context_ty_lvars_at d τ ⊆
  lvars_shift_from 0 (context_ty_lvars_at (S d) τ) ∪ {[LVBound 0]}.
Proof.
  induction τ in d |- *; cbn [context_ty_lvars_at].
  - apply lvars_at_depth_succ_body.
  - apply lvars_at_depth_succ_body.
  - eapply lvars_shift_from_succ_body_union; [apply IHτ1 | apply IHτ2].
  - eapply lvars_shift_from_succ_body_union; [apply IHτ1 | apply IHτ2].
  - eapply lvars_shift_from_succ_body_union; [apply IHτ1 | apply IHτ2].
  - eapply lvars_shift_from_succ_body_union; [apply IHτ1 | apply IHτ2].
  - eapply lvars_shift_from_succ_body_union; [apply IHτ1 | apply IHτ2].
Qed.

Lemma context_ty_lvars_body_subset D τ :
  context_ty_lvars_at 1 τ ⊆ lvars_of_atoms D ->
  context_ty_lvars τ ⊆ lvars_shift_from 0 (lvars_of_atoms D) ∪ {[LVBound 0]}.
Proof.
  intros Hsub.
  transitivity (lvars_shift_from 0 (context_ty_lvars_at 1 τ) ∪ {[LVBound 0]}).
  - apply context_ty_lvars_at_succ_body.
  - set_solver.
Qed.

Lemma context_ty_lvars_at_shift d k τ :
  context_ty_lvars_at d (cty_shift (d + k) τ) =
  lvars_shift_from k (context_ty_lvars_at d τ).
Proof.
  induction τ in d, k |- *; cbn [context_ty_lvars_at cty_shift].
  - replace (S (d + k)) with (S d + k) by lia.
    rewrite qual_shift_from_vars.
    apply lvars_at_depth_shift_from.
  - replace (S (d + k)) with (S d + k) by lia.
    rewrite qual_shift_from_vars.
    apply lvars_at_depth_shift_from.
  - rewrite IHτ1, IHτ2. symmetry. apply lvars_shift_from_union.
  - rewrite IHτ1, IHτ2. symmetry. apply lvars_shift_from_union.
  - rewrite IHτ1, IHτ2. symmetry. apply lvars_shift_from_union.
  - rewrite IHτ1.
    replace (S (d + k)) with (S d + k) by lia.
    rewrite IHτ2.
    symmetry. apply lvars_shift_from_union.
  - rewrite IHτ1.
    replace (S (d + k)) with (S d + k) by lia.
    rewrite IHτ2.
    symmetry. apply lvars_shift_from_union.
Qed.

Lemma cty_shift0_vars τ :
  context_ty_lvars (cty_shift 0 τ) = context_ty_shift_lvars τ.
Proof.
  unfold context_ty_lvars, context_ty_shift_lvars.
  change (cty_shift 0 τ) with (cty_shift (0 + 0) τ).
  apply context_ty_lvars_at_shift.
Qed.

Lemma cty_shift_vars τ :
  context_ty_lvars (cty_shift 0 τ) = context_ty_shift_lvars τ.
Proof.
  apply cty_shift0_vars.
Qed.

Lemma cty_open_fv_subset k x τ :
  fv_cty ({k ~> x} τ) ⊆ fv_cty τ ∪ {[x]}.
Proof.
  unfold fv_cty.
  rewrite cty_open_vars.
  apply lvars_fv_open_subset.
Qed.

Lemma cty_shift_fv k τ :
  fv_cty (cty_shift k τ) = fv_cty τ.
Proof.
  unfold fv_cty, context_ty_lvars.
  rewrite <- (Nat.add_0_l k) at 1.
  rewrite context_ty_lvars_at_shift.
  apply lvars_shift_from_fv.
Qed.

Lemma context_ty_lvars_open_shift_fresh x y τ :
  x <> y ->
  LVFree x ∉ context_ty_lvars τ ->
  LVFree x ∉ context_ty_lvars (cty_open 0 y (cty_shift 0 τ)).
Proof.
  intros Hxy Hfresh Hin.
  apply lvars_fv_elem in Hin.
  pose proof (cty_open_fv_subset 0 y (cty_shift 0 τ) x Hin) as Hsub.
  rewrite cty_shift_fv in Hsub.
  apply elem_of_union in Hsub as [Hinτ|Hy].
  - apply Hfresh. apply lvars_fv_elem. exact Hinτ.
  - rewrite elem_of_singleton in Hy. congruence.
Qed.
