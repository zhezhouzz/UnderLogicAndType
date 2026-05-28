(** * ContextTypeLanguage.WFLvars

    Formation/scoping predicates for logic-variable sets. *)

From ContextTypeLanguage Require Export Syntax.

Definition lvar_wf_at (d : nat) (D : aset) (v : logic_var) : Prop :=
  match v with
  | LVFree x => x ∈ D
  | LVBound k => k < d
  end.

Definition lvars_wf_at (d : nat) (D : aset) (L : lvset) : Prop :=
  forall v, v ∈ L -> lvar_wf_at d D v.

Definition lvars_lc_at (d : nat) (L : lvset) : Prop :=
  forall k, k ∈ lvars_bv L -> k < d.

Lemma lvars_wf_at_mono d D E L :
  D ⊆ E ->
  lvars_wf_at d D L ->
  lvars_wf_at d E L.
Proof.
  intros HDE Hwf [k|x] Hin; cbn [lvar_wf_at] in *.
  - exact (Hwf (LVBound k) Hin).
  - apply HDE. exact (Hwf (LVFree x) Hin).
Qed.

Lemma lvars_wf_at_lc d D L :
  lvars_wf_at d D L ->
  lvars_lc_at d L.
Proof.
  intros Hwf k Hk.
  rewrite lvars_bv_elem in Hk.
  exact (Hwf (LVBound k) Hk).
Qed.

Lemma lvars_wf_at_fv_subset d D L :
  lvars_wf_at d D L ->
  lvars_fv L ⊆ D.
Proof.
  intros Hwf x Hx.
  apply lvars_fv_elem in Hx.
  exact (Hwf (LVFree x) Hx).
Qed.

Lemma lvars_wf_at_drop_fresh d D x L :
  x ∉ lvars_fv L ->
  lvars_wf_at d (D ∪ {[x]}) L ->
  lvars_wf_at d D L.
Proof.
  intros Hfresh Hwf [k|y] Hy; cbn [lvar_wf_at].
  - exact (Hwf (LVBound k) Hy).
  - assert (y ∈ D ∪ {[x]}) as HyD by exact (Hwf (LVFree y) Hy).
    apply elem_of_union in HyD as [HyD | Hyx]; [exact HyD |].
    rewrite elem_of_singleton in Hyx. subst y.
    exfalso. apply Hfresh. apply lvars_fv_elem. exact Hy.
Qed.

Lemma lvars_wf_at_open_body D L x :
  x ∉ D ->
  lvars_wf_at 1 D L ->
  lvars_wf_at 0 (D ∪ {[x]}) (lvars_open 0 x L).
Proof.
  intros Hx Hwf v Hv.
  rewrite lvars_open_unfold in Hv.
  rewrite set_swap_elem in Hv.
  destruct v as [k|y]; cbn [lvar_wf_at].
  - destruct k as [|k].
    + rewrite swap_l in Hv.
      assert (LVFree x ∈ L) as Hxin by exact Hv.
      exfalso. apply Hx. exact (Hwf (LVFree x) Hxin).
    + exfalso.
      rewrite swap_fresh in Hv by congruence.
      assert (LVBound (S k) ∈ L) as Hk.
      { exact Hv. }
      specialize (Hwf (LVBound (S k)) Hk). cbn [lvar_wf_at] in Hwf. lia.
  - destruct (decide (x = y)) as [->|Hxy].
    + set_solver.
    + assert (LVFree y ∈ L) as Hy.
      { rewrite swap_fresh in Hv by congruence. exact Hv. }
      apply elem_of_union. left. exact (Hwf (LVFree y) Hy).
Qed.

Lemma lvars_wf_at_open_at d D L x :
  x ∉ D ->
  lvars_wf_at (S d) D L ->
  lvars_wf_at d (D ∪ {[x]}) (lvars_open d x L).
Proof.
  intros Hx Hwf v Hv.
  rewrite lvars_open_unfold in Hv.
  rewrite set_swap_elem in Hv.
  destruct v as [k|y]; cbn [lvar_wf_at].
  - destruct (decide (k = d)) as [->|Hkd].
    + rewrite swap_l in Hv.
      exfalso. apply Hx. exact (Hwf (LVFree x) Hv).
    + rewrite swap_fresh in Hv by congruence.
      specialize (Hwf (LVBound k) Hv). cbn [lvar_wf_at] in Hwf.
      lia.
  - destruct (decide (x = y)) as [->|Hxy].
    + apply elem_of_union_r. set_solver.
    + rewrite swap_fresh in Hv by congruence.
      apply elem_of_union_l. exact (Hwf (LVFree y) Hv).
Qed.

Lemma lvars_wf_at_shift d D L k :
  d <= k ->
  lvars_wf_at d D L ->
  lvars_wf_at d D (lvars_shift_from k L).
Proof.
  intros Hdk Hwf v Hv.
  unfold lvars_shift_from in Hv.
  apply elem_of_map in Hv as [u [-> Hu]].
  destruct u as [n|x]; cbn [logic_var_shift_from lvar_wf_at].
  - destruct (decide (k <= n)) as [Hkn|Hkn].
    + specialize (Hwf (LVBound n) Hu). cbn [lvar_wf_at] in Hwf. lia.
    + exact (Hwf (LVBound n) Hu).
  - exact (Hwf (LVFree x) Hu).
Qed.
