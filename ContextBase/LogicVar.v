(** * ContextBase.LogicVar

    Locally-nameless logic-variable keys, support sets, opening, atom
    projections, and public lvar helper lemmas. *)

From ContextBase Require Export Prelude.

Inductive logic_var : Type :=
  | LVBound (k : nat)
  | LVFree  (x : atom).

#[global] Instance logic_var_eqdec : EqDecision logic_var.
Proof. solve_decision. Qed.
#[global] Instance logic_var_countable : Countable logic_var.
Proof.
  refine (inj_countable'
    (λ v, match v with LVBound k => inl k | LVFree x => inr x end)
    (λ s, match s with inl k => LVBound k | inr x => LVFree x end) _).
  intros []; reflexivity.
Qed.

Notation lvset := (gset logic_var).

Definition logic_var_fv (v : logic_var) : aset :=
  match v with
  | LVBound _ => ∅
  | LVFree x => {[x]}
  end.

Definition logic_var_bv (v : logic_var) : gset nat :=
  match v with
  | LVBound k => {[k]}
  | LVFree _ => ∅
  end.

Definition logic_var_support (v : logic_var) : lvset := {[v]}.

Definition lvars_fv (D : lvset) : aset :=
  set_fold (λ v acc, logic_var_fv v ∪ acc) ∅ D.

Definition lvars_bv (D : lvset) : gset nat :=
  set_fold (λ v acc, logic_var_bv v ∪ acc) ∅ D.

(** ** Opening and atom-level operations *)

Definition logic_var_open_onesided (k : nat) (x : atom) (v : logic_var) : logic_var :=
  match v with
  | LVBound j => if decide (j = k) then LVFree x else LVBound j
  | LVFree y => LVFree y
  end.

Notation logic_var_open :=
  (fun k x => swap (LVBound k) (LVFree x)) (only parsing).

Notation lvars_open :=
  (fun k x => set_swap (LVBound k) (LVFree x)) (only parsing).

Notation lvars_open_onesided :=
  (fun k x => set_map (logic_var_open_onesided k x)) (only parsing).

(** ** Shifts, locality, and atom projections *)

Definition logic_var_shift_by (k : nat) (v : logic_var) : logic_var :=
  match v with
  | LVBound n => LVBound (k + n)
  | LVFree x => LVFree x
  end.

Definition lvars_shift_by (k : nat) (D : lvset) : lvset :=
  set_map (logic_var_shift_by k) D.

Notation logic_var_shift := (logic_var_shift_by 1) (only parsing).
Notation lvars_shift := (lvars_shift_by 1) (only parsing).

Definition lc_logic_var_key (v : logic_var) : Prop :=
  match v with
  | LVBound _ => False
  | LVFree _ => True
  end.

Definition lc_lvars (D : lvset) : Prop :=
  ∀ v, v ∈ D → lc_logic_var_key v.

Definition logic_var_to_atom (η : gmap nat atom) (v : logic_var) : option atom :=
  match v with
  | LVBound k => η !! k
  | LVFree x => Some x
  end.

Notation logic_var_swap :=
  (fun x y => swap (LVFree x) (LVFree y)) (only parsing).

Notation lvars_swap :=
  (fun x y => set_swap (LVFree x) (LVFree y)) (only parsing).
Definition lvars_of_atoms (X : aset) : lvset :=
  set_map LVFree X.

Definition lvars_of_bvars (B : gset nat) : lvset :=
  set_map LVBound B.

Class IntoLVars A := into_lvars : A → lvset.

#[global] Instance into_lvars_aset : IntoLVars aset := lvars_of_atoms.
#[global] Instance into_lvars_lvset : IntoLVars lvset := id.

#[global] Instance stale_logic_var : Stale logic_var := logic_var_fv.
Arguments stale_logic_var /.

#[global] Instance stale_logic_vars : Stale lvset := lvars_fv.
Arguments stale_logic_vars /.

(** ** Basic support lemmas *)


Lemma lvars_fv_elem D x :
  x ∈ lvars_fv D ↔ LVFree x ∈ D.
Proof.
  unfold lvars_fv.
  refine (set_fold_ind_L
    (fun acc D => ∀ x, x ∈ acc ↔ LVFree x ∈ D)
    (λ v acc, logic_var_fv v ∪ acc) ∅ _ _ D x).
  - intros y. better_set_solver.
  - intros v D' acc Hfresh IH z.
    destruct v as [k|a]; cbn [logic_var_fv];
      pose proof (IH z); better_set_solver.
Qed.

Lemma atom_notin_lvars_fv_iff_free_notin y (D : lvset) :
  y ∉ lvars_fv D ↔ LVFree y ∉ D.
Proof.
  rewrite lvars_fv_elem. tauto.
Qed.

Lemma lvars_fv_subset_notin_free y (D : lvset) (X : aset) :
  lvars_fv D ⊆ X ->
  y ∉ X ->
  LVFree y ∉ D.
Proof.
  intros Hsub Hy.
  rewrite <- atom_notin_lvars_fv_iff_free_notin.
  better_set_solver.
Qed.

Lemma lvars_bv_elem D k :
  k ∈ lvars_bv D ↔ LVBound k ∈ D.
Proof.
  unfold lvars_bv.
  refine (set_fold_ind_L
    (fun acc D => ∀ k, k ∈ acc ↔ LVBound k ∈ D)
    (λ v acc, logic_var_bv v ∪ acc) ∅ _ _ D k).
  - intros j. better_set_solver.
  - intros v D' acc Hfresh IH j.
    destruct v as [i|y]; cbn [logic_var_bv];
      pose proof (IH j); better_set_solver.
Qed.

Lemma lc_lvars_no_bv D :
  lc_lvars D ↔ lvars_bv D = ∅.
Proof.
  split.
  - intros Hlc. apply set_eq. intros k.
    rewrite elem_of_empty, lvars_bv_elem.
    split; [|tauto].
    intros Hin. specialize (Hlc (LVBound k) Hin). exact Hlc.
  - intros Hbv [k|x] Hin; cbn [lc_logic_var_key]; [|exact I].
    assert (k ∈ lvars_bv D) by (rewrite lvars_bv_elem; exact Hin).
    rewrite Hbv in H. better_set_solver.
Qed.

(** ** Opening lemmas *)

Lemma logic_var_open_involutive k x v :
  logic_var_open k x (logic_var_open k x v) = v.
Proof.
  apply swap_involutive.
Qed.

Lemma lvars_open_involutive k x D :
  lvars_open k x (lvars_open k x D) = D.
Proof.
  apply set_swap_involutive.
Qed.

Lemma lvars_open_elem_open k x v D :
  logic_var_open k x v ∈ lvars_open k x D <-> v ∈ D.
Proof.
  rewrite elem_of_set_swap.
  change (swap (LVBound k) (LVFree x) (logic_var_open k x v))
    with (logic_var_open k x (logic_var_open k x v)).
  rewrite logic_var_open_involutive. reflexivity.
Qed.

Lemma lvars_open_subseteq_iff k x D E :
  lvars_open k x D ⊆ lvars_open k x E <-> D ⊆ E.
Proof.
  split; intros Hsub v Hv.
  - apply lvars_open_elem_open with (k := k) (x := x).
    apply Hsub.
    apply lvars_open_elem_open. exact Hv.
  - apply elem_of_set_swap in Hv.
    apply elem_of_set_swap.
    apply Hsub. exact Hv.
Qed.

Lemma lvars_open_mono k x (D E : lvset) :
  D ⊆ E ->
  lvars_open k x D ⊆ lvars_open k x E.
Proof.
  intros HDE.
  apply lvars_open_subseteq_iff. exact HDE.
Qed.

Lemma lvars_open_union k x D E :
  lvars_open k x (D ∪ E) = lvars_open k x D ∪ lvars_open k x E.
Proof.
  apply set_map_union_L.
Qed.

Lemma logic_var_open_commute_fresh i j x y v :
  i <> j ->
  x <> y ->
  logic_var_open i x (logic_var_open j y v) =
  logic_var_open j y (logic_var_open i x v).
Proof.
  intros Hij Hxy.
  destruct v as [n|a];
    unfold swap;
    repeat destruct decide; subst; try congruence; reflexivity.
Qed.

Lemma lvars_open_commute_fresh i j x y D :
  i <> j ->
  x <> y ->
  lvars_open i x (lvars_open j y D) =
  lvars_open j y (lvars_open i x D).
Proof.
  intros Hij Hxy.
  apply set_eq. intros v.
  change
    (v ∈ set_swap (LVBound i) (LVFree x)
       (set_swap (LVBound j) (LVFree y) D) <->
     v ∈ set_swap (LVBound j) (LVFree y)
       (set_swap (LVBound i) (LVFree x) D)).
  rewrite !set_swap_elem.
  change
    (swap (LVBound j) (LVFree y) (swap (LVBound i) (LVFree x) v) ∈ D <->
     swap (LVBound i) (LVFree x) (swap (LVBound j) (LVFree y) v) ∈ D).
  replace (swap (LVBound j) (LVFree y) (swap (LVBound i) (LVFree x) v))
    with (swap (LVBound i) (LVFree x) (swap (LVBound j) (LVFree y) v)).
  reflexivity.
  exact (logic_var_open_commute_fresh i j x y v Hij Hxy).
Qed.

Lemma lvars_open_fresh_index k x D :
  k ∉ lvars_bv D ->
  x ∉ lvars_fv D ->
  lvars_open k x D = D.
Proof.
  intros Hk Hx.
  apply set_swap_fresh.
  - intros Hbad. apply Hk. rewrite lvars_bv_elem. exact Hbad.
  - intros Hbad. apply Hx. apply lvars_fv_elem. exact Hbad.
Qed.

Lemma lvars_open_difference_bound k x D :
  lvars_open k x (D ∖ {[LVBound k]}) =
  lvars_open k x D ∖ {[LVFree x]}.
Proof.
  apply set_swap_difference_l.
Qed.

Lemma lvars_bv_open_insert_dom k x D (η : gmap nat atom) :
  lvars_bv (lvars_open k x D) ⊆ dom η ->
  lvars_bv D ⊆ dom (<[k := x]> η).
Proof.
  intros Hsub n Hn.
  destruct (decide (n = k)) as [->|Hnk].
  - apply elem_of_dom. exists x. rewrite lookup_insert_eq. reflexivity.
  - apply elem_of_dom.
    assert (n ∈ lvars_bv (lvars_open k x D)) as Hopen.
    {
      rewrite lvars_bv_elem in Hn |- *.
      rewrite set_swap_elem.
      rewrite swap_fresh by congruence. exact Hn.
    }
    apply Hsub in Hopen.
    apply elem_of_dom in Hopen as [y Hy].
    exists y. rewrite lookup_insert_ne by congruence. exact Hy.
Qed.

Lemma lvars_fv_open_prime_except k x D :
  lvars_fv D ∖ {[x]} ⊆ lvars_fv (lvars_open k x D).
Proof.
  intros y Hy.
  apply elem_of_difference in Hy as [HyD Hyx].
  apply lvars_fv_elem.
  apply elem_of_set_swap.
  rewrite elem_of_singleton in Hyx.
  rewrite swap_fresh by congruence.
  apply lvars_fv_elem. exact HyD.
Qed.

Lemma lvars_fv_open_prime_fresh k x D :
  x ∉ lvars_fv D ->
  lvars_fv D ⊆ lvars_fv (lvars_open k x D).
Proof.
  intros Hfresh y Hy.
  apply lvars_fv_open_prime_except.
  apply elem_of_difference. split; [exact Hy|].
  intros Hyx. apply Hfresh. rewrite elem_of_singleton in Hyx. subst y. exact Hy.
Qed.

Lemma logic_var_open_sym k x v :
  logic_var_open k x v = swap (LVFree x) (LVBound k) v.
Proof.
  apply swap_sym.
Qed.

Lemma lvars_open_sym k x D :
  lvars_open k x D = set_swap (LVFree x) (LVBound k) D.
Proof.
  apply set_swap_sym.
Qed.

Lemma logic_var_open_onesided_swap_fresh k x v :
  x ∉ logic_var_fv v →
  logic_var_open_onesided k x v = logic_var_open k x v.
Proof.
  destruct v as [j|y]; simpl.
  - unfold swap.
    repeat destruct decide; congruence.
  - intros Hfresh.
    unfold swap.
    rewrite not_elem_of_singleton in Hfresh.
    repeat destruct decide; congruence.
Qed.
Lemma lvars_open_onesided_swap_fresh k x D :
  x ∉ lvars_fv D →
  lvars_open_onesided k x D = lvars_open k x D.
Proof.
  intros Hfresh.
  apply set_eq. intros v.
  unfold set_swap.
  rewrite !elem_of_map.
  split.
  - intros [u [Hv Hu]]. exists u. split; [|exact Hu].
    rewrite Hv. apply logic_var_open_onesided_swap_fresh.
    intros Hbad. apply Hfresh. apply lvars_fv_elem.
    destruct u as [j|y]; cbn [logic_var_fv] in Hbad;
      [better_set_solver | rewrite elem_of_singleton in Hbad; subst; exact Hu].
  - intros [u [Hv Hu]]. exists u. split; [|exact Hu].
    rewrite Hv. symmetry. apply logic_var_open_onesided_swap_fresh.
    intros Hbad. apply Hfresh. apply lvars_fv_elem.
    destruct u as [j|y]; cbn [logic_var_fv] in Hbad;
      [better_set_solver | rewrite elem_of_singleton in Hbad; subst; exact Hu].
Qed.

(** ** Shift, locality, and atom-projection lemmas *)

Lemma logic_var_shift_by_inj k : Inj (=) (=) (logic_var_shift_by k).
Proof.
  intros [i|x] [j|y] Hij; cbn [logic_var_shift_by] in Hij;
    inversion Hij; subst; try reflexivity; f_equal; lia.
Qed.

#[global] Instance logic_var_shift_key : ShiftKey logic_var := {
  key_shift := logic_var_shift_by;
  key_shift_inj := logic_var_shift_by_inj
}.

Lemma logic_var_swap_sym x y v :
  logic_var_swap x y v = logic_var_swap y x v.
Proof.
  apply swap_sym.
Qed.

Lemma lvars_swap_sym x y D :
  lvars_swap x y D = lvars_swap y x D.
Proof.
  apply set_swap_sym.
Qed.

Lemma logic_var_free_swap x y z :
  swap (LVFree x) (LVFree y) (LVFree z) = LVFree (swap x y z).
Proof.
  unfold swap. repeat destruct decide; congruence.
Qed.

Lemma lvars_fv_swap x y (D : lvset) :
  lvars_fv (lvars_swap x y D) = set_swap x y (lvars_fv D).
Proof.
  apply set_eq. intros z.
  change (z ∈ lvars_fv (set_swap (LVFree x) (LVFree y) D) <->
    z ∈ set_swap x y (lvars_fv D)).
  rewrite lvars_fv_elem.
  rewrite (set_swap_elem (LVFree x) (LVFree y) (LVFree z) D).
  rewrite (set_swap_elem x y z (lvars_fv D)).
  rewrite lvars_fv_elem.
  rewrite logic_var_free_swap.
  reflexivity.
Qed.

(** ** Public lvar-set interface lemmas *)

Lemma lvars_fv_of_atoms (X : aset) :
  lvars_fv (lvars_of_atoms X) = X.
Proof.
  apply set_eq. intros x.
  rewrite lvars_fv_elem.
  unfold lvars_of_atoms.
  rewrite elem_of_map.
  split.
  - intros [a [Heq Ha]]. inversion Heq. subst. exact Ha.
  - intros Hx. exists x. split; [reflexivity | exact Hx].
Qed.

Lemma lvars_bv_of_atoms (X : aset) :
  lvars_bv (lvars_of_atoms X) = ∅.
Proof.
  apply set_eq. intros k.
  rewrite lvars_bv_elem.
  unfold lvars_of_atoms.
  rewrite elem_of_empty, elem_of_map.
  split; [intros [a [Hbad _]]; discriminate | better_set_solver].
Qed.

Lemma lvars_bv_empty_subset_of_atoms_fv (D : lvset) :
  lvars_bv D = ∅ ->
  D ⊆ lvars_of_atoms (lvars_fv D).
Proof.
  intros Hbv v Hv.
  destruct v as [k|x].
  - exfalso.
    assert (k ∈ lvars_bv D) by (apply lvars_bv_elem; exact Hv).
    rewrite Hbv in H. better_set_solver.
  - unfold lvars_of_atoms. apply elem_of_map.
    exists x. split; [reflexivity|].
    apply lvars_fv_elem. exact Hv.
Qed.

Lemma lvars_fv_singleton_bound k :
  lvars_fv ({[LVBound k]} : lvset) = ∅.
Proof.
  apply set_eq. intros x.
  rewrite lvars_fv_elem.
  better_set_solver.
Qed.

Lemma lvars_fv_singleton_free x :
  lvars_fv ({[LVFree x]} : lvset) = {[x]}.
Proof.
  rewrite <- (lvars_fv_of_atoms ({[x]} : aset)).
  unfold lvars_of_atoms.
  rewrite set_map_singleton_L.
  reflexivity.
Qed.

Lemma lvars_fv_empty :
  lvars_fv (∅ : lvset) = ∅.
Proof.
  apply set_eq. intros x. rewrite lvars_fv_elem. better_set_solver.
Qed.

Lemma lvars_fv_open k x (D : lvset) :
  lvars_fv (lvars_open k x D) =
  (lvars_fv D ∖ {[x]}) ∪
  (if decide (k ∈ lvars_bv D) then {[x]} else ∅).
Proof.
  apply set_eq. intros y.
  rewrite lvars_fv_elem.
  change (LVFree y ∈ set_swap (LVBound k) (LVFree x) D ↔
    y ∈ (lvars_fv D ∖ {[x]}) ∪
      (if decide (k ∈ lvars_bv D) then {[x]} else ∅)).
  rewrite set_swap_elem.
  destruct (decide (y = x)) as [->|Hyx].
  - rewrite swap_r.
    destruct (decide (k ∈ lvars_bv D)) as [Hk|Hk].
    + rewrite elem_of_union, elem_of_difference, elem_of_singleton.
      rewrite lvars_bv_elem in Hk. tauto.
    + rewrite elem_of_union, elem_of_difference, elem_of_singleton.
      rewrite elem_of_empty. rewrite lvars_bv_elem in Hk. tauto.
  - rewrite swap_fresh by congruence.
    destruct (decide (k ∈ lvars_bv D)); rewrite elem_of_union,
      elem_of_difference, !elem_of_singleton, ?elem_of_empty, lvars_fv_elem;
      tauto.
Qed.

Lemma lvars_fv_union (D1 D2 : lvset) :
  lvars_fv (D1 ∪ D2) = lvars_fv D1 ∪ lvars_fv D2.
Proof.
  apply set_eq. intros x.
  rewrite elem_of_union.
  rewrite !lvars_fv_elem.
  rewrite elem_of_union.
  tauto.
Qed.

Lemma lvars_fv_mono (D E : lvset) :
  D ⊆ E ->
  lvars_fv D ⊆ lvars_fv E.
Proof.
  intros HDE x Hx.
  apply lvars_fv_elem.
  apply lvars_fv_elem in Hx.
  exact (HDE _ Hx).
Qed.

Lemma lvars_fv_subset_insert_free_drop
    (D E : lvset) x :
  LVFree x ∉ D ->
  D ⊆ {[LVFree x]} ∪ E ->
  lvars_fv D ⊆ lvars_fv E.
Proof.
  intros Hfresh Hsub y Hy.
  rewrite lvars_fv_elem in Hy |- *.
  specialize (Hsub (LVFree y) Hy).
  destruct (decide (y = x)) as [->|Hneq].
  - contradiction.
  - better_set_solver.
Qed.

Lemma lvars_fv_difference_singleton_free (D : lvset) x :
  lvars_fv (D ∖ {[LVFree x]}) = lvars_fv D ∖ {[x]}.
Proof.
  apply set_eq. intros y.
  rewrite !lvars_fv_elem, !elem_of_difference, !elem_of_singleton.
  split.
  - intros [HyD Hyx]. split; [apply lvars_fv_elem; exact HyD|].
    intros ->. apply Hyx. reflexivity.
  - intros [HyD Hyx]. split; [apply lvars_fv_elem in HyD; exact HyD|].
    intros Heq. inversion Heq. subst. contradiction.
Qed.

Lemma lvars_bv_union (D1 D2 : lvset) :
  lvars_bv (D1 ∪ D2) = lvars_bv D1 ∪ lvars_bv D2.
Proof.
  apply set_eq. intros k.
  rewrite elem_of_union.
  rewrite !lvars_bv_elem.
  rewrite elem_of_union.
  tauto.
Qed.

Lemma lvars_bv_swap x y (D : lvset) :
  lvars_bv (lvars_swap x y D) = lvars_bv D.
Proof.
  apply set_eq. intros k.
  rewrite !lvars_bv_elem.
  change (LVBound k ∈ set_swap (LVFree x) (LVFree y) D ↔ LVBound k ∈ D).
  rewrite set_swap_elem.
  rewrite swap_fresh by congruence.
  reflexivity.
Qed.

Lemma logic_var_swap_involutive x y v :
  logic_var_swap x y (logic_var_swap x y v) = v.
Proof.
  apply swap_involutive.
Qed.

Lemma lvars_fv_open_subset k x (D : lvset) :
  lvars_fv (lvars_open k x D) ⊆ lvars_fv D ∪ {[x]}.
Proof.
  intros y Hy.
  rewrite lvars_fv_open in Hy.
  destruct (decide (k ∈ lvars_bv D)); better_set_solver.
Qed.
