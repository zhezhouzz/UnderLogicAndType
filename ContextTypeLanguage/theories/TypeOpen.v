(** * ContextTypeLanguage.TypeOpen

    Single and finite-map opening for context types and type qualifiers.

    This file is syntax-only: it contains the generic finite-map opening
    infrastructure, the concrete multi-opening operations for [context_ty] and
    [type_qualifier], plus their structural laws.  The lvar-keyed type
    environment projection machinery stays in [ContextStore]/[LtyEnv]. *)

From Stdlib Require Import Classes.RelationClasses Classes.Morphisms.
From LocallyNameless Require Import Classes.
From ContextTypeLanguage Require Export Syntax.
From ContextBase Require Import BaseTactics.

(** * Generic finite-map opening infrastructure. *)

Class MOpen Env A B := mopen : Env -> A -> B.
Arguments mopen {_ _ _ _} _ _.

Class OpenCommute (A : Type) (openA : nat -> atom -> A -> A)
    (R : relation A) := {
  open_commute :
    forall i j x y (a : A),
      i <> j ->
      x <> y ->
      R (openA i x (openA j y a)) (openA j y (openA i x a));
}.

Class OpenProper (A : Type) (openA : nat -> atom -> A -> A)
    (R : relation A) := {
  open_proper :
    forall i x, Proper (R ==> R) (openA i x);
}.

#[global] Instance open_proper_cty_vars_equiv :
  OpenProper context_ty cty_open cty_vars_equiv.
Proof.
  constructor. intros i x τ1 τ2 Hτ.
  apply cty_vars_equiv_open. exact Hτ.
Qed.

#[global] Instance open_commute_cty_vars_equiv :
  OpenCommute context_ty cty_open cty_vars_equiv.
Proof.
  constructor. intros i j x y τ Hij Hxy.
  rewrite cty_open_commute_fvar by assumption. reflexivity.
Qed.

#[global] Instance open_commute_cty_eq :
  OpenCommute context_ty cty_open eq.
Proof.
  constructor. intros i j x y τ Hij Hxy.
  apply cty_open_commute_fvar; assumption.
Qed.

#[global] Instance open_commute_lvars :
  OpenCommute lvset lvars_open eq.
Proof.
  constructor. intros i j x y D Hij Hxy.
  rewrite set_swap_conjugate.
  replace (swap (LVBound i) (LVFree x) (LVBound j)) with (LVBound j).
  2:{ unfold swap. repeat destruct decide; congruence. }
  replace (swap (LVBound i) (LVFree x) (LVFree y)) with (LVFree y).
  2:{ unfold swap. repeat destruct decide; congruence. }
  reflexivity.
Qed.

#[global] Instance open_commute_qual_eq :
  OpenCommute type_qualifier qual_open_atom eq.
Proof.
  constructor. intros i j x y q Hij Hxy.
  apply qual_open_commute_fvar; assumption.
Qed.

Class MOpenInsertLaws A B `{Open atom A}
    `{MOpen (gmap nat atom) A B} := {
  mopen_insert_norm :
    forall k x η (a : A),
      η !! k = None ->
      open_env_avoids_atom x η ->
      mopen η ({k ~> x} a) = mopen (<[k := x]> η) a;
}.

Lemma open_map_fold_insert_fresh_eq
    {A : Type} (openA : nat -> atom -> A -> A)
    `{!OpenCommute A openA eq}
    (η : gmap nat atom) k x (a : A) :
  η !! k = None ->
  open_env_avoids_atom x η ->
  open_env_values_inj η ->
  map_fold openA a (<[k := x]> η) =
  openA k x (map_fold openA a η).
Proof.
  intros Hfresh Havoid Hinj.
  apply (map_fold_insert_L (M:=gmap nat) (A:=atom) (B:=A)
    openA a k x η).
  - intros i j xi xj acc Hij Hi Hj.
    apply open_commute; [exact Hij|].
    intros Heq. subst xj.
    pose proof (open_env_values_inj_insert k x η Hfresh Havoid Hinj)
      as Hinj'.
    apply Hij. eapply Hinj'; eassumption.
  - exact Hfresh.
Qed.

Definition open_cty_env (η : gmap nat atom) (τ : context_ty) : context_ty :=
  map_fold (fun k x acc => cty_open k x acc) τ η.

Definition qual_open_env (η : gmap nat atom) (q : type_qualifier)
    : type_qualifier :=
  map_fold (fun k x acc => qual_open_atom k x acc) q η.

Definition qual_with_vars (D : lvset) : type_qualifier :=
  tqual D (fun _ => True).

#[global] Instance mopen_context_ty_inst :
  MOpen (gmap nat atom) context_ty context_ty := open_cty_env.

Lemma open_cty_env_empty τ :
  open_cty_env ∅ τ = τ.
Proof.
  unfold open_cty_env. rewrite map_fold_empty. reflexivity.
Qed.

Lemma open_cty_env_singleton k x τ :
  open_cty_env (<[k := x]> ∅) τ = cty_open k x τ.
Proof.
  unfold open_cty_env.
  change (<[k:=x]> (∅ : gmap nat atom)) with ({[k:=x]} : gmap nat atom).
  rewrite map_fold_singleton.
  reflexivity.
Qed.

Lemma open_cty_env_insert_fresh η k x τ :
  η !! k = None ->
  open_env_avoids_atom x η ->
  open_env_values_inj η ->
  open_cty_env (<[k := x]> η) τ =
  cty_open k x (open_cty_env η τ).
Proof.
  intros Hfresh Havoid Hinj.
  unfold open_cty_env.
  apply (open_map_fold_insert_fresh_eq cty_open); assumption.
Qed.

Lemma qual_open_env_empty q :
  qual_open_env ∅ q = q.
Proof.
  unfold qual_open_env. rewrite map_fold_empty. reflexivity.
Qed.

Lemma qual_open_env_insert_fresh η k x q :
  η !! k = None ->
  open_env_avoids_atom x η ->
  open_env_values_inj η ->
  qual_open_env (<[k := x]> η) q =
  qual_open_atom k x (qual_open_env η q).
Proof.
  intros Hfresh Havoid Hinj.
  unfold qual_open_env.
  apply (open_map_fold_insert_fresh_eq qual_open_atom); assumption.
Qed.

Local Ltac open_lift_insert_fresh_side :=
  first [ apply open_env_lift_lookup_none; assumption
        | apply open_env_avoids_atom_lift; assumption
        | apply open_env_values_inj_lift; assumption ].

Lemma open_cty_env_inter η τ1 τ2 :
  open_cty_env η (CTInter τ1 τ2) =
  CTInter (open_cty_env η τ1) (open_cty_env η τ2).
Proof.
  unfold open_cty_env.
  induction η as [|k x η Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - rewrite !map_fold_empty. reflexivity.
  - rewrite !(Hfold context_ty (fun k x acc => cty_open k x acc)).
    cbn [cty_open]. rewrite IH. reflexivity.
Qed.

Lemma open_cty_env_union η τ1 τ2 :
  open_cty_env η (CTUnion τ1 τ2) =
  CTUnion (open_cty_env η τ1) (open_cty_env η τ2).
Proof.
  unfold open_cty_env.
  induction η as [|k x η Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - rewrite !map_fold_empty. reflexivity.
  - rewrite !(Hfold context_ty (fun k x acc => cty_open k x acc)).
    cbn [cty_open]. rewrite IH. reflexivity.
Qed.

Lemma open_cty_env_sum η τ1 τ2 :
  open_cty_env η (CTSum τ1 τ2) =
  CTSum (open_cty_env η τ1) (open_cty_env η τ2).
Proof.
  unfold open_cty_env.
  induction η as [|k x η Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - rewrite !map_fold_empty. reflexivity.
  - rewrite !(Hfold context_ty (fun k x acc => cty_open k x acc)).
    cbn [cty_open]. rewrite IH. reflexivity.
Qed.

Lemma open_cty_env_arrow η τx τ :
  open_env_values_inj η ->
  open_cty_env η (CTArrow τx τ) =
  CTArrow (open_cty_env η τx) (open_cty_env ((kmap S η)) τ).
Proof.
  revert τx τ.
  induction η as [|k x η Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - intros τx τ _. rewrite kmap_empty, !open_cty_env_empty.
    reflexivity.
  - intros τx τ Hinj.
    pose proof (open_env_values_inj_insert_inv η k x Hfresh Hinj)
      as [Hinjη Havoid].
    rewrite open_cty_env_insert_fresh by assumption.
    rewrite (IH τx τ Hinjη).
    cbn [cty_open].
    rewrite open_cty_env_insert_fresh by assumption.
    rewrite open_env_lift_insert.
    rewrite open_cty_env_insert_fresh by open_lift_insert_fresh_side.
    reflexivity.
Qed.

Lemma open_cty_env_wand η τx τ :
  open_env_values_inj η ->
  open_cty_env η (CTWand τx τ) =
  CTWand (open_cty_env η τx) (open_cty_env ((kmap S η)) τ).
Proof.
  revert τx τ.
  induction η as [|k x η Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - intros τx τ _. rewrite kmap_empty, !open_cty_env_empty.
    reflexivity.
  - intros τx τ Hinj.
    pose proof (open_env_values_inj_insert_inv η k x Hfresh Hinj)
      as [Hinjη Havoid].
    rewrite open_cty_env_insert_fresh by assumption.
    rewrite (IH τx τ Hinjη).
    cbn [cty_open].
    rewrite open_cty_env_insert_fresh by assumption.
    rewrite open_env_lift_insert.
    rewrite open_cty_env_insert_fresh by open_lift_insert_fresh_side.
    reflexivity.
Qed.

Lemma open_cty_env_over η b q :
  open_env_values_inj η ->
  open_cty_env η (CTOver b q) =
  CTOver b (qual_open_env ((kmap S η)) q).
Proof.
  revert q.
  induction η as [|k x η Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - intros q _. rewrite kmap_empty, open_cty_env_empty, qual_open_env_empty.
    reflexivity.
  - intros q Hinj.
    pose proof (open_env_values_inj_insert_inv η k x Hfresh Hinj)
      as [Hinjη Havoid].
    rewrite open_cty_env_insert_fresh by assumption.
    rewrite (IH q Hinjη).
    cbn [cty_open].
    rewrite open_env_lift_insert.
    rewrite qual_open_env_insert_fresh by open_lift_insert_fresh_side.
    reflexivity.
Qed.

Lemma open_cty_env_under η b q :
  open_env_values_inj η ->
  open_cty_env η (CTUnder b q) =
  CTUnder b (qual_open_env ((kmap S η)) q).
Proof.
  revert q.
  induction η as [|k x η Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - intros q _. rewrite kmap_empty, open_cty_env_empty, qual_open_env_empty.
    reflexivity.
  - intros q Hinj.
    pose proof (open_env_values_inj_insert_inv η k x Hfresh Hinj)
      as [Hinjη Havoid].
    rewrite open_cty_env_insert_fresh by assumption.
    rewrite (IH q Hinjη).
    cbn [cty_open].
    rewrite open_env_lift_insert.
    rewrite qual_open_env_insert_fresh by open_lift_insert_fresh_side.
    reflexivity.
Qed.

Lemma open_cty_env_preserves_erasure η τ :
  erase_ty (open_cty_env η τ) = erase_ty τ.
Proof.
  unfold open_cty_env.
  induction η as [|k x η Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - rewrite map_fold_empty. reflexivity.
  - rewrite (Hfold context_ty (fun k x acc => cty_open k x acc)).
    rewrite cty_open_preserves_erasure. exact IH.
Qed.

Lemma qual_open_env_vars η q :
  open_env_fresh_for_lvars η (qual_vars q) ->
  qual_vars (qual_open_env η q) = lvars_open_env η (qual_vars q).
Proof.
  revert q.
  induction η as [|k x η Hnone Hfold IH] using fin_maps.map_fold_ind.
  - intros q _. rewrite qual_open_env_empty. better_base_solver.
  - intros q Hfresh.
    pose proof (IH q ltac:(eapply open_env_fresh_for_lvars_insert_tail; eassumption))
      as HIH.
    change (qual_vars
      (map_fold (fun k x acc => qual_open_atom k x acc) q (<[k:=x]> η)) =
      lvars_open_env (<[k:=x]> η) (qual_vars q)).
    rewrite (Hfold type_qualifier (fun k x acc => qual_open_atom k x acc)).
    fold (qual_open_env η q).
    rewrite qual_open_atom_vars.
    rewrite HIH.
    rewrite lvars_open_env_insert_fresh.
    + reflexivity.
    + exact Hnone.
    + eapply open_env_fresh_for_lvars_insert_head; eassumption.
Qed.

Lemma context_ty_lvars_open_cty_env η τ :
  open_env_fresh_for_lvars η (context_ty_lvars τ) ->
  context_ty_lvars (open_cty_env η τ) =
  lvars_open_env η (context_ty_lvars τ).
Proof.
  revert τ.
  induction η as [|k x η Hnone Hfold IH] using fin_maps.map_fold_ind.
  - intros τ _. rewrite open_cty_env_empty. better_base_solver.
  - intros τ Hfresh.
    pose proof (IH τ ltac:(eapply open_env_fresh_for_lvars_insert_tail; eassumption))
      as HIH.
    change (context_ty_lvars
      (map_fold (fun k x acc => cty_open k x acc) τ (<[k:=x]> η)) =
      lvars_open_env (<[k:=x]> η) (context_ty_lvars τ)).
    rewrite (Hfold context_ty (fun k x acc => cty_open k x acc)).
    fold (open_cty_env η τ).
    rewrite cty_open_vars.
    unfold context_ty_open_lvars.
    replace (context_ty_lvars (open_cty_env η τ))
      with (lvars_open_env η (context_ty_lvars τ)) by (symmetry; exact HIH).
    rewrite lvars_open_env_insert_fresh.
    + reflexivity.
    + exact Hnone.
    + eapply open_env_fresh_for_lvars_insert_head; eassumption.
Qed.

Lemma open_env_lift_qual_diff_bound0 η q :
  open_env_fresh_for_lvars ((kmap S η)) (qual_vars q) ->
  lvars_open_env ((kmap S η)) (qual_vars q ∖ {[LVBound 0]}) =
  qual_vars (qual_open_env ((kmap S η)) q) ∖ {[LVBound 0]}.
Proof.
  intros Hfresh.
  rewrite qual_open_env_vars by exact Hfresh.
  apply set_eq. intros v.
  rewrite elem_of_difference.
  unfold lvars_open_env.
  split.
  - intros Hv.
    apply elem_of_map in Hv as [u [-> Hu]].
    apply elem_of_difference in Hu as [HuD Hu0].
    split.
    + apply elem_of_map. exists u. split; [reflexivity|exact HuD].
    + intros Hbad. apply Hu0.
      rewrite elem_of_singleton in Hbad |- *.
      destruct u as [n|a]; cbn [logic_var_open_env] in Hbad.
      * destruct n as [|n].
        -- rewrite open_env_lift_lookup_zero_none in Hbad.
           reflexivity.
        -- destruct ((kmap S η) !! S n); discriminate.
      * discriminate.
  - intros [Hv Hnot].
    apply elem_of_map in Hv as [u [-> HuD]].
    apply elem_of_map.
    exists u. split; [reflexivity|].
    apply elem_of_difference. split; [exact HuD|].
    intros Hbad. apply Hnot.
    rewrite elem_of_singleton in Hbad |- *.
    subst u.
    cbn [logic_var_open_env].
    better_base_solver.
Qed.

Lemma lvars_fv_open_env_lift_subset_at_depth1 η D :
  lvars_fv (lvars_open_env ((kmap S η)) D) ⊆
  lvars_fv (lvars_open_env η (lvars_at_depth 1 D)).
Proof.
  intros x Hx.
  apply lvars_fv_elem in Hx.
  unfold lvars_open_env in Hx.
  apply elem_of_map in Hx as [v [Hv Hvd]].
  apply lvars_fv_elem.
  unfold lvars_open_env.
  apply elem_of_map.
  destruct v as [n|a].
  - cbn [logic_var_open_env] in Hv.
    destruct n as [|n].
    + rewrite open_env_lift_lookup_zero_none in Hv. discriminate.
    + rewrite (lookup_kmap (M1:=gmap nat) (M2:=gmap nat)
        S (Inj0:=ltac:(intros ? ? ?; lia)) (A:=atom) η n) in Hv.
      destruct (η !! n) as [y|] eqn:Hηn; [|discriminate].
      inversion Hv. subst y.
      exists (LVBound n). split.
      * cbn [logic_var_open_env]. rewrite Hηn. reflexivity.
      * rewrite lvars_at_depth_elem.
        exists (LVBound (S n)). split; [exact Hvd|].
        cbn [logic_var_at_depth].
        rewrite decide_True by lia.
        replace (S n - 1) with n by lia. reflexivity.
  - cbn [logic_var_open_env] in Hv. inversion Hv. subst a.
    exists (LVFree x). split; [reflexivity|].
    rewrite lvars_at_depth_elem.
    exists (LVFree x). split; [exact Hvd|reflexivity].
Qed.

Lemma open_env_lift_fresh_for_lvars_at_depth1 η D :
  open_env_fresh_for_lvars η (lvars_at_depth 1 D) ->
  open_env_fresh_for_lvars ((kmap S η)) D.
Proof.
  intros Hfresh j x Hjx Hbad.
  destruct j as [|j].
  - rewrite open_env_lift_lookup_zero_none in Hjx. discriminate.
  - apply lookup_kmap_Some in Hjx as [i [HSi Hηi]].
    2:{ intros ? ? ?. lia. }
    injection HSi as ->.
    eapply Hfresh; [exact Hηi|].
    replace (delete (S i) ((kmap S η))) with
      (kmap S (delete i η) : gmap nat atom) in Hbad.
    2:{
      exact (@kmap_delete nat (gmap nat) _ _ _ _ _ _ _ _ _
        nat (gmap nat) _ _ _ _ _ _ _ _ _
        S (ltac:(intros ? ? ?; lia)) atom η i).
    }
    eapply lvars_fv_open_env_lift_subset_at_depth1. exact Hbad.
Qed.

Lemma open_env_lift_fresh_for_bound0_singleton η :
  open_env_fresh_for_lvars ((kmap S η)) ({[LVBound 0]}).
Proof.
  intros i x Hi Hbad.
  apply lvars_fv_elem in Hbad.
  unfold lvars_open_env in Hbad.
  apply elem_of_map in Hbad as [v [Hv HvIn]].
  apply elem_of_singleton in HvIn. subst v.
  cbn [logic_var_open_env] in Hv.
  assert (Hnone : delete i (kmap S η : gmap nat atom) !! 0 = None).
  {
    destruct (decide (i = 0)) as [->|Hi0].
    - rewrite lookup_delete_eq. reflexivity.
    - rewrite lookup_delete_ne by congruence.
      apply open_env_lift_lookup_zero_none.
  }
  rewrite Hnone in Hv. discriminate.
Qed.

Lemma open_cty_env_lift_shift0_exact η τ :
  open_env_values_inj η ->
  open_cty_env ((kmap S η)) (cty_shift 0 τ) =
  cty_shift 0 (open_cty_env η τ).
Proof.
  unfold open_cty_env.
  refine (fin_maps.map_fold_ind
    (fun η =>
      open_env_values_inj η ->
      map_fold (fun k x acc => cty_open k x acc)
        (cty_shift 0 τ) ((kmap S η)) =
      cty_shift 0
        (map_fold (fun k x acc => cty_open k x acc) τ η)) _ _ η).
  - intros _. rewrite kmap_empty, !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH Hinj.
    pose proof (open_env_values_inj_insert_inv η' k x Hfresh Hinj)
      as [Hinjη Havoid].
    rewrite open_env_lift_insert.
    change (map_fold (fun k0 x0 acc => cty_open k0 x0 acc)
      (cty_shift 0 τ) (<[S k:=x]> (kmap S η')))
      with (open_cty_env (<[S k := x]> (kmap S η'))
        (cty_shift 0 τ)).
	    rewrite open_cty_env_insert_fresh.
	    2:{ better_base_solver. }
	    2:{ better_base_solver. }
    2:{ apply open_env_values_inj_lift. exact Hinjη. }
    change (open_cty_env (kmap S η') (cty_shift 0 τ))
      with (map_fold (fun k0 x0 acc => cty_open k0 x0 acc)
        (cty_shift 0 τ) (kmap S η')).
    rewrite IH by exact Hinjη.
    rewrite cty_open_shift_under_gen by lia.
    change (cty_shift 0 (cty_open k x (open_cty_env η' τ)) =
      cty_shift 0 (open_cty_env (<[k:=x]> η') τ)).
    rewrite open_cty_env_insert_fresh by assumption.
    reflexivity.
Qed.

(** * ContextTypeLanguage.TypeOpen

    Syntax-shape normalization tactics for finite-map opening. *)

Ltac qual_open_env_syntax_norm :=
  rewrite ?qual_open_env_empty;
  try rewrite ?qual_open_env_insert_fresh by eauto;
  try rewrite ?qual_open_env_vars by eauto.

Ltac qual_open_env_syntax_norm_in H :=
  rewrite ?qual_open_env_empty in H;
  try rewrite ?qual_open_env_insert_fresh in H by eauto;
  try rewrite ?qual_open_env_vars in H by eauto.

Ltac cty_open_env_syntax_norm :=
  rewrite ?open_cty_env_empty;
  rewrite ?open_cty_env_preserves_erasure;
  rewrite ?open_cty_env_inter, ?open_cty_env_union, ?open_cty_env_sum;
  try rewrite ?open_cty_env_arrow by eauto;
  try rewrite ?open_cty_env_wand by eauto;
  try rewrite ?open_cty_env_over by eauto;
  try rewrite ?open_cty_env_under by eauto;
  try rewrite ?context_ty_lvars_open_cty_env by eauto;
  try rewrite ?open_cty_env_lift_shift0_exact by eauto.

Ltac cty_open_env_syntax_norm_in H :=
  rewrite ?open_cty_env_empty in H;
  rewrite ?open_cty_env_preserves_erasure in H;
  rewrite ?open_cty_env_inter in H;
  rewrite ?open_cty_env_union in H;
  rewrite ?open_cty_env_sum in H;
  try rewrite ?open_cty_env_arrow in H by eauto;
  try rewrite ?open_cty_env_wand in H by eauto;
  try rewrite ?open_cty_env_over in H by eauto;
  try rewrite ?open_cty_env_under in H by eauto;
  try rewrite ?context_ty_lvars_open_cty_env in H by eauto;
  try rewrite ?open_cty_env_lift_shift0_exact in H by eauto.

Ltac type_open_env_syntax_norm :=
  qual_open_env_syntax_norm;
  cty_open_env_syntax_norm;
  type_syntax_norm.

Ltac type_open_env_syntax_norm_in H :=
  qual_open_env_syntax_norm_in H;
  cty_open_env_syntax_norm_in H;
  type_syntax_norm_in H.
