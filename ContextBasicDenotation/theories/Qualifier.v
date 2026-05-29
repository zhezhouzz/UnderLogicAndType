(** * BasicDenotation.Qualifier

    Interpreting type qualifiers as exact logic-qualifier worlds. *)

From ContextBasicDenotation Require Import Notation.

Section QualifierDenotation.

Definition lstore_in_lworld_on
    {D : lvset} (s : LStoreOn D) (w : LWorldOn D) : Prop :=
  worldA_stores (@lw value _ w : LWorld) (lso_store s).

Definition type_qualifier_holds_lworld
    (q : type_qualifier) (w : LWorldOn (qual_vars q)) : Prop :=
  forall s : LStoreOn (qual_vars q),
    qual_prop q s <-> lstore_in_lworld_on s w.

Definition type_qualifier_lqual (q : type_qualifier) : logic_qualifier :=
  lqual (qual_vars q) (fun w => type_qualifier_holds_lworld q w).

Definition type_qualifier_formula (q : type_qualifier) : Formula :=
  FAtom (type_qualifier_lqual q).

Lemma type_qualifier_holds_lworld_store_iff q
    (w : LWorldOn (qual_vars q)) (s : LStoreOn (qual_vars q)) :
  type_qualifier_holds_lworld q w ->
  qual_prop q s <-> lstore_in_lworld_on s w.
Proof. intros H. apply H. Qed.

Lemma lstore_in_lworld_on_open_back k x D
    (s : LStoreOn (lvars_open k x D))
    (w : LWorldOn (lvars_open k x D)) :
  lstore_in_lworld_on (lstore_on_open_back k x D s)
    (lworld_on_open_back k x D w) <->
  lstore_in_lworld_on s w.
Proof.
  unfold lstore_in_lworld_on, lstore_on_open_back, lworld_on_open_back.
  cbn [lw lso_store lraw_world raw_worldA worldA_stores].
  split.
  - intros [σ0 [Hσ0 Hswap]].
    change (storeA_swap (LVBound k) (LVFree x) σ0 =
      lstore_swap (LVBound k) (LVFree x) (lso_store s)) in Hswap.
    assert (σ0 = lso_store s) as ->.
    {
      rewrite <- (storeA_swap_involutive (LVBound k) (LVFree x) σ0).
      rewrite Hswap.
      change (storeA_swap (LVBound k) (LVFree x)
        (lstore_swap (LVBound k) (LVFree x) (lso_store s)) = lso_store s).
      unfold lstore_swap, lstore_rekey.
      apply storeA_swap_involutive.
    }
    exact Hσ0.
  - intros Hs.
    exists (lso_store s). split; [exact Hs|].
    unfold lstore_swap, lstore_rekey. reflexivity.
Qed.

Lemma lstore_in_lworld_on_open_front k x D
    (s : LStoreOn D) (w : LWorldOn (lvars_open k x D)) :
  lstore_in_lworld_on s (lworld_on_open_back k x D w) <->
  lstore_in_lworld_on (lstore_on_open_front k x s) w.
Proof.
  unfold lstore_in_lworld_on, lstore_on_open_front, lworld_on_open_back.
  cbn [lw lso_store lraw_world raw_worldA worldA_stores].
  split.
  - intros [σ0 [Hσ0 Hswap]].
    change (storeA_swap (LVBound k) (LVFree x) σ0 =
      lso_store s) in Hswap.
    assert (σ0 = lstore_swap (LVBound k) (LVFree x) (lso_store s)) as ->.
    {
      rewrite <- (storeA_swap_involutive (LVBound k) (LVFree x) σ0).
      rewrite Hswap.
      unfold lstore_swap, lstore_rekey. reflexivity.
    }
    exact Hσ0.
  - intros Hs.
    exists (lstore_swap (LVBound k) (LVFree x) (lso_store s)).
    split; [exact Hs|].
    unfold lstore_swap, lstore_rekey.
    apply storeA_swap_involutive.
Qed.

Lemma type_qualifier_lqual_open k x q :
  x ∉ qual_dom q ->
  type_qualifier_lqual (qual_open_atom k x q) =
  lqual_open k x (type_qualifier_lqual q).
Proof.
  intros _.
  destruct q as [D P].
  unfold type_qualifier_lqual, qual_open_atom.
  cbn [qual_vars qual_lvars lqual_open].
  apply logic_qualifier_ext; [reflexivity|].
  intros w1 w2 Hlw.
  assert (Hw12 : w1 = w2) by (apply lworld_on_ext; exact Hlw).
  subst w1.
  cbn [lqual_prop type_qualifier_holds_lworld qual_prop].
  split; intros H s.
  - specialize (H (lstore_on_open_front k x s)).
    cbn [qual_prop] in H.
    split; intros HP.
    + apply (proj2 (lstore_in_lworld_on_open_front k x D s w2)).
      apply H.
      rewrite lstore_on_open_back_front. exact HP.
    + rewrite <- (lstore_on_open_back_front k x D s).
      apply H.
      apply (proj1 (lstore_in_lworld_on_open_front k x D s w2)).
      exact HP.
  - specialize (H (lstore_on_open_back k x D s)).
    split; intros HP.
    + apply (proj1 (lstore_in_lworld_on_open_back k x D s w2)).
      apply H. exact HP.
    + apply H.
      apply (proj2 (lstore_in_lworld_on_open_back k x D s w2)).
      exact HP.
Qed.

Lemma type_qualifier_formula_open k x q :
  x ∉ qual_dom q ->
  formula_open k x (type_qualifier_formula q) =
  type_qualifier_formula (qual_open_atom k x q).
Proof.
  intros Hfresh.
  unfold type_qualifier_formula.
  rewrite formula_open_atom.
  f_equal. symmetry.
  apply type_qualifier_lqual_open. exact Hfresh.
Qed.

Lemma type_qualifier_formula_open_env η q :
  open_env_fresh_for_lvars η (qual_vars q) ->
  open_env_values_inj η ->
  formula_open_env η (type_qualifier_formula q) =
  type_qualifier_formula (qual_open_env η q).
Proof.
  revert q.
  induction η as [|k x η Hnone Hfold IH] using fin_maps.map_fold_ind.
  - intros q _ _.
    rewrite formula_open_env_empty, qual_open_env_empty. reflexivity.
  - intros q Hfresh Hinj.
    pose proof (open_env_values_inj_insert_inv η k x Hnone Hinj)
      as [Hinjη Havoid].
    pose proof (open_env_fresh_for_lvars_insert_tail η k x
      (qual_vars q) Hnone Hfresh) as Hfreshη.
    rewrite formula_open_env_insert_fresh by assumption.
    rewrite IH by (exact Hfreshη || exact Hinjη).
    rewrite type_qualifier_formula_open.
    2:{
      pose proof (open_env_fresh_for_lvars_insert_head η k x
        (qual_vars q) Hnone Hfresh) as Hhead.
      unfold qual_dom.
      rewrite qual_open_env_vars by exact Hfreshη.
      exact Hhead.
    }
    rewrite qual_open_env_insert_fresh by assumption.
    reflexivity.
Qed.

Lemma formula_fv_type_qualifier_formula q :
  formula_fv (type_qualifier_formula q) = qual_dom q.
Proof. reflexivity. Qed.

Lemma formula_lvars_fv_type_qualifier_formula φ :
  lvars_fv (formula_lvars (type_qualifier_formula φ)) = qual_dom φ.
Proof.
  change (lvars_fv (formula_lvars (type_qualifier_formula φ)))
    with (formula_fv (type_qualifier_formula φ)).
  apply formula_fv_type_qualifier_formula.
Qed.

Lemma formula_fv_over_fib_type_qualifier_open_fresh x y b φ :
  LVFree x ∉ context_ty_lvars (CTOver b φ) ->
  x <> y ->
  x ∉ formula_fv
    (FFibVars (qual_vars (φ ^q^ y) ∖ {[LVFree y]})
      (FOver (type_qualifier_formula (φ ^q^ y)))).
Proof.
  intros Hfresh Hxy.
  rewrite formula_fv_fibvars, formula_fv_over,
    formula_fv_type_qualifier_formula,
    lvars_fv_qual_vars_difference_free.
  pose proof (context_ty_over_fresh_open_qual_dom x y b φ Hfresh Hxy).
  set_solver.
Qed.

Lemma formula_fv_under_fib_type_qualifier_open_fresh x y b φ :
  LVFree x ∉ context_ty_lvars (CTUnder b φ) ->
  x <> y ->
  x ∉ formula_fv
    (FFibVars (qual_vars (φ ^q^ y) ∖ {[LVFree y]})
      (FUnder (type_qualifier_formula (φ ^q^ y)))).
Proof.
  intros Hfresh Hxy.
  rewrite formula_fv_fibvars, formula_fv_under,
    formula_fv_type_qualifier_formula,
    lvars_fv_qual_vars_difference_free.
  pose proof (context_ty_under_fresh_open_qual_dom x y b φ Hfresh Hxy).
  set_solver.
Qed.

Lemma type_qualifier_formula_models_iff q (m : WfWorldT) :
  res_models m (type_qualifier_formula q) <->
  logic_qualifier_denote (type_qualifier_lqual q) m.
Proof.
  unfold res_models, type_qualifier_formula.
  cbn [formula_measure res_models_fuel].
  split; [tauto |].
  intros Hden. split; [| exact Hden].
  destruct Hden as [_ [Hsub _]].
  exact Hsub.
Qed.

End QualifierDenotation.
