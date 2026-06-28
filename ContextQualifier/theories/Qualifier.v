(** * ContextQualifier.Qualifier

    Store-level qualifiers are locally-nameless predicates over lvar-keyed
    stores.  This mirrors [LogicQualifier]'s dependent-domain design, except
    the payload is an [LStore] rather than an [LWorld].

    The core language operation is opening.  Opening is implemented as a swap
    between a bound lvar and a free atom, with the predicate interpreting its
    input after swapping the store back. *)

From CoreLang Require Export Prelude Syntax.
From ContextBase Require Export Prelude LogicVar LogicVarShift LogicVarOpenEnv
  BaseTactics.
From ContextStore Require Export Store.
From Stdlib Require Import Logic.FunctionalExtensionality
  Logic.ProofIrrelevance Logic.PropExtensionality.

Section Qualifier.

Context {V : Type} `{ValueSig V}.

Local Notation LStoreT := (LStore (V := V)) (only parsing).
Local Notation LStoreOnT := (LStoreOn (V := V)) (only parsing).
Local Notation StoreT := (Store (V := V)) (only parsing).

Record qualifier : Type := tqual {
  qual_lvars : lvset;
  qual_prop : LStoreOnT qual_lvars -> Prop;
}.

Definition qual_vars (q : qualifier) : lvset :=
  qual_lvars q.

Definition qual_dom (q : qualifier) : aset :=
  lvars_fv (qual_lvars q).

Definition qual_bvars (q : qualifier) : gset nat :=
  lvars_bv (qual_lvars q).

Lemma lvfree_notin_lvars_at_depth1_qual_vars (q : qualifier) z :
  z ∉ qual_dom q ->
  LVFree z ∉ lvars_at_depth 1 (qual_vars q).
Proof.
  unfold qual_dom.
  intros Hz HzD.
  apply Hz.
  rewrite lvars_at_depth_elem in HzD.
  destruct HzD as [v [Hv Hat]].
  destruct v as [n|a].
  - cbn [logic_var_at_depth] in Hat.
    destruct decide; discriminate.
  - cbn [logic_var_at_depth] in Hat.
    inversion Hat. subst a.
    apply lvars_fv_elem. exact Hv.
Qed.

Lemma qual_ext (q1 q2 : qualifier) :
  qual_lvars q1 = qual_lvars q2 ->
  (forall (s1 : LStoreOnT (qual_lvars q1))
          (s2 : LStoreOnT (qual_lvars q2)),
      lso_store s1 = lso_store s2 ->
      qual_prop q1 s1 <-> qual_prop q2 s2) ->
  q1 = q2.
Proof.
  destruct q1 as [D1 P1], q2 as [D2 P2]. simpl.
  intros HD HP. subst D2. f_equal.
  apply functional_extensionality. intros s.
  apply propositional_extensionality.
  apply HP. reflexivity.
Qed.

Definition qual_open_atom
    (k : nat) (x : atom) (q : qualifier) : qualifier :=
  match q with
  | tqual D P =>
      tqual (lvars_open k x D)
        (fun s => P (lstore_on_open_back k x D s))
  end.

Definition lstore_on_atom_swap_back
    (x y : atom) (D : lvset)
    (s : LStoreOnT (lvars_swap x y D)) : LStoreOnT D.
Proof.
  refine {| storeAO_store := lstore_swap (LVFree x) (LVFree y) (lso_store s) |}.
  unfold lstore_swap, lstore_rekey.
  rewrite storeA_rekey_dom by apply swap_inj.
  change (set_swap (LVFree x) (LVFree y) (dom (lso_store s : LStoreT)) = D).
  rewrite (lso_dom s).
  better_base_solver.
Defined.

Definition lstore_on_atom_swap_front
    (x y : atom) (D : lvset)
    (s : LStoreOnT D) : LStoreOnT (lvars_swap x y D).
Proof.
  refine {| storeAO_store := lstore_swap (LVFree x) (LVFree y) (lso_store s) |}.
  unfold lstore_swap, lstore_rekey.
  rewrite storeA_rekey_dom by apply swap_inj.
  change (set_swap (LVFree x) (LVFree y) (dom (lso_store s : LStoreT)) =
    lvars_swap x y D).
  rewrite (lso_dom s). reflexivity.
Defined.

Lemma lstore_on_atom_swap_back_front x y D (s : LStoreOnT D) :
  lstore_on_atom_swap_back x y D
    (lstore_on_atom_swap_front x y D s) = s.
Proof.
  apply lstore_on_ext.
  unfold lstore_on_atom_swap_back, lstore_on_atom_swap_front.
  cbn [lso_store storeAO_store].
  change (lstore_swap (LVFree x) (LVFree y)
    (lstore_swap (LVFree x) (LVFree y) (lso_store s)) = lso_store s).
  unfold lstore_swap, lstore_rekey.
  apply storeA_swap_involutive.
Qed.

Lemma lstore_on_atom_swap_front_back x y D
    (s : LStoreOnT (lvars_swap x y D)) :
  lstore_on_atom_swap_front x y D
    (lstore_on_atom_swap_back x y D s) = s.
Proof.
  apply lstore_on_ext.
  unfold lstore_on_atom_swap_back, lstore_on_atom_swap_front.
  cbn [lso_store storeAO_store].
  change (lstore_swap (LVFree x) (LVFree y)
    (lstore_swap (LVFree x) (LVFree y) (lso_store s)) = lso_store s).
  unfold lstore_swap, lstore_rekey.
  apply storeA_swap_involutive.
Qed.

Definition qual_atom_swap
    (x y : atom) (q : qualifier) : qualifier :=
  match q with
  | tqual D P =>
      tqual (lvars_swap x y D)
        (fun s => P (lstore_on_atom_swap_back x y D s))
  end.

Lemma qual_atom_swap_involutive x y (q : qualifier) :
  qual_atom_swap x y (qual_atom_swap x y q) = q.
Proof.
  destruct q as [D P]. cbn [qual_atom_swap].
  apply qual_ext.
  - apply set_swap_involutive.
  - intros s1 s2 Hs. cbn [qual_prop qual_lvars].
    enough (lstore_on_atom_swap_back x y D
      (lstore_on_atom_swap_back x y (lvars_swap x y D) s1) = s2) as ->.
    { reflexivity. }
    apply lstore_on_ext.
    unfold lstore_on_atom_swap_back. cbn [lso_store storeAO_store].
    change (lstore_swap (LVFree x) (LVFree y)
      (lstore_swap (LVFree x) (LVFree y) (lso_store s1)) = lso_store s2).
    rewrite Hs.
    unfold lstore_swap, lstore_rekey.
    apply storeA_swap_involutive.
Qed.

Lemma qual_atom_swap_fresh_id x y (q : qualifier) :
  x ∉ qual_dom q ->
  y ∉ qual_dom q ->
  qual_atom_swap x y q = q.
Proof.
  destruct q as [D P]. cbn [qual_atom_swap qual_dom qual_lvars].
  intros Hx Hy.
  apply qual_ext.
  - apply lvars_swap_fresh; assumption.
  - intros s1 s2 Hs. cbn [qual_prop qual_lvars].
    enough (lstore_on_atom_swap_back x y D s1 = s2) as -> by reflexivity.
    apply lstore_on_ext.
    unfold lstore_on_atom_swap_back. cbn [lso_store storeAO_store].
    change (lstore_swap (LVFree x) (LVFree y) (lso_store s1) =
      lso_store s2).
    rewrite Hs.
    apply storeA_swap_fresh.
    + intros Hbad. apply Hx. apply lvars_fv_elem.
      rewrite <- (lso_dom s2). exact Hbad.
    + intros Hbad. apply Hy. apply lvars_fv_elem.
      rewrite <- (lso_dom s2). exact Hbad.
Qed.

Lemma qual_atom_swap_open_conjugate k x y z q :
  qual_atom_swap x y (qual_open_atom k (swap x y z) q) =
  qual_open_atom k z (qual_atom_swap x y q).
Proof.
  destruct q as [D P]. cbn [qual_atom_swap qual_open_atom].
  apply qual_ext.
  - apply lvars_swap_open_conjugate.
  - intros s1 s2 Hs. cbn [qual_prop qual_lvars].
    enough
      (lstore_on_open_back k (swap x y z) D
        (lstore_on_atom_swap_back x y (lvars_open k (swap x y z) D) s1) =
       lstore_on_atom_swap_back x y D
        (lstore_on_open_back k z (lvars_swap x y D) s2)) as ->.
    { reflexivity. }
    apply lstore_on_ext.
    unfold lstore_on_open_back, lstore_on_atom_swap_back.
    cbn [lso_store storeAO_store].
    change (lstore_swap (LVBound k) (LVFree (swap x y z))
      (lstore_swap (LVFree x) (LVFree y) (lso_store s1)) =
      lstore_swap (LVFree x) (LVFree y)
        (lstore_swap (LVBound k) (LVFree z) (lso_store s2))).
    rewrite Hs.
    unfold lstore_swap, lstore_rekey.
    change (storeA_swap (LVBound k) (LVFree (swap x y z))
      (storeA_swap (LVFree x) (LVFree y) (lso_store s2) : LStoreT) =
      storeA_swap (LVFree x) (LVFree y)
        (storeA_swap (LVBound k) (LVFree z) (lso_store s2) : LStoreT)).
    rewrite (storeA_swap_conjugate_inv
      (LVFree x) (LVFree y) (LVBound k) (LVFree (swap x y z))).
    replace (swap (LVFree x) (LVFree y) (LVBound k)) with (LVBound k)
      by (unfold swap; repeat destruct decide; congruence).
    replace (swap (LVFree x) (LVFree y) (LVFree (swap x y z)))
      with (LVFree z)
      by (unfold swap; repeat destruct decide; congruence).
    reflexivity.
Qed.

Definition qual_mlsubst (ρ : LStoreT) (q : qualifier) : qualifier :=
  match q with
  | tqual D P =>
      tqual (D ∖ dom (ρ : gmap logic_var V))
        (fun s => P (lstore_on_mlsubst_back D ρ s))
  end.

Lemma qual_mlsubst_empty (q : qualifier) :
  qual_mlsubst (∅ : LStoreT) q = q.
Proof.
  destruct q as [D P]. cbn [qual_mlsubst].
  apply qual_ext.
  - change (D ∖ (∅ : lvset) = D).
    apply difference_empty_L.
  - intros s1 s2 Hs. cbn [qual_prop qual_lvars].
    enough (lstore_on_mlsubst_back D (∅ : LStoreT) s1 = s2) as ->.
    { reflexivity. }
    apply lstore_on_ext.
    unfold lstore_on_mlsubst_back. cbn [lso_store storeAO_store].
    change ((@union (gmap logic_var V) _ (lso_store s1)
      (storeA_restrict (∅ : LStoreT) D) : LStoreT) = lso_store s2).
    rewrite Hs.
    assert (Hempty : storeA_restrict (∅ : LStoreT) D = (∅ : LStoreT)).
    {
      apply storeA_map_eq. intros v.
      rewrite storeA_restrict_lookup_none_l; [reflexivity|].
      rewrite lookup_empty. reflexivity.
    }
    rewrite Hempty.
    rewrite (right_id_L ∅ (∪)). reflexivity.
Qed.

Lemma qual_mlsubst_merge ρ_outer ρ_inner q :
  dom (ρ_outer : gmap logic_var V) ##
    dom (ρ_inner : gmap logic_var V) ->
  qual_mlsubst ρ_inner (qual_mlsubst ρ_outer q) =
  qual_mlsubst (ρ_outer ∪ ρ_inner) q.
Proof.
  intros Hdisj.
  destruct q as [D P]. cbn [qual_mlsubst].
  apply qual_ext.
  - set_solver.
  - intros s1 s2 Hs. cbn [qual_prop qual_lvars].
    pose proof (lstore_on_mlsubst_back_merge
      D ρ_outer ρ_inner s1 s2 Hdisj Hs) as Hmerge.
    rewrite Hmerge. reflexivity.
Qed.

Lemma qual_atom_swap_mlsubst x y (ρ : LStoreT) q :
  qual_atom_swap x y (qual_mlsubst ρ q) =
  qual_mlsubst (lvar_store_swap x y ρ) (qual_atom_swap x y q).
Proof.
  destruct q as [D P]. cbn [qual_atom_swap qual_mlsubst].
  apply qual_ext.
  - transitivity (set_swap (LVFree x) (LVFree y) D ∖
      set_swap (LVFree x) (LVFree y) (dom (ρ : LStoreT))).
    + apply set_swap_difference.
    + apply (f_equal (fun R =>
        set_swap (LVFree x) (LVFree y) D ∖ R)).
      symmetry. apply lvar_store_swap_dom.
  - intros s1 s2 Hs. cbn [qual_prop qual_lvars].
    enough (lstore_on_mlsubst_back D ρ
      (lstore_on_atom_swap_back x y (D ∖ dom (ρ : LStoreT)) s1) =
      lstore_on_atom_swap_back x y D
        (lstore_on_mlsubst_back (lvars_swap x y D)
          (lvar_store_swap x y ρ) s2)) as <-.
    { reflexivity. }
    apply lstore_on_ext.
    unfold lstore_on_mlsubst_back, lstore_on_atom_swap_back.
    cbn [lso_store storeAO_store].
    change ((@union (gmap logic_var V) _
        (lstore_swap (LVFree x) (LVFree y) (lso_store s1))
        (storeA_restrict ρ D) : LStoreT) =
      lstore_swap (LVFree x) (LVFree y)
        (@union (gmap logic_var V) _ (lso_store s2)
          (storeA_restrict (lvar_store_swap x y ρ) (lvars_swap x y D)))).
    rewrite Hs.
    unfold lstore_swap, lstore_rekey, lvar_store_swap.
    change ((@union (gmap logic_var V) _
        (storeA_swap (LVFree x) (LVFree y) (lso_store s2))
        (storeA_restrict ρ D) : LStoreT) =
      storeA_swap (LVFree x) (LVFree y)
        (@union (gmap logic_var V) _ (lso_store s2)
          (storeA_restrict (storeA_swap (LVFree x) (LVFree y) ρ)
            (lvars_swap x y D)))).
    rewrite storeA_swap_union.
    f_equal.
    rewrite storeA_restrict_swap.
    rewrite storeA_swap_involutive.
    reflexivity.
Qed.

Definition qual_msubst_store (σ : StoreT) (q : qualifier) :
    qualifier :=
  qual_mlsubst (atom_store_to_lvar_store σ) q.

Lemma qual_msubst_store_merge σ_outer σ_inner q :
  dom (σ_outer : StoreT) ## dom (σ_inner : StoreT) ->
  qual_msubst_store σ_inner (qual_msubst_store σ_outer q) =
  qual_msubst_store (σ_outer ∪ σ_inner) q.
Proof.
  intros Hdisj.
  unfold qual_msubst_store.
  rewrite atom_store_to_lvar_store_union.
  apply qual_mlsubst_merge.
  rewrite !atom_store_to_lvar_store_dom.
  unfold lvars_of_atoms.
  set_solver.
Qed.

Lemma qual_mlsubst_open_atom_fresh ρ k x q :
  (forall j, LVBound j ∉ dom (ρ : gmap logic_var V)) ->
  LVFree x ∉ dom (ρ : gmap logic_var V) ->
  qual_mlsubst ρ (qual_open_atom k x q) =
  qual_open_atom k x (qual_mlsubst ρ q).
Proof.
  intros Hbound Hfree.
  destruct q as [D P]. cbn [qual_mlsubst qual_open_atom].
  apply qual_ext.
  - symmetry.
    apply (set_swap_difference_fresh (LVBound k) (LVFree x) D
      (dom (ρ : gmap logic_var V)));
      [apply Hbound|exact Hfree].
  - intros s1 s2 Hs. cbn [qual_prop qual_lvars].
    pose proof (lstore_on_open_mlsubst_back_fresh k x D ρ
      s2 s1 (Hbound k) Hfree ltac:(symmetry; exact Hs)) as Heq.
    rewrite Heq. reflexivity.
Qed.

Lemma qual_msubst_store_open_atom_fresh σ k x q :
  x ∉ dom (σ : StoreT) ->
  qual_msubst_store σ (qual_open_atom k x q) =
  qual_open_atom k x (qual_msubst_store σ q).
Proof.
  intros Hx.
  unfold qual_msubst_store.
  apply qual_mlsubst_open_atom_fresh.
  - intros j Hj.
    rewrite atom_store_to_lvar_store_dom in Hj.
    unfold lvars_of_atoms in Hj.
    apply elem_of_map in Hj as [a [Hbad _]]. discriminate.
  - rewrite atom_store_to_lvar_store_dom.
    unfold lvars_of_atoms.
    intros Hbad. apply elem_of_map in Hbad as [a [Heq Ha]].
    inversion Heq. subst. exact (Hx Ha).
Qed.

Definition qual_open_env (η : gmap nat atom) (q : qualifier) : qualifier :=
  map_fold (fun k x acc => qual_open_atom k x acc) q η.

Lemma qual_open_env_empty q :
  qual_open_env ∅ q = q.
Proof.
  unfold qual_open_env. rewrite map_fold_empty. reflexivity.
Qed.

Definition qual_top_on (D : lvset) : qualifier :=
  tqual D (fun _ => True).

Notation qual_top := (qual_top_on {[LVBound 0]}).

Lemma qual_vars_top_on D :
  qual_vars (qual_top_on D) = D.
Proof. reflexivity. Qed.

Lemma qual_lvars_top_on D :
  qual_lvars (qual_top_on D) = D.
Proof. reflexivity. Qed.

Lemma qual_dom_top_on D :
  qual_dom (qual_top_on D) = lvars_fv D.
Proof. reflexivity. Qed.

Lemma qual_open_atom_top_on k x D :
  qual_open_atom k x (qual_top_on D) = qual_top_on (lvars_open k x D).
Proof.
  apply qual_ext; cbn [qual_lvars qual_prop qual_open_atom].
  - reflexivity.
  - intros s1 s2 Hs. split; intros _; exact I.
Qed.

Definition qual_and (q1 q2 : qualifier) : qualifier :=
  match q1, q2 with
  | tqual D1 P1, tqual D2 P2 =>
      tqual (D1 ∪ D2)
        (fun s =>
           P1 (lstore_on_restrict D1 s ltac:(set_solver)) /\
           P2 (lstore_on_restrict D2 s ltac:(set_solver)))
  end.

Definition lc_qualifier (q : qualifier) : Prop :=
  lc_lvars (qual_lvars q).

Definition body_qualifier (q : qualifier) : Prop :=
  exists L : aset, forall x : atom, x ∉ L -> lc_qualifier (qual_open_atom 0 x q).

#[global] Instance stale_qualifier : Stale qualifier := qual_dom.
Arguments stale_qualifier /.

#[global] Instance open_qual_atom_inst : Open atom qualifier := qual_open_atom.
Arguments open_qual_atom_inst /.

#[global] Instance lc_qual_inst : Lc qualifier := lc_qualifier.
Arguments lc_qual_inst /.

Notation "q '^q^' x" := (qual_open_atom 0 x q) (at level 20).

Lemma qual_open_atom_vars k x q :
  qual_vars (qual_open_atom k x q) = lvars_open k x (qual_vars q).
Proof.
  destruct q. reflexivity.
Qed.

Lemma qual_open_env_vars η q :
  open_env_fresh_for_lvars η (qual_vars q) ->
  qual_vars (qual_open_env η q) = lvars_open_env η (qual_vars q).
Proof.
  revert q.
  induction η as [|k x η Hnone Hfold IH] using fin_maps.map_fold_ind.
  - intros q _. rewrite qual_open_env_empty, lvars_open_env_empty.
    reflexivity.
  - intros q Hfresh.
    pose proof (IH q
      ltac:(eapply open_env_fresh_for_lvars_insert_tail; eassumption))
      as HIH.
    change (qual_vars
      (map_fold (fun k x acc => qual_open_atom k x acc) q (<[k:=x]> η)) =
      lvars_open_env (<[k:=x]> η) (qual_vars q)).
    rewrite (Hfold qualifier (fun k x acc => qual_open_atom k x acc)).
    fold (qual_open_env η q).
    rewrite qual_open_atom_vars.
    rewrite HIH.
    rewrite lvars_open_env_insert_fresh.
    + reflexivity.
    + exact Hnone.
    + eapply open_env_fresh_for_lvars_insert_head; eassumption.
Qed.

Lemma qual_open_atom_dom_subset k x q :
  qual_dom (qual_open_atom k x q) ⊆ qual_dom q ∪ {[x]}.
Proof.
  destruct q as [D P]. cbn [qual_dom qual_open_atom qual_lvars].
  apply lvars_fv_open_subset.
Qed.

Lemma qual_open_commute_fvar i j x y q :
  i <> j ->
  x <> y ->
  qual_open_atom i x (qual_open_atom j y q) =
  qual_open_atom j y (qual_open_atom i x q).
Proof.
  intros Hij Hxy.
  destruct q as [D P].
  apply qual_ext.
  - cbn [qual_lvars qual_open_atom].
    rewrite set_swap_conjugate.
    replace (swap (LVBound i) (LVFree x) (LVBound j))
      with (LVBound j).
    2:{ better_base_solver. }
    replace (swap (LVBound i) (LVFree x) (LVFree y))
      with (LVFree y).
    2:{ better_base_solver. }
    reflexivity.
  - intros s1 s2 Hs.
    cbn [qual_prop qual_open_atom].
    assert (Hback :
      lstore_on_open_back j y D
        (lstore_on_open_back i x (lvars_open j y D) s1) =
      lstore_on_open_back i x D
        (lstore_on_open_back j y (lvars_open i x D) s2)).
    {
      apply lstore_on_ext.
      cbn [lso_store].
      unfold lstore_on_open_back. cbn [lso_store].
      change (lstore_swap (LVBound j) (LVFree y)
          (lstore_swap (LVBound i) (LVFree x) (lso_store s1)) =
        lstore_swap (LVBound i) (LVFree x)
          (lstore_swap (LVBound j) (LVFree y) (lso_store s2))).
      rewrite <- Hs.
      symmetry.
      unfold lstore_swap, lstore_rekey.
      apply storeA_swap_commute_fresh; congruence.
    }
    rewrite Hback. tauto.
Qed.

Lemma qual_open_atom_commute_fresh i j x y q :
  i <> j ->
  x <> y ->
  qual_open_atom i x (qual_open_atom j y q) =
  qual_open_atom j y (qual_open_atom i x q).
Proof. apply qual_open_commute_fvar. Qed.

Lemma qual_open_env_insert_fresh η k x q :
  η !! k = None ->
  open_env_avoids_atom x η ->
  open_env_values_inj η ->
  qual_open_env (<[k := x]> η) q =
  qual_open_atom k x (qual_open_env η q).
Proof.
  intros Hfresh Havoid Hinj.
  unfold qual_open_env.
  apply (map_fold_insert_L (M:=gmap nat) (A:=atom) (B:=qualifier)
    (fun k x acc => qual_open_atom k x acc) q k x η).
  - intros i j xi xj acc Hij Hi Hj.
    apply (qual_open_commute_fvar _ _ _ _ _ Hij).
    intros Heq. subst xj.
    pose proof (open_env_values_inj_insert k x η Hfresh Havoid Hinj)
      as Hinj'.
    apply Hij. eapply Hinj'; eassumption.
  - exact Hfresh.
Qed.

(** ** Qualifier Renaming

    Opening remains the primitive operation in [Qualifier.v], because it is the
    same involutive swap used by logic qualifiers.  Context-type denotation also needs
    binder-depth shifts; those are represented here as a renaming transport:
    the domain is renamed, and the new predicate holds exactly when the input
    store is the renamed image of an old input store satisfying the old
    predicate. *)

Definition qual_rename
    (f : logic_var -> logic_var) (Hf : Inj (=) (=) f)
    (q : qualifier) : qualifier :=
  match q with
  | tqual D P =>
      tqual (set_map f D)
        (fun s' =>
           exists s : LStoreOnT D,
             lstore_on_rekey f Hf s = s' /\ P s)
  end.

Definition qual_shift_from (k : nat) (q : qualifier) : qualifier :=
  qual_rename (logic_var_shift_from k) (logic_var_shift_from_inj k) q.

#[global] Instance shift_qual_inst : Shift qualifier :=
  qual_shift_from.
Arguments shift_qual_inst /.

Lemma qual_shift_from_vars k q :
  qual_vars (qual_shift_from k q) = lvars_shift_from k (qual_vars q).
Proof.
  destruct q. reflexivity.
Qed.

Lemma qual_open_shift_from_under_gen j k x q :
  j <= k ->
  qual_open_atom (S k) x (qual_shift_from j q) =
  qual_shift_from j (qual_open_atom k x q).
Proof.
  intros Hjk.
  destruct q as [D P].
  apply qual_ext; cbn [qual_lvars qual_prop qual_open_atom qual_shift_from
    qual_rename].
  - apply lvars_open_shift_from_under_gen. exact Hjk.
  - intros s1 s2 Hs.
    split.
    + intros [s [Hshift HP]].
      exists (lstore_on_open_front k x s). split.
      * apply lstore_on_ext.
        rewrite <- Hs.
        change (lso_store (lstore_on_shift_from j (lstore_on_open_front k x s)) =
          lso_store s1).
        rewrite lstore_on_shift_from_open_front by exact Hjk.
        replace (lstore_on_shift_from j s) with
          (lstore_on_open_back (S k) x
            (set_map (logic_var_shift_from j) D) s1)
          by (symmetry; exact Hshift).
        rewrite lstore_on_open_front_back. reflexivity.
      * rewrite lstore_on_open_back_front. exact HP.
    + intros [s [Hshift HP]].
      exists (lstore_on_open_back k x D s). split.
      * apply lstore_on_ext.
        change (lso_store (lstore_on_shift_from j (lstore_on_open_back k x D s)) =
          lso_store (lstore_on_open_back (S k) x
            (set_map (logic_var_shift_from j) D) s1)).
        rewrite lstore_on_shift_from_open_back by exact Hjk.
        replace (lso_store (lstore_on_shift_from j s)) with (lso_store s2)
          by (rewrite <- Hshift; reflexivity).
        transitivity (lstore_swap (LVBound (S k)) (LVFree x) (lso_store s1)).
        -- rewrite Hs. reflexivity.
        -- unfold lstore_on_open_back. cbn [lso_store]. reflexivity.
      * exact HP.
Qed.

Lemma qual_open_shift_from_lc_fresh k x q :
  lvars_lc_at k (qual_vars q) ->
  x ∉ qual_dom q ->
  qual_open_atom k x (qual_shift_from k q) = q.
Proof.
  intros Hlc Hx.
  destruct q as [D P].
  apply qual_ext; cbn [qual_vars qual_dom qual_lvars qual_prop
    qual_open_atom qual_shift_from qual_rename].
  - apply lvars_open_shift_from_lc_at_fresh; assumption.
  - intros s1 s2 Hs.
    assert (Hshift_id : forall (s : LStoreOnT D),
      lso_store (lstore_on_shift_from k s) = lso_store s).
    {
      intros s.
      apply lstore_shift_from_below_id. exact Hlc.
    }
    assert (Hopen_id :
      lso_store
        (lstore_on_open_back k x (lvars_shift_from k D) s1) =
      lso_store s1).
    {
      apply storeA_swap_fresh.
      - intros Hbad.
        pose proof Hbad as HbadD.
        pose proof (lso_dom s1) as Hdoms1.
        change (LVBound k ∈ dom (lso_store s1 : LStoreT)) in HbadD.
        rewrite Hdoms1 in HbadD.
        apply elem_of_set_swap in HbadD.
        unfold swap in HbadD.
        rewrite decide_True in HbadD by reflexivity.
        destruct (decide (LVFree x = LVBound k)) as [Hbad_eq|_];
          [discriminate|].
        apply elem_of_map in HbadD as [v [Hv HvD]].
        destruct v as [n|a]; cbn [logic_var_shift_from] in Hv.
        + repeat case_decide; inversion Hv.
        + inversion Hv. subst a.
          apply Hx. apply lvars_fv_elem. exact HvD.
      - intros Hbad.
        pose proof Hbad as HbadD.
        pose proof (lso_dom s1) as Hdoms1.
        change (LVFree x ∈ dom (lso_store s1 : LStoreT)) in HbadD.
        rewrite Hdoms1 in HbadD.
        apply elem_of_set_swap in HbadD.
        unfold swap in HbadD.
        destruct (decide (LVBound k = LVFree x)) as [Hbad_eq|Hneq];
          [discriminate|].
        rewrite decide_False in HbadD by (intros Heq; apply Hneq; symmetry; exact Heq).
        rewrite decide_True in HbadD by reflexivity.
        apply elem_of_map in HbadD as [v [Hv HvD]].
        destruct v as [n|a]; cbn [logic_var_shift_from] in Hv.
        + destruct (decide (k <= n)) as [Hkn|Hkn].
          * inversion Hv. lia.
          * inversion Hv. subst n.
            specialize (Hlc k ltac:(rewrite lvars_bv_elem; exact HvD)).
            lia.
        + discriminate.
    }
    split.
    + intros [s [Hshift HP]].
      pose proof (f_equal (@lso_store V _) Hshift) as Hshift_store.
      assert (Hs_eq : s = s2).
      {
        apply lstore_on_ext.
        transitivity (lso_store (lstore_on_shift_from k s)).
        - symmetry. apply Hshift_id.
        - transitivity
            (lso_store (lstore_on_open_back k x (lvars_shift_from k D) s1)).
          + exact Hshift_store.
          + rewrite Hopen_id. exact Hs.
      }
      subst s. exact HP.
    + intros HP.
      exists s2. split; [|exact HP].
      apply lstore_on_ext.
      transitivity (lso_store s2).
      { apply Hshift_id. }
      transitivity (lso_store s1).
      { symmetry. exact Hs. }
      symmetry. exact Hopen_id.
Qed.

Lemma qual_open_atom_fresh_lc_at k x q :
  (forall n, n ∈ lvars_bv (qual_vars q) -> n < k) ->
  x ∉ qual_dom q ->
  qual_open_atom k x q = q.
Proof.
  intros Hbelow Hx.
  destruct q as [D P].
  apply qual_ext; cbn [qual_vars qual_dom qual_lvars qual_prop
    qual_open_atom].
  - apply lvars_open_fresh_index.
    + intros Hk. specialize (Hbelow k Hk). lia.
    + exact Hx.
  - intros s1 s2 Hs.
    assert (Hopen_id :
      lso_store (lstore_on_open_back k x D s1) = lso_store s1).
    {
      apply storeA_swap_fresh.
      - intros Hbad.
        pose proof Hbad as HbadD.
        change (LVBound k ∈ dom (lso_store s1 : LStoreT)) in HbadD.
        rewrite (lso_dom s1) in HbadD.
        apply elem_of_set_swap in HbadD.
        unfold swap in HbadD.
        rewrite decide_True in HbadD by reflexivity.
        destruct (decide (LVFree x = LVBound k)) as [Hbad_eq|_];
          [discriminate|].
        apply Hx. apply lvars_fv_elem. exact HbadD.
      - intros Hbad.
        pose proof Hbad as HbadD.
        change (LVFree x ∈ dom (lso_store s1 : LStoreT)) in HbadD.
        rewrite (lso_dom s1) in HbadD.
        apply elem_of_set_swap in HbadD.
        unfold swap in HbadD.
        destruct (decide (LVBound k = LVFree x)) as [Hbad_eq|Hneq];
          [discriminate|].
        rewrite decide_False in HbadD by
          (intros Heq; apply Hneq; symmetry; exact Heq).
        rewrite decide_True in HbadD by reflexivity.
        specialize (Hbelow k ltac:(rewrite lvars_bv_elem; exact HbadD)).
        lia.
    }
    assert (Hback_eq : lstore_on_open_back k x D s1 = s2).
    {
      apply lstore_on_ext.
      rewrite Hopen_id. exact Hs.
    }
    split.
    + intros HP.
      rewrite Hback_eq in HP. exact HP.
    + intros HP.
      rewrite Hback_eq. exact HP.
Qed.

End Qualifier.

Notation type_qualifier := (qualifier (V := value)) (only parsing).
Notation qual_top := (qual_top_on (V := value) {[LVBound 0]}).
