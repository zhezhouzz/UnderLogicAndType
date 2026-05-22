(** * ChoiceType.QualifierBridge

    Bridges from type-level shallow qualifiers to Choice Logic atoms.

    The raw [type_qualifier] syntax and its local operations live in
    [Qualifier].  This file contains the denotational lift that depends on the
    Choice Logic world structure. *)

From ChoiceType Require Export Qualifier.
From ChoiceType Require Import QualifierProps.

Definition bstore_of_env (η : gmap nat atom) (σ : Store) : gmap nat value :=
  map_fold (λ k x β,
    match σ !! x with
    | Some v => <[k := v]> β
    | None => β
    end) ∅ η.

Lemma bstore_of_env_lookup η σ k :
  bstore_of_env η σ !! k =
  match η !! k with
  | Some x => σ !! x
  | None => None
  end.
Proof.
  unfold bstore_of_env.
  refine (fin_maps.map_fold_ind
    (fun η => ∀ k,
      map_fold
        (fun (j : nat) (x : atom) (β : gmap nat value) =>
          match σ !! x with
          | Some v => <[j:=v]> β
          | None => β
          end) ∅ η !! k =
      match η !! k with
      | Some x => σ !! x
      | None => None
      end) _ _ η k).
  - intros i. rewrite map_fold_empty, lookup_empty. reflexivity.
  - intros j x η' Hfresh Hfold IH i.
    rewrite Hfold.
    destruct (σ !! x) as [v|] eqn:Hx.
    + destruct (decide (i = j)) as [->|Hij].
      * rewrite (lookup_insert_eq
          (map_fold
            (fun (j : nat) (x : atom) (β : gmap nat value) =>
              match σ !! x with
              | Some v => <[j:=v]> β
              | None => β
              end) ∅ η') j v).
        rewrite (lookup_insert_eq η' j x).
        symmetry. exact Hx.
      * rewrite lookup_insert_ne by congruence.
        rewrite lookup_insert_ne by congruence.
        apply IH.
    + destruct (decide (i = j)) as [->|Hij].
      * rewrite IH, Hfresh.
        rewrite (lookup_insert_eq η' j x).
        symmetry. exact Hx.
      * rewrite lookup_insert_ne by congruence.
        apply IH.
Qed.

Lemma bstore_of_env_insert_restrict_some η σ k x v B :
  σ !! x = Some v →
  map_restrict value (bstore_of_env (<[k := x]> η) σ) B =
  map_restrict value (<[k := v]> (bstore_of_env η σ)) B.
Proof.
  intros Hx.
  apply map_restrict_agree. intros j _.
  rewrite bstore_of_env_lookup.
  destruct (decide (j = k)) as [->|Hjk].
  - rewrite (lookup_insert_eq η k x).
    rewrite (lookup_insert_eq (bstore_of_env η σ) k v).
    exact Hx.
  - rewrite lookup_insert_ne by congruence.
    rewrite lookup_insert_ne by congruence.
    symmetry. apply bstore_of_env_lookup.
Qed.

Lemma bstore_of_env_insert_restrict_absent η σ k x B :
  k ∉ B →
  map_restrict value (bstore_of_env (<[k := x]> η) σ) B =
  map_restrict value (bstore_of_env η σ) B.
Proof.
  intros Hk.
  apply map_restrict_agree. intros j Hj.
  rewrite bstore_of_env_lookup.
  destruct (decide (j = k)) as [->|Hjk]; [set_solver |].
  rewrite lookup_insert_ne by congruence.
  symmetry. apply bstore_of_env_lookup.
Qed.

Lemma map_restrict_insert_present
    (β : gmap nat value) B k v :
  k ∈ B →
  map_restrict value (<[k := v]> β) B =
  <[k := v]> (map_restrict value β (B ∖ {[k]})).
Proof.
  intros Hk.
  apply map_eq. intros j.
  change ((map_restrict value (<[k:=v]> β) B : gmap nat value) !! j =
    (<[k:=v]> (map_restrict value β (B ∖ {[k]})) : gmap nat value) !! j).
  destruct (decide (j = k)) as [->|Hjk].
  - rewrite (lookup_insert_eq (map_restrict value β (B ∖ {[k]})) k v).
    unfold map_restrict.
    apply map_lookup_filter_Some_2.
    + apply lookup_insert_eq.
    + exact Hk.
  - rewrite lookup_insert_ne by congruence.
    unfold map_restrict.
    destruct (decide (j ∈ B)) as [HjB|HjB].
    + destruct (β !! j) as [vj|] eqn:Hβj.
      * transitivity (Some vj).
        -- apply map_lookup_filter_Some_2.
           ++ rewrite lookup_insert_ne by congruence. exact Hβj.
           ++ exact HjB.
        -- symmetry. apply map_lookup_filter_Some_2.
           ++ exact Hβj.
           ++ set_solver.
      * transitivity (@None value).
        -- apply map_lookup_filter_None_2.
           left. rewrite lookup_insert_ne by congruence. exact Hβj.
        -- symmetry. apply map_lookup_filter_None_2.
           left. exact Hβj.
    + rewrite map_lookup_filter_None_2.
      2:{ right. intros z _ Hz. exact (HjB Hz). }
      rewrite map_lookup_filter_None_2.
      2:{ right. intros z _ Hz. set_solver. }
      reflexivity.
Qed.

Lemma bstore_of_env_insert_dom_open η σ k x v D :
  σ !! x = Some v →
  (lvars_bv D ⊆ dom (bstore_of_env (<[k := x]> η) σ) ↔
   lvars_bv (lvars_open k x D) ⊆ dom (bstore_of_env η σ)).
Proof.
  intros Hx. split.
  - intros Hdom j Hj.
    rewrite lvars_bv_open in Hj.
    apply elem_of_difference in Hj as [HjD Hjk].
    specialize (Hdom j HjD).
    apply elem_of_dom in Hdom as [vj Hlookup].
    rewrite bstore_of_env_lookup in Hlookup.
    rewrite lookup_insert_ne in Hlookup by set_solver.
    apply elem_of_dom. exists vj.
    rewrite bstore_of_env_lookup. exact Hlookup.
  - intros Hdom j HjD.
    destruct (decide (j = k)) as [->|Hjk].
    + apply elem_of_dom. exists v.
      rewrite bstore_of_env_lookup, lookup_insert.
      destruct (decide (k = k)) as [_|Hbad]; [exact Hx | congruence].
    + assert (Hjopen : j ∈ lvars_bv (lvars_open k x D)).
      {
        rewrite lvars_bv_open. apply elem_of_difference.
        split; [exact HjD | set_solver].
      }
      specialize (Hdom j Hjopen).
      apply elem_of_dom in Hdom as [vj Hlookup].
      apply elem_of_dom. exists vj.
      rewrite !bstore_of_env_lookup in *.
      rewrite lookup_insert_ne by congruence.
      exact Hlookup.
Qed.

Lemma bstore_of_env_insert_dom_absent η σ k x B :
  k ∉ B →
  (B ⊆ dom (bstore_of_env (<[k := x]> η) σ) ↔
   B ⊆ dom (bstore_of_env η σ)).
Proof.
  intros Hk. split.
  - intros Hdom j Hj.
    specialize (Hdom j Hj).
    apply elem_of_dom in Hdom as [vj Hlookup].
    apply elem_of_dom. exists vj.
    rewrite !bstore_of_env_lookup in *.
    rewrite lookup_insert_ne in Hlookup by set_solver.
    exact Hlookup.
  - intros Hdom j Hj.
    specialize (Hdom j Hj).
    apply elem_of_dom in Hdom as [vj Hlookup].
    apply elem_of_dom. exists vj.
    rewrite !bstore_of_env_lookup in *.
    rewrite lookup_insert_ne by set_solver.
    exact Hlookup.
Qed.

Lemma bstore_of_env_insert_dom_requires_value η σ k x B :
  k ∈ B →
  B ⊆ dom (bstore_of_env (<[k := x]> η) σ) →
  ∃ v, σ !! x = Some v.
Proof.
  intros Hk Hdom.
  specialize (Hdom k Hk).
  apply elem_of_dom in Hdom as [v Hv].
  rewrite bstore_of_env_lookup in Hv.
  rewrite lookup_insert in Hv.
  destruct (decide (k = k)) as [_|Hbad]; [| congruence].
  destruct (σ !! x) as [vx|] eqn:Hx; [eauto | discriminate].
Qed.

(** Formula-level lift of a type qualifier.

    A type qualifier is a shallow predicate over an explicit store and a
    singleton result-resource.  [FTypeQualifier] exposes that shape directly as
    a [FStoreResourceAtom], instead of first manufacturing an intermediate
    logic qualifier. *)
Definition FTypeQualifier (q : type_qualifier) : Formula :=
  match q with
  | qual D p =>
      FStoreResourceAtom D (fun η σ (w : WfWorld) =>
        let β := bstore_of_env η σ in
        lvars_bv D ⊆ dom β ∧
        ∃ σw, (w : World) = singleton_world σw ∧
          p (map_restrict value β (lvars_bv D))
            (store_restrict σ (lvars_fv D))
            (store_restrict σw (lvars_fv D)))
  end.

Lemma formula_fv_FTypeQualifier q :
  formula_fv (FTypeQualifier q) = qual_dom q.
Proof.
  destruct q. unfold FTypeQualifier, FStoreResourceAtom. simpl.
  reflexivity.
Qed.
