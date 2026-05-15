(** * ChoiceTyping.ResultWorldBridge

    Bridges between expression-result formulas and the concrete result worlds
    used by the soundness proof. *)

From CoreLang Require Import Instantiation InstantiationProps OperationalProps
  LocallyNamelessProps.
From ChoiceTyping Require Export SoundnessCommon.
From ChoiceTyping Require Export LetResultWorld.
From ChoiceTyping Require Export ResultWorldClosed.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

Lemma store_restrict_union_singleton_fresh_eq
    (σ : Store) (X : aset) (x : atom) :
  σ !! x = None →
  store_restrict σ (X ∪ {[x]}) = store_restrict σ X.
Proof.
  intros Hfresh.
  apply (map_eq (M := gmap atom)). intros z.
  rewrite !store_restrict_lookup.
  destruct (decide (z ∈ X ∪ {[x]})) as [HzU|HzU];
    destruct (decide (z ∈ X)) as [HzX|HzX]; try reflexivity.
  - assert (z = x) by set_solver. subst z. exact Hfresh.
  - set_solver.
Qed.

Lemma store_restrict_accum_cons_projection
    (ρ σ : Store) (X S : aset) (x : atom) :
  x ∉ S →
  dom ρ ## ({[x]} ∪ S) →
  store_restrict (ρ ∪ store_restrict σ ({[x]} ∪ S)) X =
  store_restrict ((ρ ∪ store_restrict σ {[x]}) ∪ store_restrict σ S) X.
Proof.
  intros HxS Hdisj.
  apply (map_eq (M := gmap atom)). intros z.
  rewrite !store_restrict_lookup.
  destruct (decide (z ∈ X)) as [HzX|HzX].
  2:{ repeat (rewrite decide_False by exact HzX); reflexivity. }
  repeat (rewrite decide_True by exact HzX).
  change (((ρ ∪ store_restrict σ ({[x]} ∪ S)) : Store) !! z =
    (((ρ ∪ store_restrict σ {[x]}) ∪ store_restrict σ S) : Store) !! z).
  destruct (decide (z ∈ dom ρ)) as [Hzρ|Hzρ].
  - apply elem_of_dom in Hzρ as [v Hv].
    rewrite (@lookup_union_l' atom (gmap atom) _ _ _ _ _ _ _ _ _
      value ρ (store_restrict σ ({[x]} ∪ S)) z ltac:(eauto)).
    rewrite (@lookup_union_l' atom (gmap atom) _ _ _ _ _ _ _ _ _
      value (ρ ∪ store_restrict σ {[x]}) (store_restrict σ S) z).
    2:{ rewrite (@lookup_union_l' atom (gmap atom) _ _ _ _ _ _ _ _ _
          value ρ (store_restrict σ {[x]}) z ltac:(eauto)).
        eauto. }
    rewrite (@lookup_union_l' atom (gmap atom) _ _ _ _ _ _ _ _ _
      value ρ (store_restrict σ {[x]}) z ltac:(eauto)).
    reflexivity.
  - rewrite !lookup_union_r by (apply not_elem_of_dom; exact Hzρ).
    rewrite !store_restrict_lookup.
    destruct (decide (z = x)) as [->|Hzx].
    + repeat (rewrite decide_True by set_solver).
      repeat (rewrite decide_False by exact HxS).
      rewrite lookup_union_l.
      2:{ rewrite store_restrict_lookup, decide_False by exact HxS. reflexivity. }
      rewrite lookup_union_r by (apply not_elem_of_dom; exact Hzρ).
      rewrite store_restrict_lookup, decide_True by set_solver.
      reflexivity.
    + destruct (decide (z ∈ S)) as [HzS|HzS].
      * repeat (rewrite decide_True by set_solver).
        rewrite lookup_union_r.
        -- rewrite store_restrict_lookup, decide_True by exact HzS.
           reflexivity.
        -- rewrite lookup_union_None. split.
           ++ apply not_elem_of_dom. exact Hzρ.
           ++ rewrite store_restrict_lookup, decide_False by set_solver.
              reflexivity.
      * repeat (rewrite decide_False by set_solver).
        rewrite lookup_union_r.
        -- rewrite store_restrict_lookup, decide_False by exact HzS.
           reflexivity.
        -- rewrite lookup_union_None. split.
           ++ apply not_elem_of_dom. exact Hzρ.
           ++ rewrite store_restrict_lookup, decide_False by set_solver.
           reflexivity.
Qed.

Lemma store_restrict_union_singleton_eq_from_parts
    (σ τ : Store) (x : atom) (S : aset) :
  x ∉ S →
  store_restrict σ {[x]} = store_restrict τ {[x]} →
  store_restrict σ S = store_restrict τ S →
  store_restrict σ ({[x]} ∪ S) = store_restrict τ ({[x]} ∪ S).
Proof.
  intros HxS Hx HS.
  apply (map_eq (M := gmap atom)). intros z.
  rewrite !store_restrict_lookup.
  destruct (decide (z ∈ {[x]} ∪ S)) as [HzU|HzU].
  2:{ repeat (rewrite decide_False by exact HzU). reflexivity. }
  repeat (rewrite decide_True by exact HzU).
  destruct (decide (z = x)) as [->|Hzx].
  - pose proof (f_equal (fun σ0 => σ0 !! x) Hx) as Hlookup.
    rewrite !store_restrict_lookup in Hlookup.
    repeat (rewrite decide_True in Hlookup by set_solver).
    exact Hlookup.
  - assert (HzS : z ∈ S) by set_solver.
    pose proof (f_equal (fun σ0 => σ0 !! z) HS) as Hlookup.
    rewrite !store_restrict_lookup in Hlookup.
    repeat (rewrite decide_True in Hlookup by exact HzS).
    exact Hlookup.
Qed.

Lemma store_restrict_union_singleton_insert_from_projection
    (σ : Store) (X : aset) (ν : atom) (v : value) :
  ν ∉ X →
  store_restrict σ {[ν]} = {[ν := v]} →
  store_restrict σ (X ∪ {[ν]}) =
    <[ν := v]> (store_restrict σ X).
Proof.
  intros HνX Hν.
  apply (map_eq (M := gmap atom)). intros z.
  rewrite store_restrict_lookup.
  destruct (decide (z = ν)) as [->|Hzν].
  - rewrite decide_True by set_solver.
    pose proof (f_equal (fun σ0 : Store => σ0 !! ν) Hν) as Hlookup.
    rewrite store_restrict_lookup in Hlookup.
    rewrite decide_True in Hlookup by set_solver.
    rewrite lookup_singleton in Hlookup.
    rewrite decide_True in Hlookup by reflexivity.
    transitivity (Some v); [exact Hlookup |].
    rewrite lookup_insert. rewrite decide_True by reflexivity. reflexivity.
  - rewrite lookup_insert_ne by congruence.
    rewrite store_restrict_lookup.
    destruct (decide (z ∈ X)) as [HzX|HzX].
    + rewrite decide_True by set_solver. reflexivity.
    + rewrite decide_False by set_solver. reflexivity.
Qed.

Lemma store_restrict_union_singleton_from_parts'
    (σ ρ σx : Store) (Fixed : aset) (x : atom) :
  x ∉ Fixed →
  dom ρ = Fixed →
  dom σx = {[x]} →
  store_restrict σ Fixed = ρ →
  store_restrict σ {[x]} = σx →
  store_restrict σ (Fixed ∪ {[x]}) = ρ ∪ σx.
Proof.
  intros HxFixed Hdomρ Hdomσx HFixed Hx.
  apply (map_eq (M := gmap atom)). intros z.
  rewrite store_restrict_lookup.
  destruct (decide (z ∈ Fixed ∪ {[x]})) as [HzU|HzU].
  2:{
    symmetry. apply lookup_union_None. split.
    - apply not_elem_of_dom. rewrite Hdomρ. set_solver.
    - apply not_elem_of_dom. rewrite Hdomσx. set_solver.
  }
  destruct (decide (z = x)) as [->|Hzx].
  - rewrite lookup_union_r.
    + pose proof (f_equal (fun s => s !! x) Hx) as Hlook.
      rewrite store_restrict_lookup in Hlook.
      rewrite decide_True in Hlook by set_solver.
      exact Hlook.
    + apply not_elem_of_dom. rewrite Hdomρ. exact HxFixed.
  - rewrite (lookup_union_l' ρ σx z).
    + pose proof (f_equal (fun s => s !! z) HFixed) as Hlook.
      rewrite store_restrict_lookup in Hlook.
      assert (HzFixed : z ∈ Fixed) by set_solver.
      rewrite decide_True in Hlook by exact HzFixed.
      exact Hlook.
    + apply elem_of_dom. rewrite Hdomρ. set_solver.
Qed.

Lemma store_restrict_union_singleton_to_parts'
    (σ ρ σx : Store) (Fixed : aset) (x : atom) :
  x ∉ Fixed →
  dom ρ = Fixed →
  dom σx = {[x]} →
  store_restrict σ (Fixed ∪ {[x]}) = ρ ∪ σx →
  store_restrict σ Fixed = ρ ∧ store_restrict σ {[x]} = σx.
Proof.
  intros HxFixed Hdomρ Hdomσx Hunion.
  split; apply (map_eq (M := gmap atom)); intros z.
  - pose proof (f_equal (fun s => s !! z) Hunion) as Hlook.
    rewrite store_restrict_lookup in Hlook.
    rewrite store_restrict_lookup.
    destruct (decide (z ∈ Fixed)) as [HzFixed|HzFixed].
    + rewrite decide_True in Hlook by set_solver.
      rewrite (lookup_union_l' ρ σx z) in Hlook.
      * exact Hlook.
      * apply elem_of_dom. rewrite Hdomρ. exact HzFixed.
    + symmetry. apply not_elem_of_dom. rewrite Hdomρ. exact HzFixed.
  - pose proof (f_equal (fun s => s !! z) Hunion) as Hlook.
    rewrite store_restrict_lookup in Hlook.
    rewrite store_restrict_lookup.
    destruct (decide (z = x)) as [->|Hzx].
    + rewrite decide_True by set_solver.
      rewrite decide_True in Hlook by set_solver.
      change (σ !! x = (ρ ∪ σx : Store) !! x) in Hlook.
      rewrite (lookup_union_r ρ σx x) in Hlook.
      * exact Hlook.
      * apply not_elem_of_dom. rewrite Hdomρ. exact HxFixed.
    + rewrite decide_False by set_solver.
      symmetry. apply not_elem_of_dom. rewrite Hdomσx. set_solver.
Qed.
