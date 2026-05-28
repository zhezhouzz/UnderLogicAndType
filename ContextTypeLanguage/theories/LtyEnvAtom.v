(** * ContextTypeLanguage.LtyEnvAtom

    Atom-environment lifting, lvar swapping, and atom-env interaction laws. *)

From LocallyNameless Require Import Classes.
From ContextStore Require Import AtomEnv.
From ContextTypeLanguage Require Export LtyEnvOpen.

Lemma atom_env_to_lty_env_dom Σ :
  dom (atom_env_to_lty_env Σ) = lvars_of_atoms (dom Σ).
Proof.
  apply atom_store_to_lvar_store_dom.
Qed.

Lemma atom_env_to_lty_env_insert x T Σ :
  atom_env_to_lty_env (<[x := T]> Σ) =
  <[LVFree x := T]> (atom_env_to_lty_env Σ).
Proof.
  apply atom_store_to_lvar_store_insert.
Qed.

Lemma atom_env_to_lty_env_closed Σ :
  lty_env_closed (atom_env_to_lty_env Σ).
Proof.
  apply atom_store_to_lvar_store_closed.
Qed.

Lemma atom_env_to_lty_env_atom_dom Σ :
  lty_env_atom_dom (atom_env_to_lty_env Σ) = dom Σ.
Proof.
  apply atom_store_to_lvar_store_atom_dom.
Qed.

Lemma atom_env_to_lty_env_lookup_bound_none Σ k :
  atom_env_to_lty_env Σ !! LVBound k = None.
Proof.
  apply atom_store_to_lvar_store_lookup_bound_none.
Qed.

Lemma atom_env_to_lty_env_lookup_free_none Δ x :
  x ∉ dom Δ ->
  atom_env_to_lty_env Δ !! LVFree x = None.
Proof.
  apply atom_store_to_lvar_store_lookup_free_none.
Qed.

Lemma atom_env_to_lty_env_lookup_free Δ x :
  atom_env_to_lty_env Δ !! LVFree x = Δ !! x.
Proof.
  apply atom_store_to_lvar_store_lookup_free.
Qed.

Lemma lty_env_shift_atom_env Σ :
  lty_env_shift (atom_env_to_lty_env Σ) = atom_env_to_lty_env Σ.
Proof.
  apply lvar_store_shift_atom_store.
Qed.

Lemma logic_var_swap_inj x y :
  Inj (=) (=) (logic_var_swap x y).
Proof.
  intros v1 v2 Heq.
  rewrite <- (logic_var_swap_involutive x y v1).
  rewrite <- (logic_var_swap_involutive x y v2).
  by rewrite Heq.
Qed.

Lemma logic_var_swap_match x y v :
  match v with
  | LVFree z => LVFree (swap x y z)
  | LVBound k => LVBound k
  end = logic_var_swap x y v.
Proof.
  destruct v as [k|z].
  - rewrite logic_var_swap_unfold.
    unfold swap. repeat destruct decide; congruence.
  - rewrite logic_var_swap_unfold, logic_var_free_swap.
    reflexivity.
Qed.

Lemma lty_env_swap_lookup x y Σ v :
  lty_env_swap x y Σ !! (match v with
                         | LVFree z => LVFree (swap x y z)
                         | LVBound k => LVBound k
                         end) = Σ !! v.
Proof.
  apply lvar_store_swap_lookup.
Qed.

Lemma lty_env_swap_lookup_inv x y Σ v :
  lty_env_swap x y Σ !! v =
  Σ !! (match v with
        | LVFree z => LVFree (swap x y z)
        | LVBound k => LVBound k
        end).
Proof.
  apply lvar_store_swap_lookup_inv.
Qed.

Lemma lty_env_swap_dom x y Σ :
  dom (lty_env_swap x y Σ) = lvars_swap x y (dom Σ).
Proof.
  apply lvar_store_swap_dom.
Qed.

Lemma lty_env_swap_insert x y Σ v T :
  lty_env_swap x y (<[v := T]> Σ) =
  <[match v with
     | LVFree z => LVFree (swap x y z)
     | LVBound k => LVBound k
     end := T]> (lty_env_swap x y Σ).
Proof.
  apply lvar_store_swap_insert.
Qed.

Lemma lty_env_swap_atom_dom x y Σ :
  lty_env_atom_dom (lty_env_swap x y Σ) =
  set_swap x y (lty_env_atom_dom Σ).
Proof.
  apply lvar_store_swap_atom_dom.
Qed.

Lemma lty_env_atom_dom_lookup_free Σ x T :
  Σ !! LVFree x = Some T ->
  x ∈ lty_env_atom_dom Σ.
Proof.
  apply lvar_store_atom_dom_lookup_free.
Qed.

Lemma lty_env_swap_fresh x y Σ :
  x ∉ lty_env_atom_dom Σ ->
  y ∉ lty_env_atom_dom Σ ->
  lty_env_swap x y Σ = Σ.
Proof.
  apply lvar_store_swap_fresh.
Qed.

Lemma lty_env_swap_atom_env_fresh Δ x y :
  x ∉ dom Δ ->
  y ∉ dom Δ ->
  lty_env_swap x y (atom_env_to_lty_env Δ) = atom_env_to_lty_env Δ.
Proof.
  intros Hx Hy.
  apply storeA_map_eq. intros v.
  rewrite lty_env_swap_lookup_inv.
  destruct v as [k|z]; cbn.
  - rewrite !atom_env_to_lty_env_lookup_bound_none. reflexivity.
  - destruct (decide (z = x)) as [->|Hzx].
    + rewrite swap_l.
      rewrite !atom_env_to_lty_env_lookup_free_none by assumption.
      reflexivity.
    + destruct (decide (z = y)) as [->|Hzy].
      * rewrite swap_r.
        rewrite !atom_env_to_lty_env_lookup_free_none by assumption.
        reflexivity.
      * rewrite swap_fresh by congruence. reflexivity.
Qed.

Lemma lty_env_swap_atom_env_insert_fresh Δ x y T :
  x ∉ dom Δ ->
  y ∉ dom Δ ->
  x <> y ->
  lty_env_swap y x (atom_env_to_lty_env (<[y := T]> Δ)) =
  <[LVFree x := T]> (atom_env_to_lty_env Δ).
Proof.
  intros Hx Hy Hxy.
  rewrite atom_env_to_lty_env_insert.
  rewrite lty_env_swap_insert.
  cbn.
  rewrite swap_l.
  rewrite lty_env_swap_atom_env_fresh by assumption.
  reflexivity.
Qed.

Lemma lty_env_open_atom_env η Σ :
  lty_env_open η (atom_env_to_lty_env Σ) = Σ.
Proof.
  apply lvar_store_open_atom_store.
Qed.

Lemma lty_env_to_atom_env_atom_env Σ :
  lty_env_to_atom_env (atom_env_to_lty_env Σ) = Σ.
Proof.
  apply lvar_store_to_atom_store_atom_store.
Qed.

Lemma lty_env_to_atom_env_lookup_some Σ x T :
  lty_env_to_atom_env Σ !! x = Some T ->
  Σ !! LVFree x = Some T.
Proof.
  apply lvar_store_to_atom_store_lookup_some.
Qed.

Lemma lty_env_to_atom_env_lookup_free_some Σ x T :
  (Σ : gmap logic_var ty) !! LVFree x = Some T ->
  lty_env_to_atom_env Σ !! x = Some T.
Proof.
  apply lvar_store_to_atom_store_lookup_free_some.
Qed.

Lemma lty_env_to_atom_env_lookup Σ x :
  lty_env_to_atom_env Σ !! x = (Σ : gmap logic_var ty) !! LVFree x.
Proof.
  apply lvar_store_to_atom_store_lookup.
Qed.

Lemma lty_env_to_atom_env_insert_free Σ x T :
  lty_env_to_atom_env (<[LVFree x := T]> Σ) =
  <[x := T]> (lty_env_to_atom_env Σ).
Proof.
  apply lvar_store_to_atom_store_insert_free.
Qed.

Lemma lty_env_to_atom_env_swap x y Σ :
  lty_env_to_atom_env (lty_env_swap x y Σ) =
  (kmap (swap x y) (lty_env_to_atom_env Σ) : gmap atom ty).
Proof.
  apply lvar_store_to_atom_store_swap.
Qed.

Lemma lty_env_to_atom_env_dom_subset Σ :
  dom (lty_env_to_atom_env Σ) ⊆ lty_env_atom_dom Σ.
Proof.
  apply lvar_store_to_atom_store_dom_subset.
Qed.

Lemma lty_env_open_one_atom_env k x Σ :
  x ∉ dom Σ ->
  lty_env_open_one k x (atom_env_to_lty_env Σ) =
  atom_env_to_lty_env Σ.
Proof.
  intros Hx.
  apply lty_env_open_one_fresh_noop.
  - intros Hin.
    change (LVBound k ∈ dom ((atom_env_to_lty_env Σ : lty_env)
      : gmap logic_var ty)) in Hin.
    apply elem_of_dom in Hin as [T HT].
    rewrite atom_env_to_lty_env_lookup_bound_none in HT. discriminate.
  - intros Hin.
    change (LVFree x ∈ dom ((atom_env_to_lty_env Σ : lty_env)
      : gmap logic_var ty)) in Hin.
    apply elem_of_dom in Hin as [T HT].
    rewrite atom_env_to_lty_env_lookup_free_none in HT by exact Hx.
    discriminate.
Qed.

Lemma lty_env_open_one_bind_atom_env x T Σ :
  x ∉ dom Σ ->
  lty_env_open_one 0 x (<[LVBound 0 := T]> (lty_env_shift (atom_env_to_lty_env Σ))) =
  <[LVFree x := T]> (atom_env_to_lty_env Σ).
Proof.
  intros Hx.
  rewrite lty_env_shift_atom_env.
  rewrite lty_env_open_one_insert.
  replace (logic_var_open 0 x (LVBound 0)) with (LVFree x).
  rewrite lty_env_open_one_atom_env by exact Hx.
  reflexivity.
  rewrite logic_var_open_unfold.
  unfold swap. repeat destruct decide; try lia; try congruence.
Qed.

Lemma lvars_shift_from_of_atoms k X :
  lvars_shift_from k (lvars_of_atoms X) = lvars_of_atoms X.
Proof.
  apply lvars_shift_from_below_id.
  intros n Hn. rewrite lvars_bv_of_atoms in Hn. set_solver.
Qed.

Lemma lty_env_bind_atom_env_dom T Σ :
  dom (<[LVBound 0 := T]> (lty_env_shift (atom_env_to_lty_env Σ))) =
  lvars_shift_from 0 (lvars_of_atoms (dom Σ)) ∪ {[LVBound 0]}.
Proof.
  rewrite lty_env_shift_atom_env.
  change (dom ((<[LVBound 0 := T]> (atom_env_to_lty_env Σ) : lty_env)
      : gmap logic_var ty) =
    lvars_shift_from 0 (lvars_of_atoms (dom Σ)) ∪ {[LVBound 0]}).
  transitivity ({[LVBound 0]} ∪
    dom ((atom_env_to_lty_env Σ : lty_env) : gmap logic_var ty)).
  { rewrite (dom_insert_L (M:=gmap logic_var) (D:=gset logic_var)
      (((atom_env_to_lty_env Σ : lty_env) : gmap logic_var ty))
      (LVBound 0) T).
    reflexivity. }
  rewrite atom_env_to_lty_env_dom.
  rewrite lvars_shift_from_of_atoms.
  set_solver.
Qed.
