(** * Merge/disprove case-study program *)

From ProofAutomation Require Import BasicTypeInfer.
From LocallyNameless Require Import Tactics.

Open Scope case_scope.
Open Scope core_scope.
Open Scope cty_scope.

Section DisproveMergeExample.

Definition merge : atom := 40%positive.
Definition xs : atom := 41%positive.
Definition ys : atom := 42%positive.
Definition h1 : atom := 43%positive.
Definition t1 : atom := 44%positive.
Definition h2 : atom := 45%positive.
Definition t2 : atom := 46%positive.
Definition t : atom := 47%positive.
Definition lt12 : atom := 48%positive.
Definition gt12 : atom := 49%positive.
Definition tail12 : atom := 50%positive.
Definition tail21 : atom := 51%positive.

Fixpoint mem_list (n : nat) (xs : list nat) : Prop :=
  match xs with
  | [] => False
  | x :: xs => n = x \/ mem_list n xs
  end.

Fixpoint sorted_from (prev : nat) (xs : list nat) : Prop :=
  match xs with
  | [] => True
  | x :: xs => prev <= x /\ sorted_from x xs
  end.

Definition sorted (xs : list nat) : Prop :=
  match xs with
  | [] => True
  | x :: xs => sorted_from x xs
  end.

Definition q_sorted_list (v : value) : type_qualifier :=
  q_list_pred v sorted.

Definition q_not_sorted_list (v : value) : type_qualifier :=
  q_list_pred v (fun xs => ~ sorted xs).

Definition OSortedList : context_ty :=
  over_ty TList (q_sorted_list ν).

Definition UNotSortedList : context_ty :=
  under_ty TList (q_not_sorted_list ν).

Definition merge_basic_ty : ty :=
  List →ᵦ List →ᵦ List.

Definition le_basic_ty : ty :=
  ℕ →ᵦ ℕ →ᵦ 𝔹.

Definition merge_safety_ty : context_ty :=
  OSortedList → OSortedList → OSortedList.

Definition merge_disprove_ty : context_ty :=
  O[ List ] → O[ List ] → OSortedList ⊕ UNotSortedList.

Definition merge_program : tm :=
  ret (μ merge, xs : List ~> List →ᵦ List =>
    ret (ƛ ys : List =>
      matchList (xs;
      Nil => ret ys;
      Cons (h1, t1) =>
        matchList (ys;
        Nil => ret xs;
        Cons (h2, t2) =>
          (let t := merge @@ (t1, t2) in
          let lt12 := h1 ⟨ < ⟩ h2 in
          if lt12 then
            let tail12 := h2 ::ᵗ t in
            h1 ::ᵗ tail12
          else
            let gt12 := h1 ⟨ > ⟩ h2 in
            if gt12 then
              let tail21 := h1 ::ᵗ t in
              h2 ::ᵗ tail21
            else
              h1 ::ᵗ t)
        )
			      ))).

Ltac merge_lookup :=
  repeat (rewrite lookup_insert_ne by
    solve [eassumption | symmetry; eassumption | vm_compute; congruence]);
  try rewrite lookup_insert;
  reflexivity.

Ltac finite_set_in :=
  first
    [ apply elem_of_singleton; reflexivity
    | apply elem_of_union_l; finite_set_in
    | apply elem_of_union_r; finite_set_in ].

Lemma merge_program_basic_type :
  ∅ ⊢ₑ merge_program ⋮ merge_basic_ty.
Proof.
  unfold merge_program, merge_basic_ty.
  repeat progress basic_type_surface_norm.
  eapply TT_Ret.
  eapply basic_typing_fixfun_named; [basic_type_fresh|basic_type_fresh|idtac].
  eapply TT_Ret.
  eapply basic_typing_lam_named; [basic_type_fresh|idtac].
  unfold match_list_named.
  eapply TT_ListMatch with
    (L := {[merge; xs; ys]});
    [basic_type|basic_type|idtac].
  intros hd tl Hhd Htl.
  unfold merge, xs, ys, h1, t1, h2, t2, t, lt12, gt12, tail12, tail21 in Hhd, Htl.
  unfold merge, xs, ys, h1, t1, h2, t2, t, lt12, gt12, tail12, tail21.
  assert (Htl_ys : tl <> 42%positive)
    by (intro Heq; subst; apply Htl; finite_set_in).
  assert (Hhd_ys : hd <> 42%positive)
    by (intro Heq; subst; apply Hhd; finite_set_in).
  assert (Htl_xs : tl <> 41%positive)
    by (intro Heq; subst; apply Htl; finite_set_in).
  assert (Hhd_xs : hd <> 41%positive)
    by (intro Heq; subst; apply Hhd; finite_set_in).
  assert (Htl_merge : tl <> 40%positive)
    by (intro Heq; subst; apply Htl; finite_set_in).
  assert (Hhd_merge : hd <> 40%positive)
    by (intro Heq; subst; apply Hhd; finite_set_in).
  assert (Htl_hd : tl <> hd)
    by (intro Heq; subst; apply Htl; finite_set_in).
  simpl.
  eapply TT_ListMatch with
    (L := {[merge; hd; tl]}).
  - eapply VT_FVar;
      rewrite lookup_insert_ne by exact Htl_ys;
      rewrite lookup_insert_ne by exact Hhd_ys;
      try rewrite lookup_insert;
      reflexivity.
  - eapply TT_Ret; eapply VT_FVar;
      rewrite lookup_insert_ne by exact Htl_xs;
      rewrite lookup_insert_ne by exact Hhd_xs;
      try rewrite lookup_insert_ne by (vm_compute; congruence);
      try rewrite lookup_insert_ne by (unfold merge; vm_compute; congruence);
      try rewrite lookup_insert;
      reflexivity.
  - 
  intros hd2 tl2 Hhd2 Htl2.
  unfold merge, xs, ys, h1, t1, h2, t2, t, lt12, gt12, tail12, tail21 in Hhd2, Htl2.
  assert (Hhd2_merge : hd2 <> 40%positive)
    by (intro Heq; subst; apply Hhd2; finite_set_in).
  assert (Htl2_merge : tl2 <> 40%positive)
    by (intro Heq; subst; apply Htl2; finite_set_in).
  assert (Hhd2_tl : hd2 <> tl)
    by (intro Heq; subst; apply Hhd2; finite_set_in).
  assert (Htl2_tl : tl2 <> tl)
    by (intro Heq; subst; apply Htl2; finite_set_in).
  assert (Hhd2_hd : hd2 <> hd)
    by (intro Heq; subst; apply Hhd2; finite_set_in).
  assert (Htl2_hd : tl2 <> hd)
    by (intro Heq; subst; apply Htl2; finite_set_in).
  assert (Htl2_hd2 : tl2 <> hd2)
    by (intro Heq; subst; apply Htl2; finite_set_in).
  simpl.
  repeat progress basic_type_surface_norm.
  eapply_tt_let_with_stales.
  { eapply TT_Let with
      (L := {[merge; hd; tl; hd2; tl2]})
      (T1 := (List →ᵦ List)).
    { eapply TT_App.
      { eapply VT_FVar. basic_lookup. }
      { eapply VT_FVar. basic_lookup. } }
    { intros f Hf.
      assert (Hf_tl2 : f <> tl2)
        by (intro Heq; subst; apply Hf; finite_set_in).
      simpl.
      eapply TT_App.
      { eapply VT_FVar. basic_lookup. }
      { eapply VT_FVar.
        rewrite lookup_insert_ne by exact Hf_tl2.
        basic_lookup. } } }
  { intros mt Hmt.
    assert (Hmt_hd : mt <> hd)
      by (intro Heq; subst; apply Hmt; finite_set_in).
    assert (Hmt_hd2 : mt <> hd2)
      by (intro Heq; subst; apply Hmt; finite_set_in).
    simpl.
    repeat progress basic_type_surface_norm.
    eapply TT_Let with
      (L := {[merge; hd; tl; hd2; tl2; mt]})
      (T1 := 𝔹).
    { eapply TT_BinOp.
      { reflexivity. }
      { eapply VT_FVar. basic_lookup. }
      { eapply VT_FVar. basic_lookup. } }
    { intros mlt Hmlt.
      assert (Hmlt_hd : mlt <> hd)
        by (intro Heq; subst; apply Hmlt; finite_set_in).
      assert (Hmlt_hd2 : mlt <> hd2)
        by (intro Heq; subst; apply Hmlt; finite_set_in).
      assert (Hmlt_mt : mlt <> mt)
        by (intro Heq; subst; apply Hmlt; finite_set_in).
      simpl.
      eapply TT_Match.
      { basic_type. }
      { eapply TT_Let with
          (L := {[merge; hd; tl; hd2; tl2; mt; mlt]})
          (T1 := TBase TList).
        { eapply TT_ListCons.
          { eapply VT_FVar. basic_lookup. }
          { eapply VT_FVar. basic_lookup. } }
        { intros mtail Hmtail.
          assert (Hmtail_hd : mtail <> hd)
            by (intro Heq; subst; apply Hmtail; finite_set_in).
          simpl.
          eapply TT_ListCons.
          { eapply VT_FVar.
            rewrite lookup_insert_ne by exact Hmtail_hd.
            basic_lookup. }
          { eapply VT_FVar. basic_lookup. } } }
      { eapply TT_Let with
          (L := {[merge; hd; tl; hd2; tl2; mt; mlt]})
          (T1 := 𝔹).
        { eapply TT_BinOp.
          { reflexivity. }
          { eapply VT_FVar. basic_lookup. }
          { eapply VT_FVar. basic_lookup. } }
        { intros mgt Hmgt.
          assert (Hmgt_hd : mgt <> hd)
            by (intro Heq; subst; apply Hmgt; finite_set_in).
          assert (Hmgt_hd2 : mgt <> hd2)
            by (intro Heq; subst; apply Hmgt; finite_set_in).
          assert (Hmgt_mt : mgt <> mt)
            by (intro Heq; subst; apply Hmgt; finite_set_in).
          simpl.
          eapply TT_Match.
          { basic_type. }
          { eapply TT_Let with
              (L := {[merge; hd; tl; hd2; tl2; mt; mlt; mgt]})
              (T1 := TBase TList).
            { eapply TT_ListCons.
              { eapply VT_FVar. basic_lookup. }
              { eapply VT_FVar. basic_lookup. } }
            { intros mtail2 Hmtail2.
              assert (Hmtail2_hd2 : mtail2 <> hd2)
                by (intro Heq; subst; apply Hmtail2; finite_set_in).
              simpl.
              eapply TT_ListCons.
              { eapply VT_FVar.
                rewrite lookup_insert_ne by exact Hmtail2_hd2.
                basic_lookup. }
              { eapply VT_FVar. basic_lookup. } } }
          { basic_type. } } } } }
Qed.

Lemma sorted_nil :
  sorted [].
Proof. cbn. exact I. Qed.

Lemma sorted_singleton n :
  sorted [n].
Proof. cbn. exact I. Qed.

Lemma mem_list_here n xs :
  mem_list n (n :: xs).
Proof. cbn. left. reflexivity. Qed.

Lemma basic_type_nil_ret Γ :
  Γ ⊢ₑ Ret nil_value ⋮ List.
Proof.
  unfold Ret, nil_value.
  constructor. constructor.
Qed.

Lemma basic_type_cons_nat_list Γ n xs :
  Γ ⊢ₑ cons_tm (vnat n) (vlist xs) ⋮ List.
Proof.
  unfold cons_tm, vnat, vlist.
  econstructor; constructor.
Qed.

Lemma merge_basic_first_call Γ (merge xs : atom) :
  Γ !! merge = Some merge_basic_ty ->
  Γ !! xs = Some (List : ty) ->
  Γ ⊢ₑ tapp merge xs ⋮ (List →ᵦ List).
Proof.
  intros Hmerge Hxs.
  econstructor.
  - constructor. exact Hmerge.
  - constructor. exact Hxs.
Qed.

End DisproveMergeExample.
