(** * ChoiceType.TypeDenotation.Formula

    Denotational semantics for the choice type system (§1.5 of the paper).

    The interpretation is given as formulas in [Choice Logic] whose atoms are
    logic qualifiers.  Core expressions are embedded through
    expression-result formulas, and type qualifiers are embedded directly as
    store/resource atoms after they have been opened to closed atom-based
    qualifiers.

    The satisfaction notation [m ⊨ φ] is the central judgment used by
    the typing rules and the fundamental theorem. *)

From Stdlib Require Import Logic.FunctionalExtensionality Logic.PropExtensionality Lia.
From LocallyNameless Require Import Tactics.
From CoreLang Require Import Instantiation InstantiationProps LocallyNamelessProps
  OperationalProps StrongNormalization Sugar.
From ChoiceType Require Export TypeDenotation.Fibers.
From ChoiceType Require Import BasicStore BasicTyping LocallyNamelessProps.

(** ** ChoiceLogic satisfaction, instantiated for qualifiers *)

(** Local abbreviation for the ChoiceType formula instantiation.  The exported
    name from [Prelude] is [FormulaQ]. *)
Local Notation FQ := FormulaQ.

Class MOpen Env A B := mopen : Env → A → B.

Notation "η ⊙ x" := (mopen η x)
  (at level 30, right associativity, format "η  ⊙  x").

Class MOpenInsertLaws A B `{Open atom A}
    `{MOpen (gmap nat atom) A B} := {
  mopen_insert_norm :
    ∀ k x η (a : A),
      mopen η ({k ~> x} a) = mopen (<[k := x]> η) a;
}.

Ltac mopen_norm :=
  rewrite ?mopen_insert_norm.

Class OpenCommute (A : Type) (openA : nat → atom → A → A)
    (R : relation A) := {
  open_commute :
    ∀ i j x y (a : A),
      i ≠ j →
      R (openA i x (openA j y a)) (openA j y (openA i x a));
}.

Class OpenProper (A : Type) (openA : nat → atom → A → A)
    (R : relation A) := {
  open_proper :
    ∀ i x, Proper (R ==> R) (openA i x);
}.

Lemma open_map_fold_insert_fresh_eq
    {A : Type} (openA : nat → atom → A → A)
    `{!OpenCommute A openA eq}
    (η : gmap nat atom) k x (a : A) :
  η !! k = None →
  map_fold openA a (<[k := x]> η) =
  openA k x (map_fold openA a η).
Proof.
  intros Hfresh.
  apply (map_fold_insert_L (M:=gmap nat) (A:=atom) (B:=A)
    openA a k x η).
  - intros i j xi xj acc Hij _ _.
    apply open_commute. exact Hij.
  - exact Hfresh.
Qed.

Lemma open_map_fold_insert_fresh_rel
    {A : Type} (R : relation A) `{!PreOrder R}
    (openA : nat → atom → A → A)
    `{HproperInst : !OpenProper A openA R}
    `{HcommuteInst : !OpenCommute A openA R}
    (η : gmap nat atom) k x (a : A) :
  η !! k = None →
  R (map_fold openA a (<[k := x]> η))
    (openA k x (map_fold openA a η)).
Proof.
  intros Hfresh.
  destruct HproperInst as [Hproper].
  destruct HcommuteInst as [Hcommute].
  eapply (map_fold_insert (M := gmap nat) (A := atom) (B := A)
    R openA a k x η).
  - intros i y.
    apply Hproper.
  - intros i j xi xj acc Hij _ _.
    apply Hcommute. exact Hij.
  - exact Hfresh.
Qed.

#[global] Instance into_lvars_atom_ty_env : IntoLVars (gmap atom ty) :=
  fun Σ => lvars_of_atoms (dom Σ).

#[global] Instance into_lvars_logic_ty_env : IntoLVars (gmap logic_var ty) :=
  fun Σ => dom Σ.

Ltac denot_lvars_norm :=
  repeat match goal with
  | |- context[into_lvars ?X] =>
      let T := type of X in
      lazymatch T with
      | lvset => change (into_lvars X) with X
      | aset => change (into_lvars X) with (lvars_of_atoms X)
      | gmap atom ty => change (into_lvars X) with (lvars_of_atoms (dom X))
      | gmap logic_var ty => change (into_lvars X) with (dom X)
      end
  | H : context[into_lvars ?X] |- _ =>
      let T := type of X in
      lazymatch T with
      | lvset => change (into_lvars X) with X in H
      | aset => change (into_lvars X) with (lvars_of_atoms X) in H
      | gmap atom ty => change (into_lvars X) with (lvars_of_atoms (dom X)) in H
      | gmap logic_var ty => change (into_lvars X) with (dom X) in H
      end
  end.

(** Satisfaction: [m ⊨ φ]  ↔  [res_models m φ] *)
Notation "m ⊨ φ" :=
  (res_models m φ)
  (at level 70, format "m  ⊨  φ").

(** Entailment shorthand: [φ ⊫ ψ]  ↔  [∀ m, m ⊨ φ → m ⊨ ψ] *)
Notation "φ ⊫ ψ" :=
  (entails φ ψ)
  (at level 85, ψ at level 84, no associativity).

(** ** Logic atoms and fresh variable helpers for denotation *)


Definition expr_result_store (ν : atom) (eρ : tm) (σw : Store) : Prop :=
  ∃ v,
    σw = {[ν := v]} ∧
    stale v = ∅ ∧
    is_lc v ∧
    eρ →* tret v.

Lemma expr_result_store_elim ν eρ σw :
  expr_result_store ν eρ σw →
  ∃ v,
    σw = {[ν := v]} ∧
    stale v = ∅ ∧
    is_lc v ∧
    eρ →* tret v.
Proof. intros H. exact H. Qed.

Lemma expr_result_store_intro ν eρ v :
  stale v = ∅ →
  is_lc v →
  eρ →* tret v →
  expr_result_store ν eρ ({[ν := v]}).
Proof. intros Hstale Hlc Hsteps. exists v. repeat split; auto. Qed.

Definition expr_result_in_world (ρ : Store) (e : tm) (ν : atom) (w : WfWorld) : Prop :=
  ∀ σν,
    (res_restrict w {[ν]} : World) σν ↔
    expr_result_store ν (subst_map ρ e) σν.

Lemma expr_result_in_world_sound ρ e ν w σw :
  expr_result_in_world ρ e ν w →
  (res_restrict w {[ν]} : World) σw →
  expr_result_store ν (subst_map ρ e) σw.
Proof. intros H Hw. exact (proj1 (H σw) Hw). Qed.

Definition open_tm_env (η : gmap nat atom) (e : tm) : tm :=
  map_fold (λ k x acc, open_tm k (vfvar x) acc) e η.

#[global] Instance mopen_tm_inst :
  MOpen (gmap nat atom) tm tm := open_tm_env.

Lemma open_tm_env_empty e :
  open_tm_env ∅ e = e.
Proof. unfold open_tm_env. rewrite map_fold_empty. reflexivity. Qed.

Definition formula_open_env (η : gmap nat atom) (φ : FQ) : FQ :=
  map_fold (λ k x acc, formula_open k x acc) φ η.

#[global] Instance open_formula_atom_inst : Open atom FQ := formula_open.

#[global] Instance mopen_formula_inst :
  MOpen (gmap nat atom) FQ FQ := formula_open_env.

Definition lvars_open_env (η : gmap nat atom) (D : lvset) : lvset :=
  map_fold (λ k x acc, lvars_open k x acc) D η.

Definition logic_var_open_env
    (η : gmap nat atom) (v : logic_var) : logic_var :=
  match v with
  | LVFree x => LVFree x
  | LVBound k =>
      match η !! k with
      | Some x => LVFree x
      | None => LVBound k
      end
  end.

Definition lvars_open_env_simul
    (η : gmap nat atom) (D : lvset) : lvset :=
  set_map (logic_var_open_env η) D.

(* The formula interpretation opens bound logic variables by threading a finite
   environment [η].  In denotation proofs [η] is built from formula binders, so
   every atom in its codomain is fresh for the variables produced by the other
   opens.  This is the invariant that makes finite-map folds commute for type
   environments without pretending that arbitrary colliding open environments
   are order-independent. *)
Definition open_env_fresh_for_lvars (η : gmap nat atom) (D : lvset) : Prop :=
  ∀ k x,
    η !! k = Some x →
    x ∉ lvars_fv (lvars_open_env (delete k η) D).

Definition open_env_precompose
    (η ξ : gmap nat atom) : gmap nat atom :=
  η ∪ ξ.

Definition open_env_avoids_atom (x : atom) (η : gmap nat atom) : Prop :=
  ∀ k, η !! k ≠ Some x.

Lemma open_env_avoids_atom_empty x :
  open_env_avoids_atom x ∅.
Proof. intros k. rewrite lookup_empty. discriminate. Qed.

Lemma open_env_avoids_atom_singleton k x y :
  y ≠ x →
  open_env_avoids_atom x (<[k := y]> ∅).
Proof.
  intros Hyx i Hi.
  destruct (decide (i = k)) as [->|Hik].
  - rewrite lookup_insert in Hi.
    destruct (decide (k = k)) as [_|Hbad]; [| congruence].
    inversion Hi. subst. congruence.
  - rewrite lookup_insert_ne in Hi by congruence.
      rewrite lookup_empty in Hi. discriminate.
Qed.

Lemma open_env_avoids_atom_insert k x y η :
  y ≠ x →
  open_env_avoids_atom x η →
  open_env_avoids_atom x (<[k := y]> η).
Proof.
  intros Hyx Havoid i Hi.
  destruct (decide (i = k)) as [->|Hik].
  - rewrite lookup_insert in Hi.
    destruct (decide (k = k)) as [_|Hbad]; [| congruence].
    inversion Hi. subst. congruence.
  - rewrite lookup_insert_ne in Hi by congruence.
    eapply Havoid. exact Hi.
Qed.

#[local] Instance inj_S_nat : Inj (=) (=) S :=
  λ i j H, Nat.succ_inj _ _ H.

Definition open_env_lift (η : gmap nat atom) : gmap nat atom :=
  kmap S η.

Lemma open_env_lift_empty :
  open_env_lift ∅ = ∅.
Proof. unfold open_env_lift. apply kmap_empty. Qed.

Lemma open_env_lift_insert k x η :
  open_env_lift (<[k := x]> η) = <[S k := x]> (open_env_lift η).
Proof.
  unfold open_env_lift.
  rewrite (kmap_insert (M1:=gmap nat) (M2:=gmap nat)
    S (Inj0:=ltac:(intros ? ? ?; lia)) (A:=atom) η k x).
  reflexivity.
Qed.

Lemma formula_open_env_empty φ :
  formula_open_env ∅ φ = φ.
Proof. unfold formula_open_env. rewrite map_fold_empty. reflexivity. Qed.

Lemma formula_open_env_true η :
  formula_open_env η FTrue = FTrue.
Proof.
  unfold formula_open_env.
  refine (fin_maps.map_fold_ind
    (fun η => map_fold (λ k x acc, formula_open k x acc) FTrue η = FTrue)
    _ _ η).
  - rewrite map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH. rewrite Hfold, IH. reflexivity.
Qed.

Lemma formula_open_env_singleton k x φ :
  formula_open_env (<[k := x]> ∅) φ = formula_open k x φ.
Proof.
  unfold formula_open_env.
  change (<[k := x]> ∅ : gmap nat atom) with ({[k := x]} : gmap nat atom).
  rewrite map_fold_singleton. reflexivity.
Qed.

Lemma open_env_precompose_empty ξ :
  open_env_precompose ∅ ξ = ξ.
Proof.
  unfold open_env_precompose.
  apply map_eq. intros i.
  rewrite lookup_union_r; [reflexivity | apply lookup_empty].
Qed.

Lemma open_env_precompose_empty_r η :
  open_env_precompose η ∅ = η.
Proof.
  unfold open_env_precompose.
  apply map_eq. intros i.
  destruct (η !! i) as [x|] eqn:Hηi.
  - rewrite lookup_union_l' by eauto. exact Hηi.
  - rewrite lookup_union_r by exact Hηi.
    rewrite lookup_empty. reflexivity.
Qed.

Lemma open_env_precompose_insert_fresh η k x ξ :
  η !! k = None →
  open_env_precompose (<[k := x]> η) ξ =
  open_env_precompose η (<[k := x]> ξ).
Proof.
  intros Hfresh.
  unfold open_env_precompose.
  apply map_eq. intros i.
  destruct (decide (i = k)) as [->|Hik].
  - rewrite lookup_union_l'.
    2:{ rewrite lookup_insert_eq. eauto. }
    rewrite lookup_union_r by exact Hfresh.
    rewrite !lookup_insert_eq. reflexivity.
  - destruct (η !! i) as [z|] eqn:Hηi.
    + assert (Hη'i : (<[k := x]> η : gmap nat atom) !! i = Some z).
      { rewrite lookup_insert_ne by congruence. exact Hηi. }
      rewrite lookup_union_l' by (exists z; exact Hη'i).
      rewrite lookup_union_l' by (exists z; exact Hηi).
      rewrite Hη'i, Hηi.
      reflexivity.
    + assert (Hη'i : (<[k := x]> η : gmap nat atom) !! i = None).
      { rewrite lookup_insert_ne by congruence. exact Hηi. }
      rewrite lookup_union_r by exact Hη'i.
      rewrite lookup_union_r by exact Hηi.
      rewrite lookup_insert_ne by congruence.
      reflexivity.
Qed.

Lemma formula_open_env_and η φ ψ :
  formula_open_env η (FAnd φ ψ) =
  FAnd (formula_open_env η φ) (formula_open_env η ψ).
Proof.
  unfold formula_open_env.
  refine (fin_maps.map_fold_ind
    (fun η => map_fold (λ k x acc, formula_open k x acc) (FAnd φ ψ) η =
      FAnd
        (map_fold (λ k x acc, formula_open k x acc) φ η)
        (map_fold (λ k x acc, formula_open k x acc) ψ η)) _ _ η).
  - rewrite !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite !Hfold. cbn [formula_open]. rewrite IH. reflexivity.
Qed.

Lemma formula_open_env_or η φ ψ :
  formula_open_env η (FOr φ ψ) =
  FOr (formula_open_env η φ) (formula_open_env η ψ).
Proof.
  unfold formula_open_env.
  refine (fin_maps.map_fold_ind
    (fun η => map_fold (λ k x acc, formula_open k x acc) (FOr φ ψ) η =
      FOr
        (map_fold (λ k x acc, formula_open k x acc) φ η)
        (map_fold (λ k x acc, formula_open k x acc) ψ η)) _ _ η).
  - rewrite !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite !Hfold. cbn [formula_open]. rewrite IH. reflexivity.
Qed.

Lemma formula_open_env_impl η φ ψ :
  formula_open_env η (FImpl φ ψ) =
  FImpl (formula_open_env η φ) (formula_open_env η ψ).
Proof.
  unfold formula_open_env.
  refine (fin_maps.map_fold_ind
    (fun η => map_fold (λ k x acc, formula_open k x acc) (FImpl φ ψ) η =
      FImpl
        (map_fold (λ k x acc, formula_open k x acc) φ η)
        (map_fold (λ k x acc, formula_open k x acc) ψ η)) _ _ η).
  - rewrite !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite !Hfold. cbn [formula_open]. rewrite IH. reflexivity.
Qed.

Lemma formula_open_env_wand η φ ψ :
  formula_open_env η (FWand φ ψ) =
  FWand (formula_open_env η φ) (formula_open_env η ψ).
Proof.
  unfold formula_open_env.
  refine (fin_maps.map_fold_ind
    (fun η => map_fold (λ k x acc, formula_open k x acc) (FWand φ ψ) η =
      FWand
        (map_fold (λ k x acc, formula_open k x acc) φ η)
        (map_fold (λ k x acc, formula_open k x acc) ψ η)) _ _ η).
  - rewrite !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite !Hfold. cbn [formula_open]. rewrite IH. reflexivity.
Qed.

Lemma formula_open_env_plus η φ ψ :
  formula_open_env η (FPlus φ ψ) =
  FPlus (formula_open_env η φ) (formula_open_env η ψ).
Proof.
  unfold formula_open_env.
  refine (fin_maps.map_fold_ind
    (fun η => map_fold (λ k x acc, formula_open k x acc) (FPlus φ ψ) η =
      FPlus
        (map_fold (λ k x acc, formula_open k x acc) φ η)
        (map_fold (λ k x acc, formula_open k x acc) ψ η)) _ _ η).
  - rewrite !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite !Hfold. cbn [formula_open]. rewrite IH. reflexivity.
Qed.

Lemma formula_open_env_over η φ :
  formula_open_env η (FOver φ) =
  FOver (formula_open_env η φ).
Proof.
  unfold formula_open_env.
  refine (fin_maps.map_fold_ind
    (fun η => map_fold (λ k x acc, formula_open k x acc) (FOver φ) η =
      FOver
        (map_fold (λ k x acc, formula_open k x acc) φ η)) _ _ η).
  - rewrite !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite !Hfold. cbn [formula_open]. rewrite IH. reflexivity.
Qed.

Lemma formula_open_env_under η φ :
  formula_open_env η (FUnder φ) =
  FUnder (formula_open_env η φ).
Proof.
  unfold formula_open_env.
  refine (fin_maps.map_fold_ind
    (fun η => map_fold (λ k x acc, formula_open k x acc) (FUnder φ) η =
      FUnder
        (map_fold (λ k x acc, formula_open k x acc) φ η)) _ _ η).
  - rewrite !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite !Hfold. cbn [formula_open]. rewrite IH. reflexivity.
Qed.

Lemma formula_open_env_fibvars η D φ :
  formula_open_env η (FFibVars D φ) =
  FFibVars (lvars_open_env η D) (formula_open_env η φ).
Proof.
  unfold formula_open_env, lvars_open_env.
  refine (fin_maps.map_fold_ind
    (fun η =>
      map_fold (λ k x acc, formula_open k x acc) (FFibVars D φ) η =
      FFibVars
        (map_fold (λ k x acc, lvars_open k x acc) D η)
        (map_fold (λ k x acc, formula_open k x acc) φ η)) _ _ η).
  - rewrite !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite !Hfold. cbn [formula_open]. rewrite IH. reflexivity.
Qed.

Lemma logic_var_open_commute_fvar i j x y v :
  i ≠ j →
  logic_var_open i x (logic_var_open j y v) =
  logic_var_open j y (logic_var_open i x v).
Proof.
  intros Hij.
  destruct v as [n|z]; cbn [logic_var_open].
  - repeat (destruct (decide _) as [?|?]; subst; cbn [logic_var_open] in *);
      try congruence; try lia; reflexivity.
  - reflexivity.
Qed.

#[global] Instance open_commute_logic_var :
  OpenCommute logic_var logic_var_open eq.
Proof.
  constructor. intros i j x y v Hij.
  apply logic_var_open_commute_fvar. exact Hij.
Qed.

Lemma lvars_open_commute_fvar i j x y D :
  i ≠ j →
  lvars_open i x (lvars_open j y D) =
  lvars_open j y (lvars_open i x D).
Proof.
  intros Hij.
  apply set_eq. intros v.
  unfold lvars_open.
  rewrite !elem_of_map.
  split; intros [u [-> Hu]]; rewrite elem_of_map in Hu;
    destruct Hu as [u' [-> Hu']].
  - exists (logic_var_open i x u'). split.
    + symmetry. apply logic_var_open_commute_fvar. congruence.
    + rewrite elem_of_map. eauto.
  - exists (logic_var_open j y u'). split.
    + symmetry. apply logic_var_open_commute_fvar. exact Hij.
    + rewrite elem_of_map. eauto.
Qed.

#[global] Instance open_commute_lvars :
  OpenCommute lvset lvars_open eq.
Proof.
  constructor. intros i j x y D Hij.
  apply lvars_open_commute_fvar. exact Hij.
Qed.

Lemma lvars_open_same_index_absorb_formula k x y D :
  lvars_open k y (lvars_open k x D) = lvars_open k x D.
Proof.
  apply lvars_open_no_bv.
  rewrite lvars_bv_open. set_solver.
Qed.

Lemma lqual_open_same_index_absorb k x y q :
  lqual_open (V := value) k y (lqual_open (V := value) k x q) =
  lqual_open k x q.
Proof.
  destruct q as [D p].
  cbn [lqual_open].
  rewrite lvars_open_same_index_absorb_formula.
  f_equal.
  apply functional_extensionality; intro η.
  apply functional_extensionality; intro σ.
  apply functional_extensionality; intro w.
  assert (Hη :
    ((<[k := x]> (<[k := y]> η)) : gmap nat atom) =
    ((<[k := x]> η) : gmap nat atom)).
  {
    apply map_eq. intro n.
    destruct (decide (n = k)) as [->|Hnk].
    - rewrite !lookup_insert_eq. reflexivity.
    - rewrite !lookup_insert_ne by congruence. reflexivity.
  }
  rewrite Hη. reflexivity.
Qed.

Lemma lqual_open_commute_fvar i j x y q :
  i ≠ j →
  lqual_open (V := value) i x (lqual_open (V := value) j y q) =
  lqual_open (V := value) j y (lqual_open (V := value) i x q).
Proof.
  intros Hij.
  destruct q as [D p].
  cbn [lqual_open].
  rewrite lvars_open_commute_fvar by exact Hij.
  f_equal.
  apply functional_extensionality; intro η.
  apply functional_extensionality; intro σ.
  apply functional_extensionality; intro w.
  replace (<[j:=y]> (<[i:=x]> η)) with (<[i:=x]> (<[j:=y]> η));
    [reflexivity |].
  apply map_eq. intro n.
  destruct (decide (n = i)) as [->|Hni].
  - rewrite (lookup_insert_ne (<[i:=x]> η) j i y) by congruence.
    rewrite !lookup_insert_eq. reflexivity.
  - destruct (decide (n = j)) as [->|Hnj].
    + rewrite (lookup_insert_ne (<[j:=y]> η) i j x) by congruence.
      rewrite !lookup_insert_eq. reflexivity.
    + rewrite (lookup_insert_ne (<[i:=x]> η) j n y) by congruence.
      rewrite (lookup_insert_ne η i n x) by congruence.
      rewrite (lookup_insert_ne (<[j:=y]> η) i n x) by congruence.
      rewrite (lookup_insert_ne η j n y) by congruence.
      reflexivity.
Qed.

#[global] Instance open_commute_lqual :
  OpenCommute logic_qualifier (lqual_open (V := value)) eq.
Proof.
  constructor. intros i j x y q Hij.
  apply lqual_open_commute_fvar. exact Hij.
Qed.

Lemma formula_open_commute_fvar i j x y φ :
  i ≠ j →
  formula_open (V := value) i x (formula_open (V := value) j y φ) =
  formula_open (V := value) j y (formula_open (V := value) i x φ).
Proof.
  induction φ in i, j |- *; intros Hij; cbn [formula_open];
    try rewrite IHφ1 by exact Hij;
    try rewrite IHφ2 by exact Hij;
    try reflexivity.
  - rewrite lqual_open_commute_fvar by exact Hij. reflexivity.
  - rewrite IHφ by lia. reflexivity.
  - rewrite IHφ by lia. reflexivity.
  - rewrite IHφ by exact Hij. reflexivity.
  - rewrite IHφ by exact Hij. reflexivity.
  - rewrite lvars_open_commute_fvar by exact Hij.
    rewrite IHφ by exact Hij. reflexivity.
Qed.

Lemma formula_open_same_index_absorb k x y φ :
  formula_open (V := value) k y (formula_open (V := value) k x φ) =
  formula_open k x φ.
Proof.
  induction φ in k |- *; cbn [formula_open]; try reflexivity.
  - rewrite lqual_open_same_index_absorb. reflexivity.
  - rewrite IHφ1, IHφ2. reflexivity.
  - rewrite IHφ1, IHφ2. reflexivity.
  - rewrite IHφ1, IHφ2. reflexivity.
  - rewrite IHφ1, IHφ2. reflexivity.
  - rewrite IHφ1, IHφ2. reflexivity.
  - rewrite IHφ1, IHφ2. reflexivity.
  - rewrite (IHφ (S k)). reflexivity.
  - rewrite (IHφ (S k)). reflexivity.
  - rewrite IHφ. reflexivity.
  - rewrite IHφ. reflexivity.
  - rewrite lvars_open_same_index_absorb_formula.
    rewrite IHφ. reflexivity.
Qed.

#[global] Instance open_commute_formula_eq :
  OpenCommute FQ (formula_open (V := value)) eq.
Proof.
  constructor. intros i j x y φ Hij.
  apply formula_open_commute_fvar. exact Hij.
Qed.

Lemma formula_open_env_insert_fresh η k x φ :
  η !! k = None →
  formula_open_env (<[k := x]> η) φ =
  formula_open k x (formula_open_env η φ).
Proof.
  intros Hfresh.
  unfold formula_open_env.
  exact (open_map_fold_insert_fresh_eq
    (formula_open (V := value)) η k x φ Hfresh).
Qed.

Lemma formula_open_env_open_fresh η k x φ :
  η !! k = None →
  formula_open_env η (formula_open k x φ) =
  formula_open k x (formula_open_env η φ).
Proof.
  intros Hη.
  unfold formula_open_env.
  revert Hη.
  refine (fin_maps.map_fold_ind
    (fun η =>
      η !! k = None →
      map_fold (fun j y acc => formula_open j y acc)
        (formula_open k x φ) η =
      formula_open k x
        (map_fold (fun j y acc => formula_open j y acc) φ η)) _ _ η).
  - intros _. rewrite !map_fold_empty. reflexivity.
  - intros j y η' Hfresh Hfold IH Hη.
    rewrite !Hfold.
    assert (Hjk : j ≠ k).
    {
      intros ->.
      rewrite lookup_insert in Hη.
      destruct (decide (k = k)); congruence.
    }
    assert (Hη' : η' !! k = None).
    {
      rewrite lookup_insert_ne in Hη by congruence.
      exact Hη.
    }
    rewrite IH by exact Hη'.
    apply formula_open_commute_fvar. congruence.
Qed.

Lemma formula_open_env_open_one η k x φ :
  formula_open_env η (formula_open k x φ) =
  formula_open_env (<[k := x]> η) φ.
Proof.
  destruct (η !! k) as [y|] eqn:Hηk.
  - rewrite <-(insert_delete_id η k y Hηk) at 1.
    rewrite formula_open_env_insert_fresh by apply lookup_delete_eq.
    rewrite formula_open_env_open_fresh by apply lookup_delete_eq.
    rewrite formula_open_same_index_absorb.
    replace (<[k:=x]> η) with (<[k:=x]> (delete k η)).
    2:{
      apply map_eq. intro j.
      destruct (decide (j = k)) as [->|Hjk].
      - rewrite !lookup_insert. destruct (decide (k = k)); congruence.
      - rewrite !lookup_insert_ne by congruence.
        rewrite lookup_delete_ne by congruence. reflexivity.
    }
    rewrite formula_open_env_insert_fresh.
    + reflexivity.
    + apply lookup_delete_eq.
  - rewrite formula_open_env_open_fresh by exact Hηk.
    symmetry. apply formula_open_env_insert_fresh. exact Hηk.
Qed.

#[global] Instance mopen_insert_formula_inst : MOpenInsertLaws FQ FQ := {
  mopen_insert_norm := fun k x η φ => formula_open_env_open_one η k x φ
}.

Lemma lvars_open_env_insert_fresh η k x D :
  η !! k = None →
  lvars_open_env (<[k := x]> η) D =
  lvars_open k x (lvars_open_env η D).
Proof.
  intros Hfresh.
  unfold lvars_open_env.
  exact (open_map_fold_insert_fresh_eq lvars_open η k x D Hfresh).
Qed.

Lemma lvars_open_env_union η D1 D2 :
  lvars_open_env η (D1 ∪ D2) =
  lvars_open_env η D1 ∪ lvars_open_env η D2.
Proof.
  unfold lvars_open_env.
  refine (fin_maps.map_fold_ind
    (fun η =>
      map_fold (fun k x acc => lvars_open k x acc) (D1 ∪ D2) η =
      map_fold (fun k x acc => lvars_open k x acc) D1 η ∪
      map_fold (fun k x acc => lvars_open k x acc) D2 η) _ _ η).
  - rewrite !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite !Hfold.
    rewrite IH.
    unfold lvars_open. rewrite set_map_union_L. reflexivity.
Qed.

Lemma formula_open_env_FStoreResourceAtom_lvars
    η (D : lvset) P :
  formula_open_env η (FStoreResourceAtom D P) =
  FStoreResourceAtom (lvars_open_env η D)
    (fun ξ σ m => P (open_env_precompose η ξ) σ m).
Proof.
  unfold formula_open_env, lvars_open_env.
  refine (fin_maps.map_fold_ind
    (fun η =>
      map_fold (λ k x acc, formula_open k x acc)
        (FStoreResourceAtom D P) η =
      FStoreResourceAtom
        (map_fold (λ k x acc, lvars_open k x acc) D η)
        (fun ξ σ m => P (open_env_precompose η ξ) σ m)) _ _ η).
  - rewrite !map_fold_empty.
    apply FStoreResourceAtom_ext.
    { reflexivity. }
    intros ξ σ m.
    rewrite open_env_precompose_empty.
    reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite Hfold.
    rewrite IH.
    rewrite formula_open_FStoreResourceAtom_lvars.
    apply FStoreResourceAtom_ext.
    { symmetry. exact (open_map_fold_insert_fresh_eq lvars_open η' k x D Hfresh). }
    intros ξ σ m.
    rewrite open_env_precompose_insert_fresh by exact Hfresh.
    reflexivity.
Qed.

Lemma open_env_lift_lookup_none η k :
  η !! k = None →
  open_env_lift η !! S k = None.
Proof.
  intros Hnone.
  unfold open_env_lift.
  rewrite lookup_kmap_None.
  intros j Hj.
  apply Nat.succ_inj in Hj. subst j. exact Hnone.
  Unshelve. intros ? ? ?; lia.
Qed.

Lemma open_env_lift_lookup_zero_none η :
  open_env_lift η !! 0 = None.
Proof.
  unfold open_env_lift.
  rewrite lookup_kmap_None.
  intros j Hj. lia.
  Unshelve. intros ? ? ?; lia.
Qed.

Lemma open_env_avoids_atom_lift x η :
  open_env_avoids_atom x η →
  open_env_avoids_atom x (open_env_lift η).
Proof.
  intros Havoid k Hk.
  unfold open_env_lift in Hk.
  rewrite lookup_kmap_Some in Hk.
  destruct Hk as [j [Hj Hηj]].
  eapply Havoid. exact Hηj.
  Unshelve. intros ? ? ?; lia.
Qed.

Lemma formula_open_env_forall η φ :
  formula_open_env η (FForall φ) =
  FForall (formula_open_env (open_env_lift η) φ).
Proof.
  unfold formula_open_env.
  refine (fin_maps.map_fold_ind
    (fun η => map_fold (λ k x acc, formula_open k x acc) (FForall φ) η =
      FForall
        (map_fold (λ k x acc, formula_open k x acc) φ
          (open_env_lift η))) _ _ η).
  - rewrite map_fold_empty, open_env_lift_empty, map_fold_empty.
    reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite Hfold.
    cbn [formula_open].
    rewrite IH.
    rewrite open_env_lift_insert.
    replace (map_fold (λ k0 x0 acc, formula_open k0 x0 acc) φ
      (<[S k:=x]> (open_env_lift η'))) with
      (formula_open (S k) x
        (map_fold (λ k0 x0 acc, formula_open k0 x0 acc) φ
          (open_env_lift η'))).
    { reflexivity. }
    change (map_fold (λ k0 x0 acc, formula_open k0 x0 acc) φ
      (<[S k:=x]> (open_env_lift η'))) with
      (formula_open_env (<[S k:=x]> (open_env_lift η')) φ).
    change (map_fold (λ k0 x0 acc, formula_open k0 x0 acc) φ
      (open_env_lift η')) with
      (formula_open_env (open_env_lift η') φ).
    symmetry. apply formula_open_env_insert_fresh.
    apply open_env_lift_lookup_none. exact Hfresh.
Qed.

Lemma open_tm_env_singleton k x e :
  open_tm_env (<[k := x]> ∅) e = open_tm k (vfvar x) e.
Proof.
  unfold open_tm_env.
  change (<[k := x]> ∅ : gmap nat atom) with ({[k := x]} : gmap nat atom).
  rewrite map_fold_singleton. reflexivity.
Qed.

Lemma open_tm_env_singleton_lc k x e :
  lc_tm e →
  open_tm_env (<[k := x]> ∅) e = e.
Proof.
  intros Hlc.
  rewrite open_tm_env_singleton.
  apply open_rec_lc_tm. exact Hlc.
Qed.

Lemma open_tm_env_lc η e :
  lc_tm e →
  open_tm_env η e = e.
Proof.
  intros Hlc.
  unfold open_tm_env.
  refine (fin_maps.map_fold_ind
    (fun η => map_fold
      (λ k x acc, open_tm k (vfvar x) acc) e η = e) _ _ η).
  - rewrite map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite Hfold, IH.
    apply open_rec_lc_tm. exact Hlc.
Qed.

Lemma open_same_index_fvar_mutual x y :
  (∀ v k,
    open_value k (vfvar y) (open_value k (vfvar x) v) =
    open_value k (vfvar x) v) *
  (∀ e k,
    open_tm k (vfvar y) (open_tm k (vfvar x) e) =
    open_tm k (vfvar x) e).
Proof.
  apply value_tm_mutind; simpl; intros; try reflexivity; try (f_equal; eauto).
  - destruct (decide (k = n)) as [->|Hkn]; simpl.
    + destruct (decide (n = n)) as [_|Hbad]; [reflexivity | congruence].
    + destruct (decide (k = n)) as [Hbad|_]; [congruence | reflexivity].
Qed.

Lemma open_value_same_index_fvar x y k v :
  open_value k (vfvar y) (open_value k (vfvar x) v) =
  open_value k (vfvar x) v.
Proof. exact (fst (open_same_index_fvar_mutual x y) v k). Qed.

Lemma open_tm_same_index_fvar x y k e :
  open_tm k (vfvar y) (open_tm k (vfvar x) e) =
  open_tm k (vfvar x) e.
Proof. exact (snd (open_same_index_fvar_mutual x y) e k). Qed.

Lemma open_commute_fvar_mutual x y :
  (∀ v i j,
    i ≠ j →
    open_value i (vfvar y) (open_value j (vfvar x) v) =
    open_value j (vfvar x) (open_value i (vfvar y) v)) *
  (∀ e i j,
    i ≠ j →
    open_tm i (vfvar y) (open_tm j (vfvar x) e) =
    open_tm j (vfvar x) (open_tm i (vfvar y) e)).
Proof.
  apply value_tm_mutind; simpl; intros.
  - reflexivity.
  - reflexivity.
  - destruct (decide (j = n)) as [Hjn|Hjn];
      destruct (decide (i = n)) as [Hin|Hin]; subst; simpl.
    + contradiction.
    + destruct (decide (n = n)) as [_|Hbad]; [reflexivity | congruence].
    + destruct (decide (n = n)) as [_|Hbad]; [reflexivity | congruence].
    + destruct (decide (i = n)) as [Hbad|_]; [congruence |].
      destruct (decide (j = n)) as [Hbad|_]; [congruence | reflexivity].
  - f_equal. eauto with lia.
  - f_equal. eauto with lia.
  - f_equal. eauto.
  - f_equal; eauto with lia.
  - f_equal. eauto.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma open_value_commute_fvar x y i j v :
  i ≠ j →
  open_value i (vfvar y) (open_value j (vfvar x) v) =
  open_value j (vfvar x) (open_value i (vfvar y) v).
Proof. exact (fst (open_commute_fvar_mutual x y) v i j). Qed.

Lemma open_tm_commute_fvar x y i j e :
  i ≠ j →
  open_tm i (vfvar y) (open_tm j (vfvar x) e) =
  open_tm j (vfvar x) (open_tm i (vfvar y) e).
Proof. exact (snd (open_commute_fvar_mutual x y) e i j). Qed.

Lemma open_shift_open_fvar_mutual x :
  (∀ v k cutoff,
    cutoff <= k →
    open_value (S k) (vfvar x) (value_shift cutoff v) =
    value_shift cutoff (open_value k (vfvar x) v)) *
  (∀ e k cutoff,
    cutoff <= k →
    open_tm (S k) (vfvar x) (tm_shift cutoff e) =
    tm_shift cutoff (open_tm k (vfvar x) e)).
Proof.
  apply value_tm_mutind; simpl; intros; try reflexivity; try (f_equal; eauto with lia).
  - destruct (decide (cutoff <= n)) as [Hcn|Hcn];
      destruct (decide (k = n)) as [->|Hkn]; simpl.
    + destruct (decide (S n = S n)) as [_|Hneq]; [|lia].
      cbn [value_shift]. reflexivity.
    + destruct (decide (S k = S n)) as [Heq|_]; [lia |].
      destruct (decide (k = n)) as [Heq|_]; [lia |].
      destruct (decide (cutoff <= n)) as [_|Hbad]; [reflexivity | lia].
    + lia.
    + destruct (decide (S k = n)) as [Heq|_]; [lia |].
      destruct (decide (k = n)) as [Heq|_]; [lia |].
      destruct (decide (cutoff <= n)) as [Hbad|_]; [lia | reflexivity].
Qed.

Lemma open_tm_shift_open_fvar k cutoff x e :
  cutoff <= k →
  open_tm (S k) (vfvar x) (tm_shift cutoff e) =
  tm_shift cutoff (open_tm k (vfvar x) e).
Proof. exact (snd (open_shift_open_fvar_mutual x) e k cutoff). Qed.

Lemma tm_shift_open_tm_fvar0 k x e :
  tm_shift 0 (open_tm k (vfvar x) e) =
  open_tm (S k) (vfvar x) (tm_shift 0 e).
Proof. symmetry. apply open_tm_shift_open_fvar. lia. Qed.

Lemma open_tm_env_insert_fresh η k x e :
  η !! k = None →
  open_tm_env (<[k := x]> η) e =
  open_tm k (vfvar x) (open_tm_env η e).
Proof.
  intros Hfresh.
  unfold open_tm_env.
  rewrite (map_fold_insert_L
    (fun k0 x0 acc => open_tm k0 (vfvar x0) acc) e k x η).
  - reflexivity.
  - intros i j xi xj acc Hij _ _.
    apply open_tm_commute_fvar. exact Hij.
  - exact Hfresh.
Qed.

Lemma open_tm_env_open_fresh η k x e :
  η !! k = None →
  open_tm_env η (open_tm k (vfvar x) e) =
  open_tm k (vfvar x) (open_tm_env η e).
Proof.
  unfold open_tm_env.
  refine (fin_maps.map_fold_ind
    (fun η => η !! k = None →
      map_fold (fun k0 x0 acc => open_tm k0 (vfvar x0) acc)
        (open_tm k (vfvar x) e) η =
      open_tm k (vfvar x)
        (map_fold (fun k0 x0 acc => open_tm k0 (vfvar x0) acc) e η))
    _ _ η).
  - intros _. rewrite !map_fold_empty. reflexivity.
  - intros i y η0 Hfresh Hfold IH Hnone.
    rewrite (Hfold tm (fun k0 x0 acc => open_tm k0 (vfvar x0) acc)
      (open_tm k (vfvar x) e) y).
    rewrite (Hfold tm (fun k0 x0 acc => open_tm k0 (vfvar x0) acc) e y).
    assert (Hik : i ≠ k).
    {
      intros ->.
      rewrite lookup_insert in Hnone.
      destruct (decide (k = k)) as [_|Hbad]; congruence.
    }
    assert (Hnone0 : η0 !! k = None).
    {
      rewrite lookup_insert_ne in Hnone by congruence.
      exact Hnone.
    }
    rewrite IH by exact Hnone0.
    apply open_tm_commute_fvar. congruence.
Qed.

Lemma open_tm_env_open_tm k x η e :
  open_tm_env η (open_tm k (vfvar x) e) =
  open_tm_env (<[k := x]> η) e.
Proof.
  destruct (η !! k) as [y|] eqn:Hηk.
  - rewrite <-(insert_delete_id η k y Hηk) at 1.
    rewrite open_tm_env_insert_fresh by apply lookup_delete_eq.
    rewrite open_tm_env_open_fresh by apply lookup_delete_eq.
    rewrite open_tm_same_index_fvar.
    replace (<[k := x]> η) with (<[k := x]> (delete k η)).
    2:{
      apply map_eq. intro z.
      destruct (decide (z = k)) as [->|Hzk].
      - rewrite !lookup_insert.
        destruct (decide (k = k)) as [_|Hbad]; [reflexivity | congruence].
      - rewrite !lookup_insert_ne by congruence.
        rewrite lookup_delete_ne by congruence.
        reflexivity.
    }
    rewrite open_tm_env_insert_fresh by apply lookup_delete_eq.
    reflexivity.
  - rewrite open_tm_env_open_fresh by exact Hηk.
    symmetry. apply open_tm_env_insert_fresh. exact Hηk.
Qed.

#[global] Instance mopen_insert_tm_inst : MOpenInsertLaws tm tm := {
  mopen_insert_norm := open_tm_env_open_tm
}.

Lemma open_tm_env_shift_open_one η k x e :
  open_tm_env η (tm_shift 0 (open_tm k (vfvar x) e)) =
  open_tm_env (<[S k := x]> η) (tm_shift 0 e).
Proof.
  rewrite tm_shift_open_tm_fvar0.
  apply open_tm_env_open_tm.
Qed.

Lemma open_tm_env_lift_shift0 η e :
  open_tm_env (open_env_lift η) (tm_shift 0 e) =
  tm_shift 0 (open_tm_env η e).
Proof.
  revert e.
  refine (fin_maps.map_fold_ind
    (fun η => ∀ e,
      open_tm_env (open_env_lift η) (tm_shift 0 e) =
      tm_shift 0 (open_tm_env η e)) _ _ η).
  - intros e. rewrite open_env_lift_empty.
    unfold open_tm_env. rewrite !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH e.
    rewrite open_env_lift_insert.
    rewrite open_tm_env_insert_fresh.
    2:{ apply open_env_lift_lookup_none. exact Hfresh. }
    rewrite IH.
    rewrite open_tm_env_insert_fresh by exact Hfresh.
    symmetry. apply tm_shift_open_tm_fvar0.
Qed.

Lemma lvars_fv_elem D x :
  x ∈ lvars_fv D ↔ LVFree x ∈ D.
Proof.
  unfold lvars_fv.
  refine (set_fold_ind_L
    (fun acc D => ∀ x, x ∈ acc ↔ LVFree x ∈ D)
    (λ v acc, logic_var_fv v ∪ acc) ∅ _ _ D x).
  - intros y. set_solver.
  - intros v D' acc Hfresh IH z.
    destruct v as [k|a]; cbn [logic_var_fv].
    + pose proof (IH z). set_solver.
    + pose proof (IH z). set_solver.
Qed.

Lemma lvars_fv_subset_open k x D :
  lvars_fv D ⊆ lvars_fv (lvars_open k x D).
Proof.
  intros y Hy.
  apply lvars_fv_elem.
  apply lvars_fv_elem in Hy.
  unfold lvars_open.
  apply elem_of_map.
  exists (LVFree y). split; [reflexivity | exact Hy].
Qed.

Lemma open_env_fresh_for_lvars_empty D :
  open_env_fresh_for_lvars ∅ D.
Proof.
  intros k x Hlookup.
  rewrite lookup_empty in Hlookup. discriminate.
Qed.

Lemma open_env_fresh_for_lvars_insert_head η k x D :
  η !! k = None →
  open_env_fresh_for_lvars (<[k := x]> η) D →
  x ∉ lvars_fv (lvars_open_env η D).
Proof.
  intros Hfresh Hη.
  specialize (Hη k x).
  rewrite lookup_insert_eq in Hη.
  specialize (Hη eq_refl).
  replace (delete k (<[k := x]> η)) with η in Hη.
  2:{
    apply map_eq. intro i.
    destruct (decide (i = k)) as [->|Hik].
    - rewrite lookup_delete.
      destruct (decide (k = k)) as [_|Hbad]; [exact Hfresh | congruence].
    - rewrite lookup_delete_ne by congruence.
      rewrite lookup_insert_ne by congruence. reflexivity.
  }
  exact Hη.
Qed.

Lemma open_env_fresh_for_lvars_insert_tail η k x D :
  η !! k = None →
  open_env_fresh_for_lvars (<[k := x]> η) D →
  open_env_fresh_for_lvars η D.
Proof.
  intros Hfresh Hη j y Hlookup.
  destruct (decide (j = k)) as [->|Hjk].
  - rewrite Hfresh in Hlookup. discriminate.
  - specialize (Hη j y).
    rewrite lookup_insert_ne in Hη by congruence.
    specialize (Hη Hlookup).
    assert (Hdel :
      delete j (<[k := x]> η) = <[k := x]> (delete j η)).
    {
      apply map_eq. intro i.
      destruct (decide (i = j)) as [->|Hij].
      - change ((delete j (<[k := x]> η)) !! j =
          (<[k := x]> (delete j η)) !! j).
        rewrite lookup_delete.
        rewrite (lookup_insert_ne (delete j η) k j x) by congruence.
        rewrite lookup_delete.
        destruct (decide (j = j)) as [_|Hbad]; [reflexivity | congruence].
      - rewrite !lookup_delete_ne by congruence.
        destruct (decide (i = k)) as [->|Hik].
        + rewrite !lookup_insert_eq. reflexivity.
        + rewrite lookup_insert_ne by congruence.
          rewrite lookup_insert_ne by congruence.
          rewrite lookup_delete_ne by congruence.
          reflexivity.
    }
    rewrite Hdel in Hη.
    rewrite lvars_open_env_insert_fresh in Hη.
    + intros Hy.
      apply Hη.
      apply lvars_fv_subset_open. exact Hy.
    + rewrite lookup_delete_ne by congruence. exact Hfresh.
Qed.

Lemma lvars_fv_difference_subset (D E : lvset) :
  lvars_fv (D ∖ E) ⊆ lvars_fv D.
Proof.
  intros x Hx.
  apply lvars_fv_elem.
  apply lvars_fv_elem in Hx.
  set_solver.
Qed.

(** [FExprResultAtLvar L e ν] exposes the complete lvar domain [L]
    read by the result atom.  The result coordinate [ν] is part of [L], but it
    is not an input/fiber coordinate: the expression is evaluated over the
    input projection [L ∖ {[ν]}].  This keeps continuation binders uniform:
    callers extend their environment once and pass its domain directly. *)
Definition FExprResultAtLvar (L : lvset) (e : tm) (ν : logic_var) : FQ :=
  let X := L ∖ {[ν]} in
  FFibVars X
    (FStoreResourceAtom L
      (fun η σ w =>
        match logic_var_to_atom η ν with
        | Some x =>
            expr_result_in_world (store_restrict σ (lvars_to_atoms η X))
              (open_tm_env η e) x w
        | None => False
        end)).

Definition FExprResultOn (L : lvset) (e : tm) : FQ :=
  FExprResultAtLvar (lvars_shift L ∪ {[LVBound 0]})
    (tm_shift 0 e) (LVBound 0).

Definition FExprResultAt (X : aset) (e : tm) (ν : atom) : FQ :=
  FExprResultAtLvar (lvars_of_atoms X ∪ {[LVFree ν]}) e (LVFree ν).

Lemma formula_open_FExprResultAtLvar_raw
    k x (L : lvset) (e : tm) (ν : logic_var) :
  formula_open k x (FExprResultAtLvar L e ν) =
  let X := L ∖ {[ν]} in
  FFibVars (lvars_open k x X)
    (FStoreResourceAtom (lvars_open k x L)
      (fun η σ w =>
        match logic_var_to_atom (<[k := x]> η) ν with
        | Some y =>
            expr_result_in_world
              (store_restrict σ (lvars_to_atoms (<[k := x]> η) X))
              (open_tm_env (<[k := x]> η) e) y w
        | None => False
        end)).
Proof. reflexivity. Qed.

Lemma FExprResultAtLvar_fv (L : lvset) e ν :
  formula_fv (FExprResultAtLvar L e ν) = lvars_fv L.
Proof.
  unfold FExprResultAtLvar, FStoreResourceAtom.
  cbn [formula_fv stale stale_logic_qualifier lqual_dom].
  denot_lvars_norm.
  pose proof (lvars_fv_difference_subset L ({[ν]} : lvset)).
  set_solver.
Qed.

Lemma FExprResultOn_lvars_fv (D : lvset) e :
  formula_fv (FExprResultOn D e) = lvars_fv D.
Proof.
  unfold FExprResultOn.
  rewrite FExprResultAtLvar_fv.
  rewrite lvars_fv_union, lvars_fv_singleton_bound.
  rewrite lvars_fv_shift.
  set_solver.
Qed.

Lemma FExprResultOn_fv X e :
  formula_fv (FExprResultOn (lvars_of_atoms X) e) = X.
Proof.
  rewrite FExprResultOn_lvars_fv.
  apply lvars_fv_of_atoms.
Qed.

Lemma FExprResultAt_fv X e ν :
  formula_fv (FExprResultAt X e ν) = X ∪ {[ν]}.
Proof.
  unfold FExprResultAt.
  rewrite FExprResultAtLvar_fv.
  denot_lvars_norm.
  rewrite lvars_fv_union, lvars_fv_of_atoms, lvars_fv_singleton_free.
  set_solver.
Qed.

Lemma FExprResultAt_input_lvars X ν :
  ν ∉ X →
  (lvars_of_atoms X ∪ {[LVFree ν]}) ∖ {[LVFree ν]} = lvars_of_atoms X.
Proof.
  intros HνX.
  apply set_eq. intros v.
  rewrite elem_of_difference, elem_of_union, elem_of_singleton.
  split.
  - intros [[Hv|Hv] Hne]; [exact Hv | contradiction].
  - intros Hv.
    split; [left; exact Hv |].
    intros Hvν.
    subst v.
    unfold lvars_of_atoms in Hv.
    apply elem_of_map in Hv as [x [Hx HxX]].
    inversion Hx; subst x.
    contradiction.
Qed.

Lemma FExprResultAt_input_fv X ν :
  ν ∉ X →
  lvars_fv ((lvars_of_atoms X ∪ {[LVFree ν]}) ∖ {[LVFree ν]}) = X.
Proof.
  intros HνX.
  rewrite FExprResultAt_input_lvars by exact HνX.
  apply lvars_fv_of_atoms.
Qed.

Lemma FExprResultAt_input_atoms η X ν :
  ν ∉ X →
  lvars_to_atoms η ((lvars_of_atoms X ∪ {[LVFree ν]}) ∖ {[LVFree ν]}) = X.
Proof.
  intros HνX.
  rewrite FExprResultAt_input_lvars by exact HνX.
  apply lvars_to_atoms_of_atoms.
Qed.

Lemma lvars_shift_of_atoms X :
  lvars_shift (lvars_of_atoms X) = lvars_of_atoms X.
Proof.
  unfold lvars_shift, lvars_of_atoms.
  apply set_eq. intros v.
  rewrite !elem_of_map.
  split.
  - intros [w [-> Hw]].
    rewrite elem_of_map in Hw.
    destruct Hw as [x [-> Hx]].
    exists x. split; [reflexivity | exact Hx].
  - intros [x [-> Hx]].
    exists (LVFree x). split; [reflexivity |].
    rewrite elem_of_map.
    exists x. split; [reflexivity | exact Hx].
Qed.

Lemma lvars_open_shift_of_atoms k x X :
  lvars_open k x (lvars_shift (lvars_of_atoms X)) = lvars_of_atoms X.
Proof.
  rewrite lvars_shift_of_atoms.
  apply lvars_open_of_atoms.
Qed.

Lemma lvars_to_atoms_shift_of_atoms η X :
  lvars_to_atoms η (lvars_shift (lvars_of_atoms X)) = X.
Proof.
  rewrite lvars_shift_of_atoms.
  apply lvars_to_atoms_of_atoms.
Qed.

Lemma lvars_to_atoms_elem η D x :
  x ∈ lvars_to_atoms η D ↔
  ∃ v, v ∈ D ∧ logic_var_to_atom η v = Some x.
Proof.
  unfold lvars_to_atoms.
  refine (set_fold_ind_L
    (fun acc D => ∀ x, x ∈ acc ↔
      ∃ v, v ∈ D ∧ logic_var_to_atom η v = Some x)
    (λ v acc,
      match logic_var_to_atom η v with
      | Some x => {[x]} ∪ acc
      | None => acc
      end) ∅ _ _ D x).
  - intros y. set_solver.
  - intros v D' acc Hfresh IH z.
    destruct (logic_var_to_atom η v) as [a|] eqn:Hv.
    + pose proof (IH z) as Hz. split.
      * intros Hx.
        apply elem_of_union in Hx as [Hx|Hx].
        -- apply elem_of_singleton in Hx. subst z.
           exists v. split; [set_solver | exact Hv].
        -- apply Hz in Hx.
           destruct Hx as [w [Hw Hwx]].
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
        apply Hz in Hx.
        destruct Hx as [w [Hw Hwx]].
        exists w. split; [set_solver | exact Hwx].
      * intros [w [Hw Hwx]].
        apply elem_of_union in Hw as [Hw|Hw].
        -- apply elem_of_singleton in Hw. subst w.
           rewrite Hv in Hwx. discriminate.
        -- apply Hz. exists w. split; [exact Hw | exact Hwx].
Qed.

Lemma logic_var_to_atom_open η k x v :
  logic_var_to_atom η (logic_var_open k x v) =
  logic_var_to_atom (<[k := x]> η) v.
Proof.
  destruct v as [j|y]; cbn [logic_var_open logic_var_to_atom].
  - destruct (decide (j = k)) as [->|Hne].
    + rewrite lookup_insert_eq. reflexivity.
    + rewrite lookup_insert_ne by congruence. reflexivity.
  - reflexivity.
Qed.

Lemma logic_var_shift_open k x v :
  logic_var_shift (logic_var_open k x v) =
  logic_var_open (S k) x (logic_var_shift v).
Proof.
  destruct v as [j|y]; cbn [logic_var_open logic_var_shift].
  - destruct (decide (j = k)) as [->|Hjk].
    + cbn [logic_var_open].
      destruct (decide (S k = S k)) as [_|Hbad]; [reflexivity | congruence].
    + cbn [logic_var_open].
      destruct (decide (S j = S k)) as [Heq|_].
      * inversion Heq. contradiction.
      * reflexivity.
  - reflexivity.
Qed.

Lemma lvars_shift_open k x D :
  lvars_shift (lvars_open k x D) =
  lvars_open (S k) x (lvars_shift D).
Proof.
  unfold lvars_shift, lvars_open.
  apply set_eq. intros v.
  rewrite !elem_of_map.
  split.
  - intros [w [-> Hw]].
    rewrite elem_of_map in Hw.
    destruct Hw as [u [-> Hu]].
    exists (logic_var_shift u). split.
    + rewrite <- logic_var_shift_open. reflexivity.
    + rewrite elem_of_map. eauto.
  - intros [w [-> Hw]].
    rewrite elem_of_map in Hw.
    destruct Hw as [u [-> Hu]].
    exists (logic_var_open k x u). split.
    + symmetry. apply logic_var_shift_open.
    + rewrite elem_of_map. eauto.
Qed.

Lemma lvars_to_atoms_insert_empty_subset k x D :
  lvars_to_atoms (<[k := x]> ∅) D ⊆ lvars_fv D ∪ {[x]}.
Proof.
  intros y Hy.
  apply lvars_to_atoms_elem in Hy.
  destruct Hy as [[j|z] [Hv Hlookup]]; cbn [logic_var_to_atom] in Hlookup.
  - destruct (decide (j = k)) as [->|Hne].
    + rewrite lookup_insert_eq in Hlookup. inversion Hlookup. subst y.
      set_solver.
    + rewrite lookup_insert_ne in Hlookup by congruence.
      rewrite lookup_empty in Hlookup. discriminate.
  - inversion Hlookup. subst y.
      assert (HzD : z ∈ lvars_fv D).
      { apply lvars_fv_elem. exact Hv. }
      set_solver.
Qed.

Lemma lvars_to_atoms_empty_subset D :
  lvars_to_atoms ∅ D ⊆ lvars_fv D.
Proof.
  intros x Hx.
  apply lvars_to_atoms_elem in Hx as [v [Hv Hatom]].
  destruct v as [k|y]; cbn [logic_var_to_atom] in Hatom.
  - rewrite lookup_empty in Hatom. discriminate.
  - inversion Hatom. subst y.
    apply lvars_fv_elem. exact Hv.
Qed.

Lemma lvars_to_atoms_open η k x D :
  lvars_to_atoms η (lvars_open k x D) =
  lvars_to_atoms (<[k := x]> η) D.
Proof.
  apply set_eq. intros y.
  rewrite !lvars_to_atoms_elem.
  split.
  - intros [v [Hv Hvy]].
    unfold lvars_open in Hv.
    apply elem_of_map in Hv as [u [-> Hu]].
    exists u. split; [exact Hu |].
    rewrite <- logic_var_to_atom_open. exact Hvy.
  - intros [v [Hv Hvy]].
    exists (logic_var_open k x v). split.
    + unfold lvars_open. apply elem_of_map. eauto.
    + rewrite logic_var_to_atom_open. exact Hvy.
Qed.

Lemma lvars_to_atoms_open_env η ξ D :
  lvars_to_atoms ξ (lvars_open_env η D) =
  lvars_to_atoms (open_env_precompose η ξ) D.
Proof.
  unfold lvars_open_env.
  revert ξ.
  refine (fin_maps.map_fold_ind
    (fun η =>
      ∀ ξ,
        lvars_to_atoms ξ
          (map_fold (fun k x acc => lvars_open k x acc) D η) =
        lvars_to_atoms (open_env_precompose η ξ) D) _ _ η).
  - intros ξ. rewrite map_fold_empty, open_env_precompose_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH ξ.
    rewrite Hfold.
    rewrite lvars_to_atoms_open.
    rewrite IH.
    rewrite open_env_precompose_insert_fresh by exact Hfresh.
    reflexivity.
Qed.

Lemma lvars_open_env_lift_shift η D :
  lvars_open_env (open_env_lift η) (lvars_shift D) =
  lvars_shift (lvars_open_env η D).
Proof.
  unfold lvars_open_env.
  refine (fin_maps.map_fold_ind
    (fun η =>
      map_fold (fun k x acc => lvars_open k x acc)
        (lvars_shift D) (open_env_lift η) =
      lvars_shift
        (map_fold (fun k x acc => lvars_open k x acc) D η)) _ _ η).
  - rewrite open_env_lift_empty, !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite open_env_lift_insert.
    rewrite Hfold.
    change (map_fold (fun k0 x0 acc => lvars_open k0 x0 acc)
      (lvars_shift D) (<[S k := x]> (open_env_lift η')) =
      lvars_shift (lvars_open k x
        (map_fold (fun k0 x0 acc => lvars_open k0 x0 acc) D η'))).
    change (map_fold (fun k0 x0 acc => lvars_open k0 x0 acc)
      (lvars_shift D) (<[S k := x]> (open_env_lift η')))
      with (lvars_open_env (<[S k := x]> (open_env_lift η')) (lvars_shift D)).
    rewrite lvars_open_env_insert_fresh.
    + change (lvars_open_env (open_env_lift η') (lvars_shift D))
        with (map_fold (fun k0 x0 acc => lvars_open k0 x0 acc)
          (lvars_shift D) (open_env_lift η')).
      rewrite IH.
      rewrite lvars_shift_open. reflexivity.
    + apply open_env_lift_lookup_none. exact Hfresh.
Qed.

Lemma lvars_open_env_lift_shift_bind η D :
  lvars_open_env (open_env_lift η)
    (lvars_shift D ∪ {[LVBound 0]}) =
  lvars_shift (lvars_open_env η D) ∪ {[LVBound 0]}.
Proof.
  unfold lvars_open_env.
  refine (fin_maps.map_fold_ind
    (fun η =>
      map_fold (fun k x acc => lvars_open k x acc)
        (lvars_shift D ∪ {[LVBound 0]}) (open_env_lift η) =
      lvars_shift
        (map_fold (fun k x acc => lvars_open k x acc) D η) ∪
      {[LVBound 0]}) _ _ η).
  - rewrite open_env_lift_empty, !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite open_env_lift_insert.
    rewrite Hfold.
    change (map_fold (fun k0 x0 acc => lvars_open k0 x0 acc)
      (lvars_shift D ∪ {[LVBound 0]})
      (<[S k := x]> (open_env_lift η')) =
      lvars_shift (lvars_open k x
        (map_fold (fun k0 x0 acc => lvars_open k0 x0 acc) D η')) ∪
      {[LVBound 0]}).
    change (map_fold (fun k0 x0 acc => lvars_open k0 x0 acc)
      (lvars_shift D ∪ {[LVBound 0]})
      (<[S k := x]> (open_env_lift η')))
      with (lvars_open_env (<[S k := x]> (open_env_lift η'))
        (lvars_shift D ∪ {[LVBound 0]})).
    rewrite lvars_open_env_insert_fresh.
    + change (lvars_open_env (open_env_lift η')
          (lvars_shift D ∪ {[LVBound 0]}))
        with (map_fold (fun k0 x0 acc => lvars_open k0 x0 acc)
          (lvars_shift D ∪ {[LVBound 0]}) (open_env_lift η')).
      rewrite IH.
      replace (lvars_open (S k) x
        (lvars_shift
          (map_fold (fun k0 x0 acc => lvars_open k0 x0 acc) D η') ∪
          {[LVBound 0]}))
        with (lvars_open (S k) x
          (lvars_shift
            (map_fold (fun k0 x0 acc => lvars_open k0 x0 acc) D η')) ∪
          {[LVBound 0]}).
      2:{
        unfold lvars_open.
        rewrite set_map_union_L.
        rewrite set_map_singleton_L.
        cbn [logic_var_open].
        destruct (decide (0 = S k)) as [Hbad|_]; [lia | reflexivity].
      }
      rewrite <- lvars_shift_open.
      reflexivity.
    + apply open_env_lift_lookup_none. exact Hfresh.
Qed.

Lemma lvars_to_atoms_shift_open_one η k x D :
  lvars_to_atoms η (lvars_shift (lvars_open k x D)) =
  lvars_to_atoms (<[S k := x]> η) (lvars_shift D).
Proof.
  rewrite lvars_shift_open.
  apply lvars_to_atoms_open.
Qed.

Lemma open_tm_env_shift_lc η k e :
  lc_tm e →
  open_tm_env η (tm_shift k e) = e.
Proof.
  intros Hlc.
  rewrite (tm_shift_lc_id k e Hlc).
  apply open_tm_env_lc. exact Hlc.
Qed.

Lemma formula_open_FExprResultAtLvar_shift_atom X e ν :
  ν ∉ X →
  lc_tm e →
  formula_open 0 ν
    (FExprResultAtLvar (lvars_shift (lvars_of_atoms X) ∪ {[LVBound 0]})
      (tm_shift 0 e) (LVBound 0)) =
  FExprResultAt X e ν.
Proof.
  intros HνX Hlc.
  rewrite formula_open_FExprResultAtLvar_raw.
  unfold FExprResultAt, FExprResultAtLvar.
  denot_lvars_norm.
  rewrite lvars_shift_of_atoms.
  assert (Hbound : LVBound 0 ∉ lvars_of_atoms X).
  {
    unfold lvars_of_atoms.
    intros Hin. apply elem_of_map in Hin as [x [Hx _]].
    inversion Hx.
  }
  replace ((lvars_of_atoms X ∪ {[LVBound 0]}) ∖ {[LVBound 0]})
    with (lvars_of_atoms X) by set_solver.
  rewrite lvars_open_of_atoms.
  replace (lvars_open 0 ν (lvars_of_atoms X ∪ {[LVBound 0]}))
    with (lvars_of_atoms X ∪ {[LVFree ν]}).
  2:{
    unfold lvars_open at 1.
    rewrite set_map_union_L, set_map_singleton_L.
    fold (lvars_open 0 ν (lvars_of_atoms X)).
    rewrite lvars_open_of_atoms.
    cbn [logic_var_open].
    destruct (decide (0 = 0)) as [_|Hbad]; [reflexivity | congruence].
  }
  rewrite FExprResultAt_input_lvars by exact HνX.
  f_equal. f_equal.
  apply functional_extensionality; intro η.
  apply functional_extensionality; intro σ.
  apply functional_extensionality; intro w.
  cbn [logic_var_to_atom].
  rewrite lookup_insert_eq.
  rewrite lvars_to_atoms_of_atoms.
  rewrite lvars_to_atoms_of_atoms.
  rewrite open_tm_env_shift_lc by exact Hlc.
  rewrite open_tm_env_lc by exact Hlc.
  reflexivity.
Qed.

Lemma FExprResultOn_scoped_dom X e ν m :
  formula_scoped_in_world ∅ m (FExprResultAt X e ν) →
  X ∪ {[ν]} ⊆ world_dom (m : World).
Proof.
  intros Hscope z Hz.
  apply Hscope.
  rewrite dom_empty_L.
  apply elem_of_union_r.
  rewrite FExprResultAt_fv.
  exact Hz.
Qed.

Lemma FExprResultAt_intro_from_expr_result_in_world
    X e ν (n : WfWorld) :
  lc_tm e →
  ν ∉ X →
  world_dom (n : World) = X ∪ {[ν]} →
  (∀ σX Hproj,
    expr_result_in_world (store_restrict σX X) e ν
      (res_fiber_from_projection n X σX Hproj)) →
  n ⊨ FExprResultAt X e ν.
Proof.
  intros Hlc HνX Hdom Hexpr.
  unfold FExprResultAt, FExprResultAtLvar.
  apply FFibVars_models_intro.
  - change (formula_scoped_in_world ∅ n (FExprResultAt X e ν)).
    unfold formula_scoped_in_world.
    rewrite dom_empty_L.
    rewrite FExprResultAt_fv.
    rewrite Hdom. set_solver.
  - unfold FFibVars_obligation.
    rewrite FExprResultAt_input_fv by exact HνX.
    split; [set_solver |].
    intros σX Hproj.
    unfold res_models_with_store, FStoreResourceAtom.
    cbn [formula_measure res_models_with_store_fuel formula_scoped_in_world
      formula_fv lqual_dom logic_qualifier_denote lqual_prop
      stale stale_logic_qualifier into_lvars into_lvars_aset
      into_lvars_lvset].
    denot_lvars_norm.
    rewrite lvars_fv_union, lvars_fv_of_atoms, lvars_fv_singleton_free.
    rewrite map_empty_union.
    split.
    + pose proof (wfworld_store_dom (res_restrict n X) σX Hproj)
        as HdomσX.
      simpl in HdomσX.
      unfold formula_scoped_in_world, FStoreResourceAtom.
      cbn [formula_fv stale stale_logic_qualifier lqual_dom into_lvars
        into_lvars_lvset].
      denot_lvars_norm.
      rewrite lvars_fv_union, lvars_fv_of_atoms, lvars_fv_singleton_free.
      simpl.
      rewrite HdomσX, Hdom. set_solver.
    + exists (res_fiber_from_projection n X σX Hproj).
      split.
      * pose proof (wfworld_store_dom (res_restrict n X) σX Hproj)
          as HdomσX.
        simpl in HdomσX.
        unfold formula_scoped_in_world, FStoreResourceAtom.
        cbn [formula_fv stale stale_logic_qualifier lqual_dom into_lvars
          into_lvars_lvset].
        denot_lvars_norm.
        rewrite lvars_fv_union, lvars_fv_of_atoms, lvars_fv_singleton_free.
        rewrite map_empty_union.
        simpl.
        rewrite HdomσX, Hdom. set_solver.
      * split.
        -- rewrite open_tm_env_empty.
           rewrite FExprResultAt_input_atoms by exact HνX.
           rewrite map_empty_union.
           store_norm.
           rewrite (inter_union_singleton_l X ν).
           replace (X ∪ {[ν]})
             with (world_dom (res_fiber_from_projection n X σX Hproj : World))
             by (simpl; exact Hdom).
           rewrite res_restrict_self.
           exact (Hexpr σX Hproj).
        -- reflexivity.
Qed.

Lemma FExprResultAt_fiber_expr_result_in_world
    X e ν (n : WfWorld) σX Hproj :
  lc_tm e →
  ν ∉ X →
  world_dom (n : World) = X ∪ {[ν]} →
  n ⊨ FExprResultAt X e ν →
  expr_result_in_world (store_restrict σX X) e ν
    (res_fiber_from_projection n X σX Hproj).
Proof.
  intros Hlc HνX Hdom Hmodel.
  unfold FExprResultAt, FExprResultAtLvar in Hmodel.
  destruct (FFibVars_models_elim _ _ _ _ Hmodel) as [_ Hfib].
  rewrite FExprResultAt_input_fv in Hfib by exact HνX.
  specialize (Hfib σX Hproj).
  unfold res_models_with_store, FStoreResourceAtom in Hfib.
  cbn [formula_measure res_models_with_store_fuel formula_scoped_in_world
    formula_fv lqual_dom logic_qualifier_denote lqual_prop
    stale stale_logic_qualifier into_lvars into_lvars_aset
    into_lvars_lvset] in Hfib.
  denot_lvars_norm.
  rewrite lvars_fv_union, lvars_fv_of_atoms, lvars_fv_singleton_free in Hfib.
  rewrite map_empty_union in Hfib.
  destruct Hfib as [_ [m0 [Hscope [Hresult Hle]]]].
  assert (Hm0_eq :
    m0 = res_fiber_from_projection n X σX Hproj).
  {
    apply res_le_same_dom_eq; [exact Hle |].
    unfold formula_scoped_in_world in Hscope.
    cbn [formula_fv stale stale_logic_qualifier lqual_dom] in Hscope.
    denot_lvars_norm.
    rewrite lvars_fv_union, lvars_fv_of_atoms, lvars_fv_singleton_free in Hscope.
    pose proof (raw_le_dom m0
      (res_fiber_from_projection n X σX Hproj) Hle) as Hle_dom.
    simpl in *.
    set_solver.
  }
  subst m0.
  rewrite open_tm_env_empty in Hresult.
  rewrite FExprResultAt_input_atoms in Hresult by exact HνX.
  rewrite map_empty_union in Hresult.
  store_norm.
  rewrite (inter_union_singleton_l X ν) in Hresult.
  replace (X ∪ {[ν]})
    with (world_dom (res_fiber_from_projection n X σX Hproj : World))
    in Hresult by (simpl; exact Hdom).
  rewrite res_restrict_self in Hresult.
  exact Hresult.
Qed.

(** Prop-level totality for the expression component of a type denotation.

    This is intentionally not encoded as a ChoiceLogic formula.  Since the core
    language is deterministic, totality is recorded as result reachability for
    every store in the world. *)
Definition expr_total_on (e : tm) (m : WfWorld) : Prop :=
  fv_tm e ⊆ world_dom (m : World) ∧
  ∀ σ, (m : World) σ →
    ∃ vx, subst_map (store_restrict σ (fv_tm e)) e →* tret vx.

Notation "m '|=total' e" := (expr_total_on e m)
  (at level 70, e at next level).

Lemma expr_total_on_restrict_self X e (m : WfWorld) :
  fv_tm e ⊆ X →
  expr_total_on e m →
  expr_total_on e (res_restrict m X).
Proof.
  intros HfvX [Hfv Htotal]. split; [simpl; set_solver |].
  intros σ [σm [Hσm <-]].
  rewrite store_restrict_twice_subset by exact HfvX.
  apply Htotal. exact Hσm.
Qed.

(** [world_closed_on X m] is the ChoiceType-level invariant saying that every
    store in [m] is operationally usable on the coordinates [X].  This belongs
    here rather than in ChoiceAlgebra: the algebra is polymorphic in store
    values, while closedness is a CoreLang [value] property. *)
Definition world_closed_on (X : aset) (m : WfWorld) : Prop :=
  ∀ σ, (m : World) σ → store_closed (store_restrict σ X).

#[global] Instance scoped_wf_world : ScopedIn WfWorld := world_closed_on.

Module WorldScopingNotationSmoke.
  Section Smoke.
    Variable X : aset.
    Variable m : WfWorld.

    Example scoped_world_notation :
      (X ⊢s m) = world_closed_on X m := eq_refl.
  End Smoke.
End WorldScopingNotationSmoke.

Lemma scoped_world_iff X m :
  X ⊢s m ↔ world_closed_on X m.
Proof. reflexivity. Qed.

Lemma world_closed_on_le X m n :
  m ⊑ n →
  world_closed_on X n →
  world_closed_on X m.
Proof.
  intros Hle Hclosed σ Hσ.
  unfold world_closed_on in Hclosed.
  unfold sqsubseteq, wf_world_sqsubseteq, raw_le in Hle.
  change ((m : World) σ) in Hσ.
  rewrite Hle in Hσ. simpl in Hσ.
  destruct Hσ as [σn [Hσn Hrestrict]].
  rewrite <- Hrestrict.
  rewrite store_restrict_comm.
  apply store_closed_restrict.
  exact (Hclosed σn Hσn).
Qed.

Lemma world_closed_on_extend X (m n : WfWorld) :
  X ⊆ world_dom (m : World) →
  m ⊑ n →
  world_closed_on X m →
  world_closed_on X n.
Proof.
  intros HXm Hle Hclosed σ Hσ.
  pose proof (res_restrict_eq_of_le m n Hle) as Hrestrict.
  assert ((res_restrict n (world_dom (m : World)) : World)
    (store_restrict σ (world_dom (m : World)))) as Hσm.
  { exists σ. split; [exact Hσ | reflexivity]. }
  rewrite Hrestrict in Hσm.
  replace (store_restrict σ X) with
    (store_restrict (store_restrict σ (world_dom (m : World))) X).
  - exact (Hclosed _ Hσm).
  - store_norm. reflexivity.
Qed.

Lemma world_closed_on_restrict_store_closed X (m : WfWorld) σ :
  world_closed_on X m →
  (res_restrict m X : World) σ →
  store_closed σ.
Proof.
  intros Hclosed [σ0 [Hσ0 <-]].
  exact (Hclosed σ0 Hσ0).
Qed.

Lemma world_closed_on_store_restrict_closed X Y (m : WfWorld) σ :
  Y ⊆ X →
  world_closed_on X m →
  (m : World) σ →
  store_closed (store_restrict σ Y).
Proof.
  intros HYX Hclosed Hσ.
  replace (store_restrict σ Y) with
    (store_restrict (store_restrict σ X) Y).
  - apply store_closed_restrict. exact (Hclosed σ Hσ).
  - rewrite store_restrict_twice_subset by exact HYX. reflexivity.
Qed.

Lemma world_closed_on_mono (X Y : aset) (m : WfWorld) :
  X ⊆ Y →
  world_closed_on Y m →
  world_closed_on X m.
Proof.
  intros HXY Hclosed σ Hσ.
  specialize (Hclosed σ Hσ) as Hclosed_env.
  replace (store_restrict σ X) with
    (store_restrict (store_restrict σ Y) X).
  - apply store_closed_restrict. exact Hclosed_env.
  - rewrite store_restrict_twice_subset by exact HXY. reflexivity.
Qed.

Lemma expr_total_on_to_fv_result X e (m : WfWorld) :
  world_closed_on X m →
  expr_total_on e m →
  ∀ σ, (m : World) σ →
    ∃ vx, subst_map (store_restrict σ (fv_tm e)) e →* tret vx.
Proof.
  intros _ [_ Htotal] σ Hσ.
  apply Htotal. exact Hσ.
Qed.

Lemma msubst_closed_tm_of_restrict_world X e (m : WfWorld) σ :
  X ⊆ world_dom (m : World) →
  fv_tm e ⊆ X →
  lc_tm e →
  world_closed_on X m →
  (res_restrict m X : World) σ →
  closed_tm (subst_map (store_restrict σ X) e).
Proof.
  intros HXm Hfv Hlc Hclosed Hσ.
  assert (Hdomσ : dom σ ⊆ X).
  {
    pose proof (wfworld_store_dom (res_restrict m X) σ Hσ) as Hdom.
    simpl in Hdom. set_solver.
  }
  replace (store_restrict σ X) with σ.
  - apply msubst_closed_tm.
    + eapply world_closed_on_restrict_store_closed; eauto.
    + eauto 6.
    + change (fv_tm e ⊆ dom σ).
      pose proof (wfworld_store_dom (res_restrict m X) σ Hσ) as Hdom.
      simpl in Hdom. rewrite Hdom. set_solver.
  - symmetry. apply store_restrict_idemp. exact Hdomσ.
Qed.

Lemma steps_closed_result_of_restrict_world X e (m : WfWorld) σ v :
  X ⊆ world_dom (m : World) →
  fv_tm e ⊆ X →
  lc_tm e →
  world_closed_on X m →
  (res_restrict m X : World) σ →
  subst_map (store_restrict σ X) e →* tret v →
  stale v = ∅ ∧ is_lc v.
Proof.
  intros HXm Hfv Hlc Hclosed Hσ Hsteps.
  eapply steps_closed_result.
  - eapply msubst_closed_tm_of_restrict_world; eauto.
  - eauto 6.
Qed.

Lemma body_tm_msubst_restrict_world X e (m : WfWorld) σ :
  body_tm e →
  world_closed_on X m →
  (res_restrict m X : World) σ →
  body_tm (subst_map (store_restrict σ X) e).
Proof.
  intros Hbody Hclosed Hσ.
  assert (Hdomσ : dom σ ⊆ X).
  {
    pose proof (wfworld_store_dom (res_restrict m X) σ Hσ) as Hdom.
    simpl in Hdom. set_solver.
  }
  replace (store_restrict σ X) with σ.
  - apply body_tm_msubst.
    + exact (proj1 (world_closed_on_restrict_store_closed X m σ
        Hclosed Hσ)).
    + exact (proj2 (world_closed_on_restrict_store_closed X m σ
        Hclosed Hσ)).
    + eauto 6.
  - symmetry. apply store_restrict_idemp. exact Hdomσ.
Qed.

Lemma world_closed_on_restrict X Y (m : WfWorld) :
  X ⊆ Y →
  world_closed_on X m →
  world_closed_on X (res_restrict m Y).
Proof.
  intros HXY Hclosed σ Hσ.
  destruct Hσ as [σ0 [Hσ0 Hrestrict]].
  rewrite <- Hrestrict.
  store_norm.
  exact (Hclosed σ0 Hσ0).
Qed.

Lemma fresh_notin_restrict_insert_dom X x (n : WfWorld) :
  x ∉ X →
  world_dom (n : World) = X ∪ {[x]} →
  x ∉ world_dom (res_restrict n X : World).
Proof.
  intros HxX Hdom Hx.
  simpl in Hx. rewrite Hdom in Hx. set_solver.
Qed.

Lemma res_restrict_insert_dom_eq X x (n : WfWorld) :
  world_dom (n : World) = X ∪ {[x]} →
  world_dom (res_restrict n X : World) = X.
Proof.
  intros Hdom. simpl. rewrite Hdom. set_solver.
Qed.

Lemma expr_total_on_tlete_elim_e1_strong X e1 e2 (m : WfWorld) :
  fv_tm (tlete e1 e2) ⊆ X →
  world_closed_on X m →
  expr_total_on (tlete e1 e2) m →
  expr_total_on e1 m.
Proof.
  intros HfvX Hclosed [Hfv Htotal].
  split; [simpl in Hfv; set_solver |].
  intros σ Hσ.
  destruct (Htotal σ Hσ) as [v Hsteps].
  rewrite (subst_map_restrict_to_fv_from_superset
    (tlete e1 e2) X σ HfvX (proj1 (Hclosed σ Hσ))) in Hsteps.
  change (m{store_restrict σ X} (tlete e1 e2) →* tret v) in Hsteps.
  rewrite msubst_lete in Hsteps.
  apply reduction_lete in Hsteps as [vx [HstepsX _]].
  exists vx.
  rewrite (subst_map_restrict_to_fv_from_superset e1
    X σ ltac:(simpl in HfvX; set_solver)).
  - exact HstepsX.
  - exact (proj1 (Hclosed σ Hσ)).
Qed.

Lemma basic_world_formula_world_closed_on Σ X m :
  X ⊆ dom Σ →
  m ⊨ basic_world_formula Σ X →
  world_closed_on X m.
Proof.
  intros HXΣ Hbasic σ Hσ.
  split.
  - eapply basic_world_formula_store_restrict_closed_env; eauto.
  - eapply basic_world_formula_store_restrict_lc_env; eauto.
Qed.

Lemma expr_result_store_let_elim ρ e1 e2 ν σw :
  expr_result_store ν (subst_map ρ (tlete e1 e2)) σw →
  ∃ v vx,
    σw = {[ν := v]} ∧
    subst_map ρ e1 →* tret vx ∧
    open_tm 0 vx (subst_map ρ e2) →* tret v.
Proof.
  intros Hstore.
  destruct (expr_result_store_elim ν (subst_map ρ (tlete e1 e2)) σw Hstore)
    as [v [Hσw [_ [_ Hsteps]]]].
  change (subst_map ρ (tlete e1 e2)) with (m{ρ} (tlete e1 e2)) in Hsteps.
  rewrite msubst_lete in Hsteps.
  destruct (reduction_lete (m{ρ} e1) (m{ρ} e2) v Hsteps)
    as [vx [Hsteps1 Hsteps2]].
  exists v, vx. repeat split; assumption.
Qed.

Lemma expr_result_in_world_let_elim ρ e1 e2 ν (w : WfWorld) :
  expr_result_in_world ρ (tlete e1 e2) ν w →
  ∀ σν,
    (res_restrict w {[ν]} : World) σν →
    ∃ v vx,
      σν = {[ν := v]} ∧
      subst_map ρ e1 →* tret vx ∧
      open_tm 0 vx (subst_map ρ e2) →* tret v.
Proof.
  intros Hworld σν Hσν.
  pose proof (expr_result_in_world_sound ρ (tlete e1 e2) ν w σν
    Hworld Hσν) as Hstore.
  exact (expr_result_store_let_elim ρ e1 e2 ν σν Hstore).
Qed.

Lemma expr_result_store_let_intro ρ e1 e2 ν v vx :
  stale v = ∅ →
  is_lc v →
  body_tm (subst_map ρ e2) →
  subst_map ρ e1 →* tret vx →
  open_tm 0 vx (subst_map ρ e2) →* tret v →
  expr_result_store ν (subst_map ρ (tlete e1 e2)) {[ν := v]}.
Proof.
  intros Hv_closed Hv_lc Hbody Hsteps1 Hsteps2.
  apply expr_result_store_intro; [exact Hv_closed | exact Hv_lc |].
  change (subst_map ρ (tlete e1 e2)) with (m{ρ} (tlete e1 e2)).
  rewrite msubst_lete.
  eapply reduction_lete_intro; eauto.
Qed.

Lemma expr_result_in_world_let_intro ρ e1 e2 ν (w : WfWorld) :
  body_tm (subst_map ρ e2) →
  (∀ σν,
    (res_restrict w {[ν]} : World) σν ↔
    ∃ v vx,
      σν = {[ν := v]} ∧
      stale v = ∅ ∧
      is_lc v ∧
      subst_map ρ e1 →* tret vx ∧
      open_tm 0 vx (subst_map ρ e2) →* tret v) →
  expr_result_in_world ρ (tlete e1 e2) ν w.
Proof.
  intros Hbody Hexact σν. split.
  - intros Hσν.
    destruct (proj1 (Hexact σν) Hσν)
      as [v [vx [Hσν_eq [Hv_closed [Hv_lc [Hsteps1 Hsteps2]]]]]].
    subst σν.
    eapply expr_result_store_let_intro; eauto.
  - intros Hstore.
    destruct (expr_result_store_elim ν (subst_map ρ (tlete e1 e2)) σν Hstore)
      as [v [Hσν_eq [Hv_closed [Hv_lc Hsteps]]]].
    destruct (expr_result_store_let_elim ρ e1 e2 ν σν Hstore)
      as [v' [vx [Hσν_eq' [Hsteps1 Hsteps2]]]].
    subst σν.
    assert (Hv' : v' = v).
    {
      assert (({[ν := v']} : Store) !! ν = Some v).
      {
        rewrite <- Hσν_eq'.
        rewrite lookup_singleton. rewrite decide_True by reflexivity.
        reflexivity.
      }
      rewrite lookup_singleton in H.
      rewrite decide_True in H by reflexivity.
      inversion H. reflexivity.
    }
    subst v'.
    apply (proj2 (Hexact {[ν := v]})).
    exists v, vx. repeat split; eauto.
Qed.

Lemma expr_result_store_tlete_to_body_open_atom ρ e1 e2 x ν σν :
  closed_env ρ →
  lc_env ρ →
  x ∉ dom ρ ∪ fv_tm e2 →
  (∀ vx, subst_map ρ e1 →* tret vx → stale vx = ∅ ∧ is_lc vx) →
  expr_result_store ν (subst_map ρ (tlete e1 e2)) σν →
  ∃ vx,
    subst_map ρ e1 →* tret vx ∧
    expr_result_store ν (subst_map (<[x := vx]> ρ) (e2 ^^ x)) σν.
Proof.
  intros Hclosed Hlc Hx Hresult_closed Hstore.
  destruct (expr_result_store_elim ν (subst_map ρ (tlete e1 e2)) σν Hstore)
    as [v [Hσν [Hv_closed [Hv_lc _]]]].
  destruct (expr_result_store_let_elim ρ e1 e2 ν σν Hstore)
    as [v' [vx [Hσν' [Hsteps1 Hsteps2]]]].
  subst σν.
  assert (Hv' : v' = v).
  {
    assert (({[ν := v']} : Store) !! ν = Some v).
    {
      rewrite <- Hσν'.
      rewrite lookup_singleton. rewrite decide_True by reflexivity.
      reflexivity.
    }
    rewrite lookup_singleton in H.
    rewrite decide_True in H by reflexivity.
    inversion H. reflexivity.
  }
  subst v'.
  exists vx. split; [exact Hsteps1 |].
  apply expr_result_store_intro; [exact Hv_closed | exact Hv_lc |].
  change (subst_map (<[x := vx]> ρ) (e2 ^^ x)) with
    (m{<[x := vx]> ρ} (open_tm 0 (vfvar x) e2)).
  rewrite (msubst_intro_open_tm e2 0 vx x ρ).
  - exact Hsteps2.
  - exact Hclosed.
  - apply (proj1 (Hresult_closed vx Hsteps1)).
  - apply (proj2 (Hresult_closed vx Hsteps1)).
  - exact Hlc.
  - exact Hx.
Qed.

Lemma expr_result_store_body_open_to_tlete ρ e1 e2 x ν σν vx :
  closed_env ρ →
  lc_env ρ →
  body_tm (subst_map ρ e2) →
  x ∉ dom ρ ∪ fv_tm e2 →
  stale vx = ∅ →
  is_lc vx →
  subst_map ρ e1 →* tret vx →
  expr_result_store ν (subst_map (<[x := vx]> ρ) (e2 ^^ x)) σν →
  expr_result_store ν (subst_map ρ (tlete e1 e2)) σν.
Proof.
  intros Hclosed Hlc Hbody Hx Hv_closed Hv_lc Hsteps1 Hstore.
  destruct (expr_result_store_elim ν
    (subst_map (<[x := vx]> ρ) (e2 ^^ x)) σν Hstore)
    as [v [Hσν [Hres_closed [Hres_lc Hsteps2]]]].
  subst σν.
  eapply expr_result_store_let_intro; eauto.
  change (subst_map (<[x := vx]> ρ) (e2 ^^ x)) with
    (m{<[x := vx]> ρ} (open_tm 0 (vfvar x) e2)) in Hsteps2.
  rewrite (msubst_intro_open_tm e2 0 vx x ρ) in Hsteps2.
  - exact Hsteps2.
  - exact Hclosed.
  - exact Hv_closed.
  - exact Hv_lc.
  - exact Hlc.
  - exact Hx.
Qed.

Lemma expr_result_store_ret_fvar_lookup x ν σw vx :
  stale vx = ∅ →
  σw !! x = Some vx →
  expr_result_store ν (subst_map ∅ (tret (vfvar x))) σw →
  σw !! ν = Some vx.
Proof.
  intros _ _ Hret.
  destruct (expr_result_store_elim ν (subst_map ∅ (tret (vfvar x))) σw Hret)
    as [v [-> [Hv_stale [_ Hsteps]]]].
  simpl in Hsteps.
  pose proof (value_steps_self (vfvar x) (tret v) Hsteps) as Heq.
  inversion Heq. subst v.
  simpl in Hv_stale. set_solver.
Qed.

Lemma expr_result_store_ret_fvar_trans ρ e x ν σw :
  (∀ vx, subst_map σw (subst_map ρ e) →* tret vx → stale vx = ∅) →
  expr_result_store x (subst_map ρ e) σw →
  expr_result_store ν (subst_map ∅ (tret (vfvar x))) σw →
  expr_result_store ν (subst_map ρ e) σw.
Proof.
  intros _ _ Hret.
  destruct (expr_result_store_elim ν (subst_map ∅ (tret (vfvar x))) σw Hret)
    as [v [-> [Hv_stale [_ Hsteps]]]].
  simpl in Hsteps.
  pose proof (value_steps_self (vfvar x) (tret v) Hsteps) as Heq.
  inversion Heq. subst v.
  simpl in Hv_stale. set_solver.
Qed.

Lemma expr_result_in_world_ret_fvar_trans ρ e x ν (w : WfWorld) :
  (∀ σw vx,
    (w : World) σw →
    subst_map σw (subst_map ρ e) →* tret vx →
    stale vx = ∅) →
  expr_result_in_world ρ e x w →
  expr_result_in_world ∅ (tret (vfvar x)) ν w →
  expr_result_in_world ρ e ν w.
Proof.
  intros _ _ Hret_world.
  exfalso.
  destruct (world_wf w) as [[σ Hσ] _].
  set (σν := store_restrict σ {[ν]}).
  assert (Hprojν : (res_restrict w {[ν]} : World) σν).
  { exists σ. split; [exact Hσ | reflexivity]. }
  pose proof (expr_result_in_world_sound ∅ (tret (vfvar x)) ν w σν
    Hret_world Hprojν) as Hret.
  destruct (expr_result_store_elim ν (subst_map ∅ (tret (vfvar x))) σν Hret)
    as [v [-> [Hv_stale [_ Hsteps]]]].
  simpl in Hsteps.
  pose proof (value_steps_self (vfvar x) (tret v) Hsteps) as Heq.
  inversion Heq. subst v.
  simpl in Hv_stale. set_solver.
Qed.
