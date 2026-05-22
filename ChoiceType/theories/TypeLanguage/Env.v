(** * ChoiceType.TypeLanguage.Env

    Pure locally-nameless environment operations for choice types.

    These definitions are syntax-level infrastructure: logic-variable type
    environments, multi-opening by finite maps, and the small map-fold laws used
    by later denotation files.  They deliberately live below semantic
    denotation. *)

From Stdlib Require Import Classes.RelationClasses Classes.Morphisms.
From LocallyNameless Require Import Classes.
From ChoiceType.TypeLanguage Require Export Syntax.

Definition lty_env : Type := gmap logic_var ty.

Definition lty_env_shift_from (k : nat) (Σ : lty_env) : lty_env :=
  kmap (logic_var_shift_from k) Σ.

Definition lty_env_shift (Σ : lty_env) : lty_env :=
  lty_env_shift_from 0 Σ.

Definition lty_env_open_one (k : nat) (x : atom) (Σ : lty_env) : lty_env :=
  kmap (logic_var_open k x) Σ.

Definition lty_env_closed (Σ : lty_env) : Prop :=
  lvars_bv (dom Σ) = ∅.

Definition atom_env_to_lty_env (Σ : gmap atom ty) : lty_env :=
  map_fold (fun x T acc => <[LVFree x := T]> acc) ∅ Σ.

Definition lvar_to_atom (η : gmap nat atom) (v : logic_var) : option atom :=
  logic_var_to_atom η v.

Definition lty_env_open (η : gmap nat atom) (Σ : lty_env) : gmap atom ty :=
  map_fold (fun v T acc =>
    match lvar_to_atom η v with
    | Some x => <[x := T]> acc
    | None => acc
    end) ∅ Σ.

Definition lty_env_open_lvars (η : gmap nat atom) (Σ : lty_env) : lty_env :=
  map_fold (fun v T acc => <[logic_var_open_env η v := T]> acc) ∅ Σ.

Definition lty_env_atom_dom (Σ : lty_env) : aset :=
  lvars_fv (dom Σ).

Definition lty_env_bvar_scope (Σ : lty_env) : lvset :=
  lvars_of_bvars (lvars_bv (dom Σ)).

Definition typed_lty_env_bind (Σ : lty_env) (T : ty) : lty_env :=
  <[LVBound 0 := T]> (lty_env_shift Σ).

Definition lty_env_agree_on_lvars
    (D : lvset) (Σ1 Σ2 : lty_env) : Prop :=
  forall v, v ∈ D -> Σ1 !! v = Σ2 !! v.

Definition lty_env_swap (x y : atom) (Σ : lty_env) : lty_env :=
  kmap (fun v =>
    match v with
    | LVFree z => LVFree (atom_swap x y z)
    | LVBound k => LVBound k
    end) Σ.

Class MOpen Env A B := mopen : Env -> A -> B.

Notation "η ⊙ x" := (mopen η x)
  (at level 30, right associativity, format "η  ⊙  x").

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
  OpenProper choice_ty cty_open cty_vars_equiv.
Proof.
Admitted.

#[global] Instance open_commute_cty_vars_equiv :
  OpenCommute choice_ty cty_open cty_vars_equiv.
Proof.
Admitted.

#[global] Instance open_commute_cty_eq :
  OpenCommute choice_ty cty_open eq.
Proof.
Admitted.

#[global] Instance open_commute_lvars :
  OpenCommute lvset lvars_open eq.
Proof.
Admitted.

#[global] Instance open_commute_qual_eq :
  OpenCommute type_qualifier qual_open_atom eq.
Proof.
Admitted.

Class MOpenInsertLaws A B `{Open atom A}
    `{MOpen (gmap nat atom) A B} := {
  mopen_insert_norm :
    forall k x η (a : A),
      η !! k = None ->
      open_env_avoids_atom x η ->
      mopen η ({k ~> x} a) = mopen (<[k := x]> η) a;
}.

Definition open_cty_env (η : gmap nat atom) (τ : choice_ty) : choice_ty :=
  map_fold (fun k x acc => cty_open k x acc) τ η.

Definition qual_open_env (η : gmap nat atom) (q : type_qualifier)
    : type_qualifier :=
  map_fold (fun k x acc => qual_open_atom k x acc) q η.

Definition qual_with_vars (D : lvset) : type_qualifier :=
  tqual D (fun _ => True).

#[global] Instance mopen_choice_ty_inst :
  MOpen (gmap nat atom) choice_ty choice_ty := open_cty_env.

#[global] Instance open_lty_env_atom_inst : Open atom lty_env :=
  lty_env_open_one.

#[global] Instance mopen_lty_env_inst :
  MOpen (gmap nat atom) lty_env (gmap atom ty) := lty_env_open.

#[global] Instance into_lvars_atom_ty_env : IntoLVars (gmap atom ty) :=
  fun Σ => lvars_of_atoms (dom Σ).

#[global] Instance into_lvars_logic_ty_env : IntoLVars (gmap logic_var ty) :=
  fun Σ => dom Σ.

Lemma open_map_fold_insert_fresh_eq
    {A : Type} (openA : nat -> atom -> A -> A)
    `{!OpenCommute A openA eq}
    (η : gmap nat atom) k x (a : A) :
  η !! k = None ->
  open_env_avoids_atom x η ->
  map_fold openA a (<[k := x]> η) =
  openA k x (map_fold openA a η).
Proof.
Admitted.

Lemma open_map_fold_insert_fresh_rel
    {A : Type} (R : relation A) `{!PreOrder R}
    (openA : nat -> atom -> A -> A)
    `{HproperInst : !OpenProper A openA R}
    `{HcommuteInst : !OpenCommute A openA R}
    (η : gmap nat atom) k x (a : A) :
  η !! k = None ->
  open_env_avoids_atom x η ->
  R (map_fold openA a (<[k := x]> η))
    (openA k x (map_fold openA a η)).
Proof.
Admitted.

Lemma open_cty_env_empty τ :
  open_cty_env ∅ τ = τ.
Proof.
Admitted.

Lemma open_cty_env_singleton k x τ :
  open_cty_env (<[k := x]> ∅) τ = cty_open k x τ.
Proof.
Admitted.

Lemma open_cty_env_insert_fresh η k x τ :
  η !! k = None ->
  open_env_avoids_atom x η ->
  open_cty_env (<[k := x]> η) τ =
  cty_open k x (open_cty_env η τ).
Proof.
Admitted.

Lemma qual_open_env_empty q :
  qual_open_env ∅ q = q.
Proof.
Admitted.

Lemma qual_open_env_insert_fresh η k x q :
  η !! k = None ->
  open_env_avoids_atom x η ->
  qual_open_env (<[k := x]> η) q =
  qual_open_atom k x (qual_open_env η q).
Proof.
Admitted.

Lemma open_cty_env_cty_vars_equiv η τ1 τ2 :
  τ1 ≡τv τ2 ->
  open_cty_env η τ1 ≡τv open_cty_env η τ2.
Proof.
Admitted.

Lemma open_cty_env_open_fresh_vars_equiv η k x τ :
  η !! k = None ->
  open_env_avoids_atom x η ->
  open_cty_env η (cty_open k x τ) ≡τv
  cty_open k x (open_cty_env η τ).
Proof.
Admitted.

Lemma open_cty_env_insert_fresh_vars_equiv η k x τ :
  η !! k = None ->
  open_env_avoids_atom x η ->
  open_cty_env (<[k := x]> η) τ ≡τv
  cty_open k x (open_cty_env η τ).
Proof.
Admitted.

Lemma open_cty_env_open_one_vars_equiv η k x τ :
  η !! k = None ->
  open_env_avoids_atom x η ->
  open_cty_env η (cty_open k x τ) ≡τv
  open_cty_env (<[k := x]> η) τ.
Proof.
Admitted.

Lemma open_cty_env_open_one η k x τ :
  η !! k = None ->
  open_env_avoids_atom x η ->
  open_cty_env η (cty_open k x τ) =
  open_cty_env (<[k := x]> η) τ.
Proof.
Admitted.

Lemma open_cty_env_inter η τ1 τ2 :
  open_cty_env η (CTInter τ1 τ2) =
  CTInter (open_cty_env η τ1) (open_cty_env η τ2).
Proof.
Admitted.

Lemma open_cty_env_union η τ1 τ2 :
  open_cty_env η (CTUnion τ1 τ2) =
  CTUnion (open_cty_env η τ1) (open_cty_env η τ2).
Proof.
Admitted.

Lemma open_cty_env_sum η τ1 τ2 :
  open_cty_env η (CTSum τ1 τ2) =
  CTSum (open_cty_env η τ1) (open_cty_env η τ2).
Proof.
Admitted.

Lemma open_cty_env_arrow η τx τ :
  open_cty_env η (CTArrow τx τ) =
  CTArrow (open_cty_env η τx) (open_cty_env (open_env_lift η) τ).
Proof.
Admitted.

Lemma open_cty_env_wand η τx τ :
  open_cty_env η (CTWand τx τ) =
  CTWand (open_cty_env η τx) (open_cty_env (open_env_lift η) τ).
Proof.
Admitted.

Lemma open_cty_env_over η b q :
  open_cty_env η (CTOver b q) =
  CTOver b (qual_open_env (open_env_lift η) q).
Proof.
Admitted.

Lemma open_cty_env_under η b q :
  open_cty_env η (CTUnder b q) =
  CTUnder b (qual_open_env (open_env_lift η) q).
Proof.
Admitted.

Lemma open_cty_env_preserves_erasure η τ :
  erase_ty (open_cty_env η τ) = erase_ty τ.
Proof.
Admitted.

Lemma open_cty_env_inter_vars_equiv η τ1 τ2 :
  open_cty_env η (CTInter τ1 τ2) ≡τv
  CTInter (open_cty_env η τ1) (open_cty_env η τ2).
Proof.
Admitted.

Lemma open_cty_env_union_vars_equiv η τ1 τ2 :
  open_cty_env η (CTUnion τ1 τ2) ≡τv
  CTUnion (open_cty_env η τ1) (open_cty_env η τ2).
Proof.
Admitted.

Lemma open_cty_env_sum_vars_equiv η τ1 τ2 :
  open_cty_env η (CTSum τ1 τ2) ≡τv
  CTSum (open_cty_env η τ1) (open_cty_env η τ2).
Proof.
Admitted.

Lemma open_cty_env_arrow_vars_equiv η τx τ :
  open_cty_env η (CTArrow τx τ) ≡τv
  CTArrow (open_cty_env η τx) (open_cty_env (open_env_lift η) τ).
Proof.
Admitted.

Lemma open_cty_env_wand_vars_equiv η τx τ :
  open_cty_env η (CTWand τx τ) ≡τv
  CTWand (open_cty_env η τx) (open_cty_env (open_env_lift η) τ).
Proof.
Admitted.

Lemma open_cty_env_over_vars_equiv η b q :
  open_cty_env η (CTOver b q) ≡τv
  CTOver b (qual_with_vars (lvars_open_env (open_env_lift η) (qual_vars q))).
Proof.
Admitted.

Lemma open_cty_env_under_vars_equiv η b q :
  open_cty_env η (CTUnder b q) ≡τv
  CTUnder b (qual_with_vars (lvars_open_env (open_env_lift η) (qual_vars q))).
Proof.
Admitted.

Lemma open_cty_env_lift_shift0_vars_equiv η τ :
  open_cty_env (open_env_lift η) (cty_shift 0 τ) ≡τv
  cty_shift 0 (open_cty_env η τ).
Proof.
Admitted.

Lemma lty_env_agree_on_lvars_mono D E Σ1 Σ2 :
  D ⊆ E ->
  lty_env_agree_on_lvars E Σ1 Σ2 ->
  lty_env_agree_on_lvars D Σ1 Σ2.
Proof.
Admitted.

Lemma lty_env_agree_on_lvars_refl D Σ :
  lty_env_agree_on_lvars D Σ Σ.
Proof.
Admitted.

Lemma lty_env_agree_on_lvars_sym D Σ1 Σ2 :
  lty_env_agree_on_lvars D Σ1 Σ2 ->
  lty_env_agree_on_lvars D Σ2 Σ1.
Proof.
Admitted.

Lemma lty_env_agree_on_lvars_union D1 D2 Σ1 Σ2 :
  lty_env_agree_on_lvars D1 Σ1 Σ2 ->
  lty_env_agree_on_lvars D2 Σ1 Σ2 ->
  lty_env_agree_on_lvars (D1 ∪ D2) Σ1 Σ2.
Proof.
Admitted.

Lemma lty_env_agree_on_lvars_insert_same D Σ1 Σ2 v T :
  lty_env_agree_on_lvars (D ∖ {[v]}) Σ1 Σ2 ->
  lty_env_agree_on_lvars D (<[v := T]> Σ1) (<[v := T]> Σ2).
Proof.
Admitted.

Lemma lty_env_agree_on_lvars_insert_same_keep D Σ1 Σ2 v T :
  lty_env_agree_on_lvars D Σ1 Σ2 ->
  lty_env_agree_on_lvars (D ∪ {[v]})
    (<[v := T]> Σ1) (<[v := T]> Σ2).
Proof.
Admitted.

Lemma lty_env_atom_dom_shift_from k Σ :
  lty_env_atom_dom (lty_env_shift_from k Σ) = lty_env_atom_dom Σ.
Proof.
Admitted.

Lemma lty_env_atom_dom_shift Σ :
  lty_env_atom_dom (lty_env_shift Σ) = lty_env_atom_dom Σ.
Proof.
Admitted.

Lemma lty_env_agree_on_lvars_shift_from k D Σ1 Σ2 :
  lty_env_agree_on_lvars D Σ1 Σ2 ->
  lty_env_agree_on_lvars (lvars_shift_from k D)
    (lty_env_shift_from k Σ1) (lty_env_shift_from k Σ2).
Proof.
Admitted.

Lemma lty_env_agree_on_lvars_shift_insert_bound D Σ1 Σ2 T :
  lty_env_agree_on_lvars D Σ1 Σ2 ->
  lty_env_agree_on_lvars (lvars_shift_from 0 D ∪ {[LVBound 0]})
    (<[LVBound 0 := T]> (lty_env_shift Σ1))
    (<[LVBound 0 := T]> (lty_env_shift Σ2)).
Proof.
Admitted.

Lemma lty_env_atom_dom_insert_bound Σ k T :
  lty_env_atom_dom (<[LVBound k := T]> Σ) = lty_env_atom_dom Σ.
Proof.
Admitted.

Lemma lty_env_shift_insert_from k v T Σ :
  lty_env_shift_from k (<[v := T]> Σ) =
  <[logic_var_shift_from k v := T]> (lty_env_shift_from k Σ).
Proof.
Admitted.

Lemma lty_env_shift_insert v T Σ :
  lty_env_shift (<[v := T]> Σ) =
  <[logic_var_shift_from 0 v := T]> (lty_env_shift Σ).
Proof.
Admitted.

Lemma lty_env_shift_insert_free x T Σ :
  lty_env_shift (<[LVFree x := T]> Σ) =
  <[LVFree x := T]> (lty_env_shift Σ).
Proof.
Admitted.

Lemma lty_env_open_lvars_shift_from k η Σ :
  open_env_fresh_for_lvars η (dom Σ) ->
  lty_env_open_lvars (open_env_shift_from k η)
    (lty_env_shift_from k Σ) =
  lty_env_shift_from k (lty_env_open_lvars η Σ).
Proof.
Admitted.

Lemma logic_var_open_inj_fresh k x v1 v2 :
  logic_var_open k x v1 = logic_var_open k x v2 ->
  v1 = v2.
Proof.
Admitted.

Lemma logic_var_open_inj_on k x (D : lvset) :
  Inj (=) (=) (logic_var_open k x).
Proof.
Admitted.

Lemma lty_env_shift_free_notin_from k x Σ :
  LVFree x ∉ dom Σ ->
  LVFree x ∉ dom (lty_env_shift_from k Σ).
Proof.
Admitted.

Lemma lty_env_shift_free_notin x Σ :
  LVFree x ∉ dom Σ ->
  LVFree x ∉ dom (lty_env_shift Σ).
Proof.
Admitted.

Lemma lty_env_shift_insert_free_notin x v T Σ :
  LVFree x ∉ dom Σ ->
  LVFree x ∉ dom (lty_env_shift (<[v := T]> Σ)) ->
  x ∉ lty_env_atom_dom Σ.
Proof.
Admitted.

Lemma lty_env_open_one_dom k x Σ :
  dom (lty_env_open_one k x Σ) = lvars_open k x (dom Σ).
Proof.
Admitted.

Lemma lty_env_open_lvars_empty Σ :
  lty_env_open_lvars ∅ Σ = Σ.
Proof.
Admitted.

Lemma lty_env_open_lvars_singleton k x Σ :
  LVFree x ∉ dom Σ ->
  lty_env_open_lvars (<[k := x]> ∅) Σ =
  lty_env_open_one k x Σ.
Proof.
Admitted.

Lemma lty_env_open_lvars_open_one_empty k x Σ :
  LVFree x ∉ dom Σ ->
  lty_env_open_lvars ∅ (lty_env_open_one k x Σ) =
  lty_env_open_lvars (<[k := x]> ∅) Σ.
Proof.
Admitted.

Lemma lty_env_open_lvars_dom η Σ :
  open_env_fresh_for_lvars η (dom Σ) ->
  dom (lty_env_open_lvars η Σ) =
  lvars_open_env_simul η (dom Σ).
Proof.
Admitted.

Lemma lty_env_open_lvars_lookup_fresh η v T Σ :
  Σ !! v = None ->
  open_env_fresh_for_lvars η (dom (<[v := T]> Σ)) ->
  lty_env_open_lvars η Σ !! logic_var_open_env η v = None.
Proof.
Admitted.

Lemma lty_env_open_lvars_insert_entry η v T Σ :
  Σ !! v = None ->
  logic_var_open_env_inj_on η (dom (<[v := T]> Σ)) ->
  lty_env_open_lvars η (<[v := T]> Σ) =
  <[logic_var_open_env η v := T]> (lty_env_open_lvars η Σ).
Proof.
Admitted.

Lemma lty_env_open_lvars_insert_fresh η k x Σ :
  η !! k = None ->
  open_env_avoids_atom x η ->
  open_env_fresh_for_lvars (<[k := x]> η) (dom Σ) ->
  lty_env_open_lvars (<[k := x]> η) Σ =
  lty_env_open_one k x (lty_env_open_lvars η Σ).
Proof.
Admitted.

Lemma logic_var_bv_elem_singleton v k :
  k ∈ lvars_bv ({[v]} : lvset) <-> v = LVBound k.
Proof.
Admitted.

Lemma logic_var_open_fresh_noop k x v :
  LVBound k <> v ->
  LVFree x <> v ->
  logic_var_open k x v = v.
Proof.
Admitted.

Lemma lty_env_open_one_fresh_noop k x Σ :
  LVBound k ∉ dom Σ ->
  LVFree x ∉ dom Σ ->
  lty_env_open_one k x Σ = Σ.
Proof.
Admitted.

Lemma lty_env_open_one_involutive k x Σ :
  lty_env_open_one k x (lty_env_open_one k x Σ) = Σ.
Proof.
Admitted.

Lemma lty_env_open_one_insert k x v T Σ :
  lty_env_open_one k x (<[v := T]> Σ) =
  <[logic_var_open k x v := T]> (lty_env_open_one k x Σ).
Proof.
Admitted.

Lemma lty_env_open_one_insert_fresh k x v T Σ :
  logic_var_open k x v ∉ dom (lty_env_open_one k x Σ) ->
  lty_env_open_one k x (<[v := T]> Σ) =
  <[logic_var_open k x v := T]> (lty_env_open_one k x Σ).
Proof.
Admitted.

Lemma lty_env_open_one_shift_under j k x Σ :
  j <= k ->
  lty_env_open_one (S (S k)) x (lty_env_shift_from (S j) Σ) =
  lty_env_shift_from (S j) (lty_env_open_one (S k) x Σ).
Proof.
Admitted.

Lemma lvars_open_shift_dom j k x (Σ : lty_env) :
  j <= k ->
  lvars_open (S (S k)) x (lvars_shift_from (S j) (dom Σ)) =
  lvars_shift_from (S j) (lvars_open (S k) x (dom Σ)).
Proof.
Admitted.

Lemma lty_env_open_one_shift_insert_bound k x T Σ :
  lty_env_open_one (S k) x (lty_env_shift (<[LVBound k := T]> Σ)) =
  lty_env_shift (lty_env_open_one k x (<[LVBound k := T]> Σ)).
Proof.
Admitted.

Lemma lvars_bv_of_bvars (B : gset nat) :
  lvars_bv (lvars_of_bvars B) = B.
Proof.
Admitted.

Lemma lvars_bv_shift_from D k :
  lvars_bv (lvars_shift_from k D) =
  set_map (fun n => if decide (k <= n) then S n else n) (lvars_bv D).
Proof.
Admitted.

Lemma lty_env_bvar_scope_shift_open_noop k x Σ :
  LVBound k ∉ lty_env_bvar_scope (lty_env_shift Σ) ->
  lvars_open k x (lty_env_bvar_scope (lty_env_shift Σ)) =
  lty_env_bvar_scope (lty_env_shift Σ).
Proof.
Admitted.

Lemma lty_env_bvar_scope_shift_open_one_noop k x Σ :
  LVBound k ∉ lty_env_bvar_scope (lty_env_shift Σ) ->
  lty_env_bvar_scope (lty_env_open_one k x (lty_env_shift Σ)) =
  lty_env_bvar_scope (lty_env_shift Σ).
Proof.
Admitted.

Lemma lty_env_bvar_scope_open_one_shift_under_result k x Σ :
  LVBound (S k) ∉ lty_env_bvar_scope (lty_env_shift Σ) ->
  lty_env_bvar_scope (lty_env_open_one (S k) x (lty_env_shift Σ)) =
  lty_env_bvar_scope (lty_env_shift Σ).
Proof.
Admitted.

Lemma lvars_open_shift_union_bound0 k x D :
  lvars_open (S k) x (lvars_shift_from 0 D ∪ {[LVBound 0]}) =
  lvars_shift_from 0 (lvars_open k x D) ∪ {[LVBound 0]}.
Proof.
Admitted.

Lemma lvars_open_shift_dom_union_bound0 k x (Σ : lty_env) :
  lvars_open (S k) x (lvars_shift_from 0 (dom Σ) ∪ {[LVBound 0]}) =
  lvars_shift_from 0 (lvars_open k x (dom Σ)) ∪ {[LVBound 0]}.
Proof.
Admitted.

Lemma lty_env_atom_dom_open_one k x Σ :
  lty_env_atom_dom (lty_env_open_one k x Σ) ⊆ lty_env_atom_dom Σ ∪ {[x]}.
Proof.
Admitted.

Lemma atom_env_to_lty_env_dom Σ :
  dom (atom_env_to_lty_env Σ) = lvars_of_atoms (dom Σ).
Proof.
Admitted.

Lemma atom_env_to_lty_env_insert x T Σ :
  atom_env_to_lty_env (<[x := T]> Σ) =
  <[LVFree x := T]> (atom_env_to_lty_env Σ).
Proof.
Admitted.

Lemma atom_env_to_lty_env_closed Σ :
  lty_env_closed (atom_env_to_lty_env Σ).
Proof.
Admitted.

Lemma atom_env_to_lty_env_atom_dom Σ :
  lty_env_atom_dom (atom_env_to_lty_env Σ) = dom Σ.
Proof.
Admitted.

Lemma atom_env_to_lty_env_lookup_bound_none Σ k :
  atom_env_to_lty_env Σ !! LVBound k = None.
Proof.
Admitted.

Lemma atom_env_to_lty_env_lookup_free_none Δ x :
  x ∉ dom Δ ->
  atom_env_to_lty_env Δ !! LVFree x = None.
Proof.
Admitted.

Lemma atom_env_to_lty_env_lookup_free Δ x :
  atom_env_to_lty_env Δ !! LVFree x = Δ !! x.
Proof.
Admitted.

Lemma lty_env_shift_atom_env Σ :
  lty_env_shift (atom_env_to_lty_env Σ) = atom_env_to_lty_env Σ.
Proof.
Admitted.

Lemma logic_var_swap_inj x y :
  Inj (=) (=)
    (fun v =>
      match v with
      | LVFree z => LVFree (atom_swap x y z)
      | LVBound k => LVBound k
      end).
Proof.
Admitted.

Lemma lty_env_swap_lookup x y Σ v :
  lty_env_swap x y Σ !! (match v with
                         | LVFree z => LVFree (atom_swap x y z)
                         | LVBound k => LVBound k
                         end) = Σ !! v.
Proof.
Admitted.

Lemma lty_env_swap_lookup_inv x y Σ v :
  lty_env_swap x y Σ !! v =
  Σ !! (match v with
        | LVFree z => LVFree (atom_swap x y z)
        | LVBound k => LVBound k
        end).
Proof.
Admitted.

Lemma lty_env_swap_insert x y Σ v T :
  lty_env_swap x y (<[v := T]> Σ) =
  <[match v with
     | LVFree z => LVFree (atom_swap x y z)
     | LVBound k => LVBound k
     end := T]> (lty_env_swap x y Σ).
Proof.
Admitted.

Lemma lty_env_swap_atom_dom x y Σ :
  lty_env_atom_dom (lty_env_swap x y Σ) =
  aset_swap x y (lty_env_atom_dom Σ).
Proof.
Admitted.

Lemma lty_env_swap_fresh x y Σ :
  x ∉ lty_env_atom_dom Σ ->
  y ∉ lty_env_atom_dom Σ ->
  lty_env_swap x y Σ = Σ.
Proof.
Admitted.

Lemma lty_env_swap_atom_env_fresh Δ x y :
  x ∉ dom Δ ->
  y ∉ dom Δ ->
  lty_env_swap x y (atom_env_to_lty_env Δ) = atom_env_to_lty_env Δ.
Proof.
Admitted.

Lemma lty_env_swap_atom_env_insert_fresh Δ x y T :
  x ∉ dom Δ ->
  lty_env_swap x y (<[LVFree x := T]> (atom_env_to_lty_env Δ)) =
  <[LVFree y := T]> (atom_env_to_lty_env Δ).
Proof.
Admitted.

Lemma lty_env_open_atom_env η Σ :
  lty_env_open η (atom_env_to_lty_env Σ) = Σ.
Proof.
Admitted.

Lemma lty_env_open_one_atom_env k x Σ :
  x ∉ dom Σ ->
  lty_env_open_one k x (atom_env_to_lty_env Σ) =
  atom_env_to_lty_env Σ.
Proof.
Admitted.

Lemma lty_env_open_one_bind_atom_env x T Σ :
  x ∉ dom Σ ->
  lty_env_open_one 0 x (<[LVBound 0 := T]> (lty_env_shift (atom_env_to_lty_env Σ))) =
  <[LVFree x := T]> (atom_env_to_lty_env Σ).
Proof.
Admitted.

Lemma lty_env_bind_atom_env_dom T Σ :
  dom (<[LVBound 0 := T]> (lty_env_shift (atom_env_to_lty_env Σ))) =
  lvars_shift_from 0 (lvars_of_atoms (dom Σ)) ∪ {[LVBound 0]}.
Proof.
Admitted.

Lemma lty_env_open_insert_bound_atom_env k x T η Σ :
  η !! k = None ->
  open_env_avoids_atom x η ->
  LVFree x ∉ dom Σ ->
  lty_env_open (<[k := x]> η) (<[LVBound k := T]> Σ) =
  <[x := T]> (lty_env_open η Σ).
Proof.
Admitted.

Lemma typed_lty_env_bind_dom Σ T :
  dom (typed_lty_env_bind Σ T) =
  lvars_shift_from 0 (dom Σ) ∪ {[LVBound 0]}.
Proof.
Admitted.

Lemma typed_lty_env_bind_atom_env_insert_dom
    (Δ : gmap atom ty) x Tx Ty :
  x ∉ dom Δ ->
  dom (typed_lty_env_bind (atom_env_to_lty_env (<[x := Tx]> Δ)) Ty) =
  dom (typed_lty_env_bind (atom_env_to_lty_env Δ) Ty) ∪
  {[LVFree x]}.
Proof.
Admitted.

Lemma typed_lty_env_bind_lvars_fv_dom Σ T :
  lvars_fv (dom (typed_lty_env_bind Σ T)) = lvars_fv (dom Σ).
Proof.
Admitted.

Lemma typed_lty_env_bind_atom_dom Σ T :
  lty_env_atom_dom (typed_lty_env_bind Σ T) = lty_env_atom_dom Σ.
Proof.
Admitted.

Lemma typed_lty_env_bind_free_notin x Σ T :
  LVFree x ∉ dom Σ ->
  LVFree x ∉ dom (typed_lty_env_bind Σ T).
Proof.
Admitted.

Lemma typed_lty_env_bind_open_under k x Σ T :
  LVFree x ∉ dom Σ ->
  lty_env_open_one (S k) x (typed_lty_env_bind Σ T) =
  typed_lty_env_bind (lty_env_open_one k x Σ) T.
Proof.
Admitted.

Lemma lty_env_open_typed_bind_atom_env (Δ : gmap atom ty) T x :
  x ∉ dom Δ ->
  lty_env_open_one 0 x
    (typed_lty_env_bind (atom_env_to_lty_env Δ) T) =
  atom_env_to_lty_env (<[x := T]> Δ).
Proof.
Admitted.

Lemma typed_lty_env_bind_open_env_shift0 η Σ T :
  open_env_fresh_for_lvars η (dom Σ) ->
  lty_env_open_lvars (open_env_shift_from 0 η) (typed_lty_env_bind Σ T) =
  typed_lty_env_bind (lty_env_open_lvars η Σ) T.
Proof.
Admitted.

Lemma typed_lty_env_bind_open_env_lift η Σ T :
  open_env_fresh_for_lvars η (dom Σ) ->
  lty_env_open_lvars (open_env_lift η) (typed_lty_env_bind Σ T) =
  typed_lty_env_bind (lty_env_open_lvars η Σ) T.
Proof.
Admitted.
