From ContextLogic Require Export FormulaSyntax.
From ContextLogic Require Import FormulaSyntaxTactics.

(** * Context Logic semantics

    The semantic judgment no longer carries an explicit store environment.
    Formula scope is simply a subset check against the current atom-world
    domain.  Universal quantification is phrased directly with resource
    extensions whose input is the free-variable footprint of the body. *)

Section Formula.

Context {V : Type} `{ValueSig V}.

Local Notation WorldT := (World (V := V)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation FormulaT := (Formula (V := V)) (only parsing).

Definition formula_scoped_in_world
    (m : WfWorldT) (φ : FormulaT) : Prop :=
  formula_fv φ ⊆ world_dom (m : WorldT).

Lemma formula_scoped_res_subset
    (m m' : WfWorldT) (φ : FormulaT) :
  formula_scoped_in_world m φ →
  res_subset m m' →
  formula_scoped_in_world m' φ.
Proof.
  unfold formula_scoped_in_world.
  intros Hscope [Hdom _].
  unfold world_dom in *.
  change (formula_fv φ ⊆ ResourceCore.worldA_dom (m : WorldT)) in Hscope.
  change (formula_fv φ ⊆ ResourceCore.worldA_dom (m' : WorldT)).
  change (ResourceCore.worldA_dom (m : WorldT) =
          ResourceCore.worldA_dom (m' : WorldT)) in Hdom.
  rewrite Hdom in Hscope. exact Hscope.
Qed.

Lemma formula_scoped_world_dom_eq
    (m m' : WfWorldT) (φ : FormulaT) :
  world_dom (m : WorldT) = world_dom (m' : WorldT) →
  formula_scoped_in_world m φ →
  formula_scoped_in_world m' φ.
Proof.
  unfold formula_scoped_in_world. intros Hdom Hscope. rewrite <- Hdom.
  exact Hscope.
Qed.

Lemma formula_scoped_true_iff (m : WfWorldT) :
  formula_scoped_in_world m FTrue ↔ True.
Proof.
  unfold formula_scoped_in_world. formula_fv_syntax_norm.
  split; [trivial | intros _ z Hz; rewrite lvars_fv_elem in Hz; set_solver].
Qed.

Lemma formula_scoped_false_iff (m : WfWorldT) :
  formula_scoped_in_world m FFalse ↔ True.
Proof.
  unfold formula_scoped_in_world. formula_fv_syntax_norm.
  split; [trivial | intros _ z Hz; rewrite lvars_fv_elem in Hz; set_solver].
Qed.

Lemma formula_scoped_atom_iff (m : WfWorldT) q :
  formula_scoped_in_world m (FAtom q) ↔ lqual_fv q ⊆ world_dom (m : WorldT).
Proof. reflexivity. Qed.

Lemma formula_scoped_and_iff (m : WfWorldT) φ ψ :
  formula_scoped_in_world m (FAnd φ ψ) ↔
  formula_scoped_in_world m φ ∧ formula_scoped_in_world m ψ.
Proof.
  unfold formula_scoped_in_world. formula_fv_syntax_norm. set_solver.
Qed.

Lemma formula_scoped_and_l (m : WfWorldT) φ ψ :
  formula_scoped_in_world m (FAnd φ ψ) ->
  formula_scoped_in_world m φ.
Proof. intros Hscope. apply (proj1 (formula_scoped_and_iff m φ ψ)) in Hscope. tauto. Qed.

Lemma formula_scoped_and_r (m : WfWorldT) φ ψ :
  formula_scoped_in_world m (FAnd φ ψ) ->
  formula_scoped_in_world m ψ.
Proof. intros Hscope. apply (proj1 (formula_scoped_and_iff m φ ψ)) in Hscope. tauto. Qed.

Lemma formula_scoped_or_iff (m : WfWorldT) φ ψ :
  formula_scoped_in_world m (FOr φ ψ) ↔
  formula_scoped_in_world m φ ∧ formula_scoped_in_world m ψ.
Proof.
  unfold formula_scoped_in_world. formula_fv_syntax_norm. set_solver.
Qed.

Lemma formula_scoped_or_l (m : WfWorldT) φ ψ :
  formula_scoped_in_world m (FOr φ ψ) ->
  formula_scoped_in_world m φ.
Proof. intros Hscope. apply (proj1 (formula_scoped_or_iff m φ ψ)) in Hscope. tauto. Qed.

Lemma formula_scoped_or_r (m : WfWorldT) φ ψ :
  formula_scoped_in_world m (FOr φ ψ) ->
  formula_scoped_in_world m ψ.
Proof. intros Hscope. apply (proj1 (formula_scoped_or_iff m φ ψ)) in Hscope. tauto. Qed.

Lemma formula_scoped_impl_iff (m : WfWorldT) φ ψ :
  formula_scoped_in_world m (FImpl φ ψ) ↔
  formula_scoped_in_world m φ ∧ formula_scoped_in_world m ψ.
Proof.
  unfold formula_scoped_in_world. formula_fv_syntax_norm. set_solver.
Qed.

Lemma formula_scoped_impl_l (m : WfWorldT) φ ψ :
  formula_scoped_in_world m (FImpl φ ψ) ->
  formula_scoped_in_world m φ.
Proof. intros Hscope. apply (proj1 (formula_scoped_impl_iff m φ ψ)) in Hscope. tauto. Qed.

Lemma formula_scoped_impl_r (m : WfWorldT) φ ψ :
  formula_scoped_in_world m (FImpl φ ψ) ->
  formula_scoped_in_world m ψ.
Proof. intros Hscope. apply (proj1 (formula_scoped_impl_iff m φ ψ)) in Hscope. tauto. Qed.

Lemma formula_scoped_star_iff (m : WfWorldT) φ ψ :
  formula_scoped_in_world m (FStar φ ψ) ↔
  formula_scoped_in_world m φ ∧ formula_scoped_in_world m ψ.
Proof.
  unfold formula_scoped_in_world. formula_fv_syntax_norm. set_solver.
Qed.

Lemma formula_scoped_star_l (m : WfWorldT) φ ψ :
  formula_scoped_in_world m (FStar φ ψ) ->
  formula_scoped_in_world m φ.
Proof. intros Hscope. apply (proj1 (formula_scoped_star_iff m φ ψ)) in Hscope. tauto. Qed.

Lemma formula_scoped_star_r (m : WfWorldT) φ ψ :
  formula_scoped_in_world m (FStar φ ψ) ->
  formula_scoped_in_world m ψ.
Proof. intros Hscope. apply (proj1 (formula_scoped_star_iff m φ ψ)) in Hscope. tauto. Qed.

Lemma formula_scoped_wand_iff (m : WfWorldT) φ ψ :
  formula_scoped_in_world m (FWand φ ψ) ↔
  formula_scoped_in_world m φ ∧ formula_scoped_in_world m ψ.
Proof.
  unfold formula_scoped_in_world. formula_fv_syntax_norm. set_solver.
Qed.

Lemma formula_scoped_wand_l (m : WfWorldT) φ ψ :
  formula_scoped_in_world m (FWand φ ψ) ->
  formula_scoped_in_world m φ.
Proof. intros Hscope. apply (proj1 (formula_scoped_wand_iff m φ ψ)) in Hscope. tauto. Qed.

Lemma formula_scoped_wand_r (m : WfWorldT) φ ψ :
  formula_scoped_in_world m (FWand φ ψ) ->
  formula_scoped_in_world m ψ.
Proof. intros Hscope. apply (proj1 (formula_scoped_wand_iff m φ ψ)) in Hscope. tauto. Qed.

Lemma formula_scoped_plus_iff (m : WfWorldT) φ ψ :
  formula_scoped_in_world m (FPlus φ ψ) ↔
  formula_scoped_in_world m φ ∧ formula_scoped_in_world m ψ.
Proof.
  unfold formula_scoped_in_world. formula_fv_syntax_norm. set_solver.
Qed.

Lemma formula_scoped_plus_l (m : WfWorldT) φ ψ :
  formula_scoped_in_world m (FPlus φ ψ) ->
  formula_scoped_in_world m φ.
Proof. intros Hscope. apply (proj1 (formula_scoped_plus_iff m φ ψ)) in Hscope. tauto. Qed.

Lemma formula_scoped_plus_r (m : WfWorldT) φ ψ :
  formula_scoped_in_world m (FPlus φ ψ) ->
  formula_scoped_in_world m ψ.
Proof. intros Hscope. apply (proj1 (formula_scoped_plus_iff m φ ψ)) in Hscope. tauto. Qed.

Lemma formula_scoped_forall_iff (m : WfWorldT) φ :
  formula_scoped_in_world m (FForall φ) ↔
  formula_scoped_in_world m φ.
Proof. reflexivity. Qed.

Lemma formula_scoped_forall_body (m : WfWorldT) φ :
  formula_scoped_in_world m (FForall φ) ->
  formula_scoped_in_world m φ.
Proof. intros Hscope. apply (proj1 (formula_scoped_forall_iff m φ)); exact Hscope. Qed.

Lemma formula_scoped_over_iff (m : WfWorldT) φ :
  formula_scoped_in_world m (FOver φ) ↔
  formula_scoped_in_world m φ.
Proof. reflexivity. Qed.

Lemma formula_scoped_over_body (m : WfWorldT) φ :
  formula_scoped_in_world m (FOver φ) ->
  formula_scoped_in_world m φ.
Proof. intros Hscope. apply (proj1 (formula_scoped_over_iff m φ)); exact Hscope. Qed.

Lemma formula_scoped_under_iff (m : WfWorldT) φ :
  formula_scoped_in_world m (FUnder φ) ↔
  formula_scoped_in_world m φ.
Proof. reflexivity. Qed.

Lemma formula_scoped_under_body (m : WfWorldT) φ :
  formula_scoped_in_world m (FUnder φ) ->
  formula_scoped_in_world m φ.
Proof. intros Hscope. apply (proj1 (formula_scoped_under_iff m φ)); exact Hscope. Qed.

Lemma formula_scoped_fibvars_iff (m : WfWorldT) D φ :
  formula_scoped_in_world m (FFibVars D φ) ↔
  lvars_fv D ⊆ world_dom (m : WorldT) ∧ formula_scoped_in_world m φ.
Proof.
  unfold formula_scoped_in_world. formula_fv_syntax_norm. set_solver.
Qed.

Lemma formula_scoped_fibvars_l (m : WfWorldT) D φ :
  formula_scoped_in_world m (FFibVars D φ) ->
  lvars_fv D ⊆ world_dom (m : WorldT).
Proof. intros Hscope. apply (proj1 (formula_scoped_fibvars_iff m D φ)) in Hscope. tauto. Qed.

Lemma formula_scoped_fibvars_r (m : WfWorldT) D φ :
  formula_scoped_in_world m (FFibVars D φ) ->
  formula_scoped_in_world m φ.
Proof. intros Hscope. apply (proj1 (formula_scoped_fibvars_iff m D φ)) in Hscope. tauto. Qed.

Lemma formula_scoped_open_from_fv
    (m : WfWorldT) k x φ :
  formula_fv φ ∪ {[x]} ⊆ world_dom (m : WorldT) →
  formula_scoped_in_world m (formula_open k x φ).
Proof.
  unfold formula_scoped_in_world.
  intros Hscope.
  pose proof (formula_open_fv_subset k x φ) as Hopen.
  set_solver.
Qed.

Lemma formula_scoped_open
    (m : WfWorldT) k x φ :
  formula_scoped_in_world m φ →
  x ∈ world_dom (m : WorldT) →
  formula_scoped_in_world m (formula_open k x φ).
Proof.
  unfold formula_scoped_in_world.
  intros Hscope Hx.
  pose proof (formula_open_fv_subset k x φ) as Hopen.
  set_solver.
Qed.

Lemma formula_scoped_from_fv_subset
    (m : WfWorldT) (φ : FormulaT) (S : aset) :
  S ⊆ world_dom (m : WorldT) →
  formula_fv φ ⊆ S →
  formula_scoped_in_world m φ.
Proof.
  unfold formula_scoped_in_world. set_solver.
Qed.

Lemma formula_scoped_open_res_le
    (m n : WfWorldT) k x φ :
  formula_scoped_in_world m φ →
  m ⊑ n →
  x ∈ world_dom (n : WorldT) →
  formula_scoped_in_world n (formula_open k x φ).
Proof.
  unfold formula_scoped_in_world.
  intros Hscope Hle Hx.
  pose proof (raw_le_dom _ _ Hle) as Hdom.
  pose proof (formula_open_fv_subset k x φ) as Hopen.
  set_solver.
Qed.

End Formula.
