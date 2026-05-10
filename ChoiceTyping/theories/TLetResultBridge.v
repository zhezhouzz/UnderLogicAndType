(** * ChoiceTyping.TLetResultBridge

    The high-risk expression-result bridge for [tlet].

    This file is intentionally placed after both [ResultWorldBridge] and
    [TLetGraph].  The general result-world facts do not depend on the
    proof-only tlet graph, while the tlet bridge does: its job is to show that
    the graph preserves the exact [X -> x -> ν] pairing needed by the body
    proof and by the whole-let result atom. *)

From CoreLang Require Import Instantiation InstantiationProps OperationalProps
  LocallyNamelessProps.
From ChoiceTyping Require Export ResultWorldBridge.
From ChoiceTyping Require Import TLetGraph.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

(** High-risk tlet expression-result bridge.

    This is the resource-level version of the operational identity
    [Results(let x = e1 in e2) = Results(e2[x := Results(e1)])].
    It is intentionally phrased as an [expr_result_model_bridge], so later type
    denotation transport can stay generic in [τ].

    Anti-slip rule: this proof must stay expression/resource-level.  It should
    use the tlet graph and exact expression-result worlds, but it must not
    inspect the final choice type or split into [CTOver]/[CTUnder] cases. *)
Lemma expr_result_model_bridge_tlete
    X e1 e2 x (m : WfWorld) Hfresh Hresult :
  x ∉ X ∪ fv_tm e2 →
  fv_tm (tlete e1 e2) ⊆ X →
  X ⊆ world_dom (m : World) →
  world_store_closed_on X m →
  lc_tm (tlete e1 e2) →
  (∀ n,
    m ⊑ n →
    X ⊆ world_dom (n : World) →
    (∀ σ, (n : World) σ →
      ∃ vx, subst_map (store_restrict σ X) e1 →* tret vx) →
    ∀ Hfreshn Hresultn,
      expr_total_on (X ∪ {[x]}) (e2 ^^ x)
        (let_result_world_on X e1 x n Hfreshn Hresultn)) →
  expr_result_model_bridge
    (X ∪ {[x]}) (e2 ^^ x)
    X (tlete e1 e2)
    (let_result_world_on X e1 x m Hfresh Hresult)
    m.
Proof.
Admitted.

