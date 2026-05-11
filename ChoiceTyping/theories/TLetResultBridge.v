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
From ChoiceTyping Require Import ResultWorldFreshForall.
From ChoiceTyping Require Import TLetGraph.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

Lemma nested_tlet_result_world_source_transport
    X e1 e2 x ν (m ntgt : WfWorld)
    Hfresh_m Hresult_m Hfreshx_ntgtX Hresult_ntgtX Hfreshν Hresult_body :
  X ⊆ world_dom (m : World) →
  m ⊑ ntgt →
  x ∉ X →
  ν ∉ X ∪ {[x]} →
  model_transport_on (X ∪ {[x]})
    (let_result_world_on e1 x m Hfresh_m Hresult_m)
    (let_result_world_on (e2 ^^ x) ν
      (let_result_world_on e1 x (res_restrict ntgt X)
        Hfreshx_ntgtX Hresult_ntgtX)
      Hfreshν Hresult_body).
Proof.
Admitted.

Lemma nested_tlet_result_world_target_transport
    X e1 e2 x ν (ntgt : WfWorld)
    Hfreshx Hresult1 Hfreshν Hresult2 :
  x ∉ X ∪ fv_tm e2 ∪ {[ν]} →
  fv_tm (tlete e1 e2) ⊆ X →
  ν ∉ X →
  X ⊆ world_dom (ntgt : World) →
  world_store_closed_on X ntgt →
  lc_tm (tlete e1 e2) →
  ntgt ⊨ FExprResult (tlete e1 e2) ν →
  model_transport_on (X ∪ {[ν]})
    (let_result_world_on (e2 ^^ x) ν
      (let_result_world_on e1 x (res_restrict ntgt X) Hfreshx Hresult1)
      Hfreshν Hresult2)
    ntgt.
Proof.
Admitted.

Lemma nested_body_result_world_models_FExprResult X e1 e2 x ν (ntgt : WfWorld)
    Hfreshx Hresult1 Hfreshν Hresult2 :
  x ∉ X ∪ fv_tm e2 →
  fv_tm (tlete e1 e2) ⊆ X →
  ν ∉ X ∪ {[x]} →
  X ⊆ world_dom (ntgt : World) →
  world_store_closed_on X ntgt →
  lc_tm (tlete e1 e2) →
  let_result_world_on (e2 ^^ x) ν
    (let_result_world_on e1 x (res_restrict ntgt X) Hfreshx Hresult1)
    Hfreshν Hresult2
    ⊨ FExprResult (e2 ^^ x) ν.
Proof.
Admitted.

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
        (let_result_world_on e1 x n Hfreshn Hresultn)) →
  expr_result_model_bridge
    (X ∪ {[x]}) (e2 ^^ x)
    X (tlete e1 e2)
    (let_result_world_on e1 x m Hfresh Hresult)
    m.
Proof.
Admitted.
