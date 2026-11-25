(** Federer (1969), 4.1.1, pp. 344–345: the private weak
    topology witness has pointwise convergence. Existing initial
    and product convergence theorems prove the independent law;
    no sequence-convergence assertion is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormOpenTopology OpenFamilyConvergence
  DaniellSpaceWeakTopology WeakEvaluationTopologyUP WeakEvaluationConvergenceUP
  WeakEvaluationTopologyExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Section WeakTopologyConvergence.
Variable R:realType.
Variables E D:choiceType.
Variable ev:D->E->R.
Local Notation S := (real_norm_metric_space (@scalar_absolute_value_norm R)).
Local Notation P := (prod_topology (fun _:E=>[the topologicalType of S])).
Local Notation W := (initial_topology (ev:D->P)).

(** Source for [weak_evaluation_open_witness_convergence]: the
    exact pointwise convergence law for the weak topology of
    Federer 4.1.1, pp. 344–345, including arbitrary proper or
    improper filters and all evaluation index sets. *)
Theorem weak_evaluation_open_witness_convergence:
  is_weak_evaluation_convergence ev (weak_evaluation_open_witness ev).
Proof.
move=>F hF d.
have hInit:=@initial_topology_cvg D [the topologicalType of P] ev F d hF.
have hEF:Filter (ev @ F):=fmap_filter ev hF.
have hProd:=@product_topology_cvg E (fun _:E=>[the topologicalType of S])
  (ev @ F) (ev d) hEF.
split.
- move=>hc e.
  have hCvg: F --> (d:W):=
    (@open_family_topological_convergence [the topologicalType of W] F d hF).1 hc.
  have he:=hProd.1 (hInit.1 hCvg) e.
  have hCF:Filter ((fun x:D=>ev x e) @ F):=fmap_filter _ hF.
  exact:(@open_family_topological_convergence [the topologicalType of S]
    ((fun x:D=>ev x e) @ F) (ev d e) hCF).2 he.
- move=>hc.
  have hEval:ev @ F --> (ev d:P).
    apply:hProd.2=>e.
    have hCF:Filter ((fun x:D=>ev x e) @ F):=fmap_filter _ hF.
    exact:(@open_family_topological_convergence [the topologicalType of S]
      ((fun x:D=>ev x e) @ F) (ev d e) hCF).1 (hc e).
  exact:(@open_family_topological_convergence [the topologicalType of W] F d hF).2
    (hInit.2 hEval).
Qed.

(** Source for [weak_evaluation_topology_with_convergence_exists]:
    the same topology satisfies its independent mapping and
    convergence characterizations, supporting Federer 4.1.1,
    pp. 344–345. This joint witness is used only by the seal. *)
Theorem weak_evaluation_topology_with_convergence_exists:
  exists O,is_weak_evaluation_topology ev O /\ is_weak_evaluation_convergence ev O.
Proof.
exists (weak_evaluation_open_witness ev); split.
- exact:weak_evaluation_open_witness_laws.
- exact:weak_evaluation_open_witness_convergence.
Qed.
End WeakTopologyConvergence.
