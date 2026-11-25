(** Federer (1969), 4.1.1, pp. 344–345: existence of the
    weak topology. The witness uses only the general-topology
    product and initial topology, and reuses the project's
    coordinatewise product continuity theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormOpenTopology OpenFamilyTopologyUP
  OpenFamilyTopologyMathcomp DependentProductContinuity WeakEvaluationTopologyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Section WeakTopologyWitness.
Variable R:realType.
Variables E D:choiceType.
Variable ev:D->E->R.
Local Notation S := (real_norm_metric_space (@scalar_absolute_value_norm R)).
Local Notation P := (prod_topology (fun _:E=>[the topologicalType of S])).
Local Notation W := (initial_topology (ev:D->P)).

(** Source for [weak_evaluation_open_witness]: private product
    witness for the real-evaluation topology, supporting Federer
    4.1.1, pp. 344–345. *)
Definition weak_evaluation_open_witness:set (set D):=
  fun A=>@open [the topologicalType of W] A.

(** Source for [weak_evaluation_open_witness_laws]: the original
    weak topology exists with the independent real-evaluation
    universal property, Federer 4.1.1, pp. 344–345. *)
Theorem weak_evaluation_open_witness_laws:
  is_weak_evaluation_topology ev weak_evaluation_open_witness.
Proof.
split.
- constructor.
  + exact:(@openT W).
  + move=>A B; exact:(@openI W A B).
  + move=>I A hA; apply:bigcup_open=>i _; exact:hA i.
- move=>Z Q hQ f; split.
  + move=>hf e.
    have hf':continuous (fun z:open_family_topological_space hQ=>(f z:W)).
      by apply/continuousP; exact:hf.
    have hev:continuous (ev:W->P):=@initial_continuous D [the topologicalType of P] ev.
    have he:continuous (fun t:P=>(t e:S)):=
      @proj_continuous E (fun _:E=>[the topologicalType of S]) e.
    have hc:continuous (fun z:open_family_topological_space hQ=>(ev (f z) e:S)).
      move=>z.
      have hProduct:=@continuous_comp
        [the topologicalType of open_family_topological_space hQ]
        [the topologicalType of W] [the topologicalType of P]
        (fun z=>f z) ev z (hf' z) (hev (f z)).
      exact:(@continuous_comp
        [the topologicalType of open_family_topological_space hQ]
        [the topologicalType of P] [the topologicalType of S]
        (fun z=>ev (f z)) (fun t=>t e) z hProduct (he (ev (f z)))).
    move/continuousP:hc; exact.
  + move=>hf.
    have hc:continuous (fun z:open_family_topological_space hQ=>(f z:W)).
      apply:continuous_comp_initial.
      apply:dependent_product_map_continuous=>e.
      apply/continuousP; exact:hf e.
    move/continuousP:hc; exact.
Qed.

(** Source for [weak_evaluation_topology_exists]: existence of
    the independently specified weak topology, Federer 4.1.1,
    pp. 344–345. The witness laws are proved above. *)
Theorem weak_evaluation_topology_exists:
  exists O,is_weak_evaluation_topology ev O.
Proof. exists weak_evaluation_open_witness; exact:weak_evaluation_open_witness_laws. Qed.
End WeakTopologyWitness.
