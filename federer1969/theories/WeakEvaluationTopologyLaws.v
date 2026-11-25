(** Federer (1969), 4.1.1, pp. 344–345: consequences of
    the independent weak topology specification. These proofs
    inspect neither a product witness nor the dual carrier. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP NormOpenTopology OpenFamilyTopologyUP WeakEvaluationTopologyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [weak_evaluation_continuous]: each evaluation
    T mapping to T(phi) is continuous, the generating condition
    for the weak dual topologies in Federer 4.1.1, pp. 344–345. *)
Theorem weak_evaluation_continuous (R:realType) (E D:choiceType)
    (ev:D->E->R) (O:set (set D)):
  is_weak_evaluation_topology ev O -> forall e,
    open_family_continuous O (norm_open_family (@scalar_absolute_value_norm R))
      (fun d=>ev d e).
Proof.
move=>hO e.
have hId:open_family_continuous O O id:=@open_family_continuous_identity D O.
have hAll:=(hO.2 D O hO.1 id).1 hId.
exact (hAll e).
Qed.

(** Source for [weak_evaluation_topology_unique]: the evaluation
    universal property uniquely determines the weak topology,
    supporting the generating definition in Federer 4.1.1,
    pp. 344–345. *)
Theorem weak_evaluation_topology_unique (R:realType) (E D:choiceType)
    (ev:D->E->R) (O P:set (set D)):
  is_weak_evaluation_topology ev O -> is_weak_evaluation_topology ev P -> O = P.
Proof.
move=>hO hP.
have hOP:open_family_continuous O P id.
  apply:(hP.2 D O hO.1 id).2=>e; exact:weak_evaluation_continuous hO e.
have hPO:open_family_continuous P O id.
  apply:(hO.2 D P hP.1 id).2=>e; exact:weak_evaluation_continuous hP e.
apply:funext=>A; apply:propext; split=>hA; [exact:hPO A hA|exact:hOP A hA].
Qed.
