(** Federer (1969), 4.1.1, pp. 344–345: opaque weak topology
    determined by its independent evaluation universal property. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import WeakEvaluationTopologyUP WeakEvaluationConvergenceUP
  WeakEvaluationTopologyConvergence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type WeakEvaluationTopologySignature.
(** Source for [opens]: the original weak topology on the
    real-evaluation space, Federer 4.1.1, pp. 344–345. *)
Parameter opens:forall (R:realType) (E D:choiceType),(D->E->R)->set (set D).
(** Source for [laws]: the evaluation universal property of
    the weak topology, supporting the generating strips of
    Federer 4.1.1, pp. 344–345. *)
Parameter laws:forall (R:realType) (E D:choiceType) (ev:D->E->R),
  is_weak_evaluation_topology ev (@opens R E D ev).
(** Source for [convergence]: weak convergence is exactly
    convergence of all real evaluations, supporting the weak
    topology of Federer 4.1.1, pp. 344–345. *)
Parameter convergence:forall (R:realType) (E D:choiceType) (ev:D->E->R),
  is_weak_evaluation_convergence ev (@opens R E D ev).
End WeakEvaluationTopologySignature.
Module WeakEvaluationTopology:WeakEvaluationTopologySignature.
(** Source for [opens]: private selection of the proved weak
    topology witness, supporting Federer 4.1.1, pp. 344–345. *)
Definition opens (R:realType) (E D:choiceType) (ev:D->E->R):set (set D):=
  projT1 (cid (weak_evaluation_topology_with_convergence_exists ev)).
(** Source for [laws]: the hidden topology has the exact
    independent evaluation property, Federer 4.1.1, pp. 344–345. *)
Lemma laws (R:realType) (E D:choiceType) (ev:D->E->R):
  is_weak_evaluation_topology ev (@opens R E D ev).
Proof. exact:(projT2 (cid (weak_evaluation_topology_with_convergence_exists ev))).1. Qed.
(** Source for [convergence]: the selected weak topology has
    its proved independent pointwise convergence law, supporting
    Federer 4.1.1, pp. 344–345. *)
Lemma convergence (R:realType) (E D:choiceType) (ev:D->E->R):
  is_weak_evaluation_convergence ev (@opens R E D ev).
Proof. exact:(projT2 (cid (weak_evaluation_topology_with_convergence_exists ev))).2. Qed.
End WeakEvaluationTopology.
