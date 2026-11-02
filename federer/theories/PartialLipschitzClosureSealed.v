(** Opaque graph closure supporting Federer (1969),
    3.2.14, p. 252. Downstream proofs use the independent
    graph specification and do not unfold the construction. *)
From mathcomp Require Import all_boot boolp reals topology.
From Federer Require Import PartialFunctionUP PartialMetricLipschitz
  PartialLipschitzClosureUP PartialLipschitzClosureConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type PartialLipschitzClosureSignature.
(** Source for [value]: abstract closed-graph extension
    supporting Federer 3.2.14, p. 252. *)
Parameter value : forall (R : realType) (X Y : metricType R)
  (f : partial_function X Y) (L : R),
  is_partial_metric_lipschitz_bound f L -> partial_function X Y.
(** Source for [laws]: the exact closed-graph law for
    the extension supporting Federer 3.2.14, p. 252. *)
Parameter laws : forall (R : realType) (X Y : metricType R)
  (f : partial_function X Y) (L : R)
  (hf : is_partial_metric_lipschitz_bound f L),
  is_partial_lipschitz_graph_closure f (@value R X Y f L hf).
End PartialLipschitzClosureSignature.
Module PartialLipschitzClosure : PartialLipschitzClosureSignature.
(** Source for [value]: opaque selection from the proved
    existence supporting Federer 3.2.14, p. 252. *)
Definition value (R : realType) (X Y : metricType R)
  (f : partial_function X Y) (L : R)
  (hf : is_partial_metric_lipschitz_bound f L) :=
  projT1 (cid (@partial_lipschitz_graph_closure_exists R X Y f L hf)).
(** Source for [laws]: the selected extension satisfies
    its independent specification, Federer 3.2.14, p. 252. *)
Lemma laws (R : realType) (X Y : metricType R)
  (f : partial_function X Y) (L : R)
  (hf : is_partial_metric_lipschitz_bound f L) :
  is_partial_lipschitz_graph_closure f (@value R X Y f L hf).
Proof. exact: projT2 (cid (@partial_lipschitz_graph_closure_exists R X Y f L hf)). Qed.
End PartialLipschitzClosure.
