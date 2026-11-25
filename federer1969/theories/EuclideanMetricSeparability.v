(** General topology supporting Federer (1969), 2.10.5, p. 172: the
    Euclidean source in the Suslin-image argument is separable. Extract a
    countable dense set from the already proved countable open base. This is
    background for 2.2.10, p. 65, rather than a separate assertion about
    integral-geometric measure. Source context: EuclideanLebesgueHaar.v and
    CountableBaseDenseSet.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  cardinality reals topology.
From Federer Require Import EuclideanInnerProduct InnerMetric
  EuclideanLebesgueHaar CountableBaseDenseSet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_metric_separable]: supporting
    separability of R^n, including dimension zero, in
    the continuous Suslin-image argument of Federer
    2.10.5, p. 172. A point is used only to
    choose a default for empty basic open sets. *)
Theorem euclidean_metric_separable (R : realType) (n : nat) :
  exists D : set (inner_metric_space (@euclidean_inner_productP R n)),
    countable D /\ dense D.
Proof.
have [U hU] := euclidean_countable_open_base R n.
exact: (@countable_open_base_dense_set
  (inner_metric_space (@euclidean_inner_productP R n)) 0 U hU).
Qed.
