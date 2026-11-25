(** Federer (1969), 3.1.19, p. 231: local
    coordinate neighbourhoods make Euclidean submanifolds locally
    compact. Their countable compact cover and 2.2.1(2),
    pp. 59–60, imply Borelness; supporting the disjoint
    class-one reduction in 3.2.47, p. 283. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets cardinality topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanSubmanifoldUP SubmanifoldCountableCompactCover TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [euclidean_submanifold_borel]: Borelness of
    each class-one covering submanifold in the 3.2.29
    reduction of 3.2.47, p. 283, by local
    compactness from 3.1.19, p. 231, and
    the countable union law of 2.2.1(2), p. 59. *)
Theorem euclidean_submanifold_borel (R:realType) N r k (M:set (R_n R N)):
  @is_euclidean_submanifold R N r k M ->
  @borel_set (inner_metric_space (@euclidean_inner_productP R N)) M.
Proof.
move=>hM; have [K [hK hCover]]:=submanifold_countable_compact_cover hM.
rewrite hCover.
apply:(borel_set_countable_union (countableP setT)).
move=>i _; apply:closed_borel_set.
exact (compact_closed (@metric_hausdorff R (inner_metric_space (@euclidean_inner_productP R N))) (hK i).1).
Qed.
