(** Federer (1969), 3.2.35, p. 272:
    orthogonal projections of the original open
    body are open, by actual exact-distance lifts. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanProjectionSpace EuclideanProjectionMetric ProjectionImageLifting.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_projection_open_image]: supporting
    openness of p(S) in the boundary-fibre
    calculation of Federer 3.2.35, p. 272.
    Lift each sufficiently close target point
    with exactly its target displacement. The
    original source neighbourhood then gives an
    actual original preimage, without convexity,
    boundedness or a selected right inverse. *)
Theorem euclidean_projection_open_image (R:realType) n m
    (p:orthogonal_projection_metric_space R n m)
    (S:set (inner_metric_space (@euclidean_inner_productP R n))):
  open S ->@open [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)]
    (euclidean_projection_linear p @` S).
Proof.
move=>hOpen; rewrite openE=>y [x hx hValue].
have [d hd hBall]:=proj1 (metricType_numDomainType.nbhs_mdistP x S)
  (open_nbhs_nbhs (conj hOpen hx)).
apply:(proj2 (metricType_numDomainType.nbhs_mdistP
  (y:inner_metric_space (@euclidean_inner_productP R m)) (euclidean_projection_linear p @` S))).
exists d=>// z hz.
have [u [hu hDistance]]:=@orthogonal_projection_exact_distance_lift R n m p x z.
exists u; last exact hu; apply:hBall.
change (is_true (mdist x u<d)); by rewrite hDistance hValue.
Qed.
