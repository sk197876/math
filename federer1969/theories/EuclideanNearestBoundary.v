(** Federer (1969), 3.2.43, printed p. 278:
    a nearest point to an exterior point lies on the actual
    boundary, without convexity or regularity assumptions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  InnerNormInequalities InnerMetric RealNormUP NormDifferentialUP InnerNearestUP
  NormNearestBoundary NormMetric HilbertFormCompactness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_nearest_outside_boundary]: supporting
    boundary-tube inclusion in Federer 3.2.43, p. 278.
    The actual nearest point is retained; no selected
    boundary point, normal, convexity or finite-volume
    premise is added. Existence is used locally elsewhere. *)
Lemma euclidean_nearest_outside_boundary (R:realType) n
    (C:set (inner_metric_space (@euclidean_inner_productP R n)))
    (x a:inner_metric_space (@euclidean_inner_productP R n)):
  ~C x ->is_inner_nearest (@euclidean_inner_productP R n) x C a ->
  C a /\~interior C a.
Proof.
move=>hx hNearest; split; first exact:inner_nearest_member_law hNearest.
move=>hInterior.
pose N:=inner_norm (@euclidean_inner_productP R n).
have hN:is_real_norm N:=inner_norm_real_norm _.
have hNormInterior:norm_domain_interior N C a.
  have [d hd hBall]:=proj1 (metricType_numDomainType.nbhs_mdistP a C) hInterior.
  exists d; split; first exact hd.
  move=>h hSmall; apply:hBall.
  change (is_true (mdist a (a+h)<d)).
  by rewrite inner_metric_distanceE opprD addrA subrr add0r inner_normN.
exact:(@norm_nearest_outside_not_interior R (R_n R n) N C x a hN
  (inner_nearest_member_law hNearest) hx (inner_nearest_minimal_law hNearest) hNormInterior).
Qed.
