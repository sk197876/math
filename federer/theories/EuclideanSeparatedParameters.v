(** Federer (1969), 3.2.14, p. 252: two bounded
    parameter sets in positive-dimensional Euclidean
    space can be separated by translation. The
    separation is proved before gluing their maps. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology lra.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerNormInequalities InnerMetric EuclideanCoordinateMetric
  PartialFunctionUP PartialMetricLipschitz PartialEuclideanTranslation
  CoveringFamilyUP MetricBoundedUnion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_bounded_parameters_separate]:
    the translated, positively separated parametrizing
    sets for S union T in Federer 3.2.14, p. 252.
    Positivity of dimension supplies a unit direction;
    neither set is required to be nonempty. *)
Theorem euclidean_bounded_parameters_separate (R : realType) m
    (A B : set (inner_metric_space (@euclidean_inner_productP R m))) :
  (0<m)%N -> metric_set_bounded A -> metric_set_bounded B ->
  exists v : R_n R m,
    forall x y : inner_metric_space (@euclidean_inner_productP R m),
      A x -> B (y-v) -> 1<=mdist x y.
Proof.
move=> hm hA hB.
pose P := inner_metric_space (@euclidean_inner_productP R m).
have [r [hr hAr]] := metric_bounded_distance_bound (0 : P) hA.
have [s [hs hBs]] := metric_bounded_distance_bound (0 : P) hB.
pose v : P := (r+s+1) *: (@coordinate_basis R m (Ordinal hm)).
have hv : mdist (0 : P) v=r+s+1.
  rewrite inner_metric_distanceE sub0r inner_normN /v inner_normZ
    euclidean_coordinate_unit_norm mulr1 ger0_norm //.
  lra.
exists v=> x y hx hy.
have h0x := hAr x hx.
have hyv : mdist y v<=s.
  have hh := hBs (y-v) hy.
  by rewrite !inner_metric_distanceE sub0r inner_normN in hh *.
have h0v := metric_triangle (0 : P) x v.
have hxv := metric_triangle x y v.
rewrite hv in h0v; lra.
Qed.
