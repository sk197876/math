(** Supporting boundary case for Federer (1969),
    3.4.8(8), p. 330: extend the existing
    positive-dimensional null-cone theorem to dimension
    zero, whose unit sphere is empty. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanLebesgueDimensions EuclideanConeSphereNull HausdorffMeasure MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_all_dimensions_null_cone_sphere]:
    unit-sphere nullity for the failing directions
    in 3.4.8(8), p. 330. Positive dimensions
    apply the existing radial theorem directly;
    dimension zero uses the empty sphere. *)
Theorem euclidean_all_dimensions_null_cone_sphere (R:realType) n
  (A:set (inner_metric_space (@euclidean_inner_productP R n))):
  (forall t:R,(0<t)%R ->forall v,A v ->A (t*:v)) ->
  @euclidean_lebesgue_measure R n A = 0%:E ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) (n-1)
    [set v|A v /\inner_norm (@euclidean_inner_productP R n) v = 1] = 0%:E.
Proof.
case:n A=>[A|n A] hCone hNull.
- have hEmpty:[set v:inner_metric_space (@euclidean_inner_productP R 0)|
      A v /\inner_norm (@euclidean_inner_productP R 0) v = 1] = set0.
    apply/seteqP;split=>v;last by [].
    move=>[_ hUnit].
    have hZero:inner_norm (@euclidean_inner_productP R 0) v = 0 by rewrite (coordinate_zero v) inner_norm0.
    rewrite hZero in hUnit;have h01:(0:R)!=1 by rewrite eq_sym oner_eq0.
    by rewrite hUnit eqxx in h01.
  rewrite hEmpty;exact:measure_empty (@hausdorff_measure_is_measure R
    (inner_metric_space (@euclidean_inner_productP R 0)) (0-1)).
- rewrite subn1 /=;exact:(@euclidean_null_cone_unit_sphere_null R n A hCone hNull).
Qed.
