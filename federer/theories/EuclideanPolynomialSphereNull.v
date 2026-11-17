(** Federer (1969), 3.4.7, p. 324: the
    unit-sphere exceptional set of a nonzero homogeneous
    polynomial is null. The zero-dimensional source has
    empty unit sphere; positive dimensions use the
    proved radial cone theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm InnerMetric
  PolynomialFunctions HomogeneousPolynomialFunctions EuclideanHomogeneousPolynomialNull
  MeasureUP MeasureBasic HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_homogeneous_polynomial_unit_sphere_null]:
    the unit-sphere assertion in 3.4.7, p. 324,
    with the empty unit sphere in dimension zero
    included explicitly. Natural subtraction in its degree
    is harmless there because the source set is empty. *)
Theorem euclidean_homogeneous_polynomial_unit_sphere_null (R:realType) n k
    (P:PolynomialFunction (R_n R n) R^o):
  @is_homogeneous_polynomial R (R_n R n) R^o k P ->
  (exists v,P v<>0) ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) (n-1)
    [set v|P v = 0 /\inner_norm (@euclidean_inner_productP R n) v = 1] = 0%:E.
Proof.
case:n P=>[P|n P] hHomogeneous hNonzero.
- have hEmpty:[set v:inner_metric_space (@euclidean_inner_productP R 0)|
      P v = 0 /\inner_norm (@euclidean_inner_productP R 0) v = 1] = set0.
    apply/seteqP;split=>v;last by [].
    move=>[_ hUnit].
    have hZero:inner_norm (@euclidean_inner_productP R 0) v = 0.
      by rewrite (coordinate_zero v) inner_norm0.
    rewrite hZero in hUnit.
    have h01:(0:R)!=1 by rewrite eq_sym oner_eq0.
    by rewrite hUnit eqxx in h01.
  rewrite hEmpty;exact:(measure_empty (@hausdorff_measure_is_measure R
    (inner_metric_space (@euclidean_inner_productP R 0)) (0-1))).
- rewrite subn1 /=.
  exact:(@euclidean_homogeneous_polynomial_exceptional_null R n k P hHomogeneous hNonzero).2.
Qed.
