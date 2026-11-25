(** Federer (1969), 3.2.45, p. 280:
    the exact Q_1 cube-product upper bound follows
    by removing the positive covering margin. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanCoordinateCubeUP EuclideanCartesianMap ConvexCubeProductCutoff
  IntegralGeometricGauge IntegralGeometricMeasure IntegralGeometricClosedCovers IntegralGeometricMeasureUP
  ProjectionMeasureUP MetricScaleEnvelopeUP CaratheodoryLimitUP
  PolynomialMarginLimit MeasureUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_cube_product_upper_bound]: expanded
    cube-cover consequence in Federer 3.2.45, p. 280.
    For an actual side-s cube P and every second-factor
    set V of finite Q_1^k mass, the original Q_1^(m+k)
    mass of P times V is at most s^m Q_1^k(V).
    Zero mass, zero side and both dimension-zero endpoints
    are included. The original second factor need not
    be measurable, bounded or convex. *)
Theorem convex_cube_product_upper_bound (R : realType) m n k (hKN : (k <= n)%N)
    (a : R_n R m) (s : R)
    (P : set (inner_metric_space (@euclidean_inner_productP R m)))
    (V : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_euclidean_coordinate_cube a s P ->
  @convex_integral_geometric_measure R n k hKN 1 V < +oo ->
  @convex_integral_geometric_measure R (m+n) (m+k) (leq_add (leqnn m) hKN) 1
    (euclidean_cartesian_set P V) <= ((s^+m)%R)%:E *
      @convex_integral_geometric_measure R n k hKN 1 V.
Proof.
move=> hP hFinite.
have hNonnegative := @measure_nonnegative R _ _
  (@convex_integral_geometric_measure_is_measure R n k hKN 1 (lexx 1)) V.
pose v := fine (@convex_integral_geometric_measure R n k hKN 1 V).
have hFiniteValue : @convex_integral_geometric_measure R n k hKN 1 V = v%:E.
  symmetry; apply: fineK; by rewrite (ge0_fin_numE hNonnegative).
have hV : (0 <= v)%R by move: hNonnegative; rewrite hFiniteValue lee_fin.
rewrite hFiniteValue -EFinM.
apply: (caratheodory_limit_least (@convex_integral_geometric_closed_cover_specification
  R (m+n) (m+k) (leq_add (leqnn m) hKN) 1 (lexx 1)))=> delta xi hDelta hXi.
have hBound : xi (euclidean_cartesian_set P V) <= (v*s^+m)%R%:E.
  apply: (@nonnegative_polynomial_margin_limit R m s 1%R v _ hP.1 (@ltr01 R) hV)=> e hE _.
  have h := @convex_cube_product_cutoff_bound R n k hKN m a s P V delta xi hP hDelta hXi e hE.
  by rewrite hFiniteValue -EFinM mulrC in h.
by rewrite mulrC in hBound.
Qed.
