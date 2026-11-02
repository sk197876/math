(** Federer (1969), 3.2.26(2), p. 261: the
    omitted Hausdorff-null subset contributes zero to the
    integral-geometric covers. Derive this rough estimate
    before any rectifiable-set equality, to avoid circularity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric HausdorffMeasure HausdorffSphericalComparison
  IntegralGeometricMeasure ProjectionBeta RectifiableGeometricBasicComparisons MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_integral_geometric_hausdorff_rough_bound]:
    supporting estimate for 3.2.26(2), p. 261:
    beta_t Q_t<=S^m<=2^m H^m. All source
    sets are allowed; no rectifiability or measurability is
    assumed. This is used only to control null remainders. *)
Lemma convex_integral_geometric_hausdorff_rough_bound (R:realType) n m
    (hmn:(m<=n)%N) (t: \bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))):
  1<=t ->(@projection_beta R n m hmn t)%:E*
    @convex_integral_geometric_measure R n m hmn t A<=
    ((2:R)^+m)%R%:E*@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m A.
Proof.
move=>ht; exact:(le_trans (@convex_integral_geometric_spherical_rough_bound R n m hmn t A ht)
  (@spherical_measure_le_double_hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m A)).
Qed.

(** Source for [convex_integral_geometric_hausdorff_null]: the
    null-remainder consequence needed in 3.2.26(2),
    p. 261. Multiply the rough comparison by the
    reciprocal of the actual positive projection constant;
    no equality theorem on rectifiable sets is used. *)
Lemma convex_integral_geometric_hausdorff_null (R:realType) n m
    (hmn:(m<=n)%N) (t: \bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))):
  1<=t ->@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m A=0 ->
  @convex_integral_geometric_measure R n m hmn t A=0.
Proof.
move=>ht hNull.
have hBound:=@convex_integral_geometric_hausdorff_rough_bound R n m hmn t A ht.
rewrite hNull mule0 in hBound.
have hBeta:=@projection_beta_positive R n m hmn t ht.
have hInv:(0<=(@projection_beta R n m hmn t)^-1)%R by rewrite invr_ge0; exact:ltW hBeta.
have hScaled:=lee_wpmul2l (lee_tofin hInv) hBound.
rewrite muleA -EFinM mulVf ?gt_eqF // mul1e mule0 in hScaled.
apply/eqP; rewrite eq_le hScaled /=.
exact:(measure_nonnegative (@convex_integral_geometric_measure_is_measure R n m hmn t ht) A).
Qed.

(** Source for [integral_geometric_hausdorff_null]: supporting
    I_t-null remainder in 3.2.26, pp. 261–262.
    The independent Borel-cover measure is below Q_t;
    nonnegativity gives zero also on nonmeasurable null sets. *)
Lemma integral_geometric_hausdorff_null (R:realType) n m
    (hmn:(m<=n)%N) (t: \bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))):
  1<=t ->@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m A=0 ->
  @integral_geometric_measure R n m hmn t A=0.
Proof.
move=>ht hNull.
have hBound:=@integral_geometric_le_convex R n m hmn t A ht.
rewrite (@convex_integral_geometric_hausdorff_null R n m hmn t A ht hNull) in hBound.
apply/eqP; rewrite eq_le hBound /=.
exact:(measure_nonnegative (@integral_geometric_measure_is_measure R n m hmn t ht) A).
Qed.
