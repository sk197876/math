(** Federer (1969), 3.2.46, p. 281: actual curve
    lengths add at a parameter value, by 2.4.10, p. 85.
    This supports concatenation and the first-exit/last-return
    argument without dropping the intervening curve segment. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric RealMetricBackground ExtendedRealOrderTopology RiemannianTensorUP
  RiemannianCurveCost RiemannianAdmissibleIntegral RiemannianCurveSubinterval
  MeasureIntegralUP MeasureSubsetIntegral FiniteIntervalIntegralSplitting.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_admissible_curve_cost_finite_value]:
    the finite values in the distance infimum of Federer
    3.2.46, p. 281, have their proved scalar parts. No
    value at an infinite integral is used. *)
Lemma riemannian_admissible_curve_cost_finite_value (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) x y
    (C : real_line_metric R -> inner_metric_space (@euclidean_inner_productP R n)) a b :
  is_riemannian_admissible_curve A x y C a b ->
  riemannian_curve_cost g C a b = (fine (riemannian_curve_cost g C a b))%:E.
Proof.
move=> hC.
have hFinite : riemannian_curve_cost g C a b \is a fin_num.
  rewrite (ge0_fin_numE (riemannian_curve_cost_nonnegative g C a b)).
  exact: (riemannian_admissible_curve_finite_integral hg hC).2.
exact: esym (fineK hFinite).
Qed.

(** Source for [riemannian_curve_cost_split]: the sum of
    the two actual interval lengths is the whole curve length,
    supporting the triangle and localization arguments of Federer
    3.2.46, p. 281. Degenerate subintervals are included. *)
Lemma riemannian_curve_cost_split (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) x y
    (C : real_line_metric R -> inner_metric_space (@euclidean_inner_productP R n)) a b u :
  is_riemannian_admissible_curve A x y C a b -> a <= u <= b ->
  riemannian_curve_cost g C a b =
    (riemannian_curve_cost g C a u + riemannian_curve_cost g C u b)%E.
Proof.
move=> hC /andP [hau hub].
have hLeft := riemannian_admissible_curve_subinterval hC (lexx a) hau hub.
have hRight := riemannian_admissible_curve_subinterval hC hau hub (lexx b).
have hWholeI := (riemannian_admissible_curve_finite_integral hg hC).1.
have hLeftI := (riemannian_admissible_curve_finite_integral hg hLeft).1.
have hRightI := (riemannian_admissible_curve_finite_integral hg hRight).1.
have hWholeE := riemannian_admissible_curve_cost_finite_value hg hC.
have hLeftE := riemannian_admissible_curve_cost_finite_value hg hLeft.
have hRightE := riemannian_admissible_curve_cost_finite_value hg hRight.
rewrite hWholeE in hWholeI.
rewrite hLeftE in hLeftI.
rewrite hRightE in hRightI.
have hSum := finite_lebesgue_interval_integral_split hau hub hWholeI hLeftI hRightI.
rewrite hWholeE hLeftE hRightE -EFinD.
exact (congr1 (@EFin R) hSum).
Qed.
