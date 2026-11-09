(** Federer (1969), 3.3.4, p. 291: the
    centre-independent density-one ball ratios
    imply strict uniform fivefold growth. Derive
    both the actual radius cutoff and a finite
    coefficient, retaining the degree-zero case. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology ring lra.
From Federer Require Import MetricDensities MetricDensityNumericalBounds MetricClosedBalls
  PartialFunctionUP PositiveRightOrderLimit PositiveRadiusCommonOrderLimit
  UniformBallGrowthAdequacy EuclideanBallVolume.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [homogeneous_density_one_uniform_growth]:
    the uniform fivefold growth required when
    applying 2.9.17 in Federer 3.3.4, p. 291.
    The original actual ball masses and common
    density one produce a positive radius cutoff
    and coefficient 4 times 5^m greater than one. *)
Theorem homogeneous_density_one_uniform_growth (R:realType) (X:metricType R)
    (mu:set X->\bar R) m (a:X):
  (forall x y r,mu (metric_closed_ball x r)=mu (metric_closed_ball y r)) ->
  partial_function_graph (metric_density m mu) a 1%E ->
  exists d:R,0<d /\ 1<(4:R)*(5:R)^+m /\
    has_uniform_fivefold_ball_growth mu setT d ((4:R)*(5:R)^+m).
Proof.
move=>hBalls [hUpper hLower].
have hLimit:=positive_radius_common_order_limit hLower hUpper.
have hHalf:(2:R)^-1<1 by rewrite invf_lt1 ?ltr0n // ltr1n.
have hHalfE:(((2:R)^-1)%:E<1%E)%E by rewrite lte_fin.
have hTwoE:(1%E<(2:R)%:E)%E by rewrite lte_fin ltr1n.
have [dL [hdL hLowerBound]]:=hLimit.1 (((2:R)^-1)%:E) hHalfE.
have [dU [hdU hUpperBound]]:=hLimit.2 ((2:R)%:E) hTwoE.
pose d:=Num.min dL (dU/5).
have hd:0<d by rewrite /d lt_min hdL divr_gt0 // ltr0n.
have hFive:0<(5:R) by rewrite ltr0n.
have hFive1:1<=(5:R) by rewrite ler1n.
have hPower:1<=(5:R)^+m:=exprn_ege1 m hFive1.
have hLambda:0<(4:R)*(5:R)^+m by rewrite mulr_gt0 ?ltr0n // exprn_gt0.
have hLambda1:1<(4:R)*(5:R)^+m by nra.
exists d; split=>//; split=>// x _ r hr hrd.
have hdLower:d<=dL by rewrite /d ge_min lexx.
have hdUpper:d<=dU/5 by rewrite /d ge_min lexx orbT.
have hrL:r<dL:=lt_le_trans hrd hdLower.
have hrU:r<dU/5:=lt_le_trans hrd hdUpper.
have h5r:0<5*r by rewrite mulr_gt0.
have h5rU:5*r<dU by move:hrU; rewrite (ltr_pdivlMr _ _ hFive) mulrC.
have hLowerMass:=metric_ball_density_value_large hr (hLowerBound r hr hrL).
have hUpperMass:=metric_ball_density_value_bound h5r (ltW (hUpperBound (5*r) h5r h5rU)).
rewrite (hBalls x a (5*r)) (hBalls x a r).
apply:(le_lt_trans hUpperMass).
have hProduct:
    (((4:R)*5^+m*((2:R)^-1*(euclidean_unit_ball_volume R m*r^+m)))%:E<
      ((4:R)*5^+m)%:E*mu (metric_closed_ball a r))%E.
  rewrite EFinM.
  by rewrite lte_pmul2l ?fin_numE ?lte_fin.
have hCoefficient:(4:R)*5^+m*((2:R)^-1*(euclidean_unit_ball_volume R m*r^+m))=
    2*(euclidean_unit_ball_volume R m*(5*r)^+m).
  rewrite exprMn; field; by rewrite ?pnatr_eq0.
by rewrite hCoefficient in hProduct.
Qed.
