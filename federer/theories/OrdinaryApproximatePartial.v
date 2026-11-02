(** Federer (1969), 3.1.6, p. 216: ordinary coordinate
    derivatives supplied by 2.9.19 are approximate partial derivatives.
    This bridge uses the exact punctured quotient of 3.1.2. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates RealNormUP
  NormMetric RealMetricBackground NormPartialDerivative NormedCurveDerivativeUP
  RealCurveDerivativeUP PartialFunctionUP ApproximatePartialDerivativeUP
  LebesgueScalarMeasure ScalarLebesgueBallContext ScalarEuclideanApproximateLimits
  CenteredNullSetDensity LocalZeroDensity EuclideanApproximateContext
  CenteredBallRelations MetricClosedBalls MeasureSetDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [ordinary_partial_is_approximate]: the identification
    used between the first and second paragraphs of the proof of
    Federer 3.1.6, pp. 216–217. An ordinary limit of the
    coordinate quotient is also its approximate limit, since the only
    excluded nearby increment is zero, a Lebesgue-null singleton. *)
Theorem ordinary_partial_is_approximate (R : realType) n (Y : lmodType R)
    (NY : Y->R) (hNY : is_real_norm NY) (f : R_n R n->Y)
    (a : R_n R n) (i : 'I_n) (v : Y) :
  has_norm_partial_derivative NY f a i v ->
  has_approximate_partial_derivative hNY setT f a i v.
Proof.
move=> hv; split=> // W hW.
have [e he heW] := (metricType_numDomainType.nbhs_mdistP
  (v : real_norm_metric_space hNY) W).1 hW.
have [d [hd hdq]] := hv e he.
have hz := @centered_null_set_density_zero R [the metricType R of real_line_metric R]
  (@lebesgue_scalar_measure R) [set 0] 0 (lebesgue_scalar_is_measure R)
  (@scalar_centered_ball_positive_finite R) (lebesgue_scalar_singleton 0).
apply: (@local_zero_density_mono R [the metricType R of real_line_metric R]
  (@lebesgue_scalar_measure R)
  (@centered_closed_ball_relation R [the metricType R of real_line_metric R])
  _ [set 0] [set t | mdist (0 : real_line_metric R) t<d] 0
  (scalar_approximate_context R) (metric_open_ball_open _ _) _ _ hz).
- change (is_true (mdist (0 : real_line_metric R) 0<d)).
  by rewrite mdistxx.
- move=> t ht hn; apply: contrapT=> hne.
  have ht0 : t!=0 by apply/eqP.
  have hnorm : 0<`|t|<d.
    rewrite normr_gt0 ht0 /=.
    change (is_true (mdist (0 : real_line_metric R) t<d)) in ht.
    by move: ht; rewrite real_line_metric_distanceE sub0r normrN.
  apply: hn.
  exists (t^-1*:(f (a+t*:(@coordinate_basis R n i))-f a)); split.
  + by split; first split.
  + apply: heW.
    change (is_true (NY (v-t^-1*:(f (a+t*:(@coordinate_basis R n i))-f a))<e)).
    rewrite (real_seminorm_subtract hNY.1).
    exact: hdq t hnorm.
Qed.

(** Source for [real_coordinate_curve_derivative_partial]: the
    equality D_i f(u,s)=f_u'(s) in Federer 3.1.6, p. 216.
    A translated coordinate parametrisation is used; associativity
    of vector addition identifies the actual difference quotients. *)
Lemma real_coordinate_curve_derivative_partial (R : realType) n
    (f : R_n R n->R^o) (i : 'I_n) (a : R_n R n) (s v : R) :
  has_real_curve_derivative (fun t=>f (a+t*:(@coordinate_basis R n i))) s v ->
  has_norm_partial_derivative (fun x : R^o=>`|x|) f
    (a+s*:(@coordinate_basis R n i)) i v.
Proof.
move=> hv.
have hh := (scalar_normed_curve_derivative _ _ _).2 hv.
move=> e he; have [d [hd hq]] := hh e he.
exists d; split=> // t ht.
have hx : (a+s*:(@coordinate_basis R n i))+t*:(@coordinate_basis R n i)=
    a+(s+t)*:(@coordinate_basis R n i) by rewrite scalerDl addrA.
rewrite hx; exact: hq t ht.
Qed.
