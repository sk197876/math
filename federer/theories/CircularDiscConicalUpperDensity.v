(** Federer (1969), 3.3.19, p. 305: the original
    infinite-cone restriction has upper one-density at least
    1/(2pi), simultaneously for all planes and apertures. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets constructive_ereal topology lra ring.
From Federer Require Import GrassmannAbbreviations GrassmannSubspaces EuclideanInnerProduct InnerNorm InnerMetric
  FactorialDiscScalesUP FactorialDiscScalesSealed FactorialDiscScaleLaws CircularTrigonometryUP CircularTrigonometrySealed RealTrigonometryUP
  CircularDiscTreeUP CircularDiscLimitUP CircularDiscRadialMapUP CircularDiscAngularTailDensity
  CircularDiscLateNormalApproximation CircularConicalDensityParameters CircularDiscBufferedConeMass
  PlanarProjectionUnitNormal EuclideanProjectionSpace StructureProjectionKernel StructureKernelOnto
  StructureCone StructureConeBallRatioBound PartialFunctionUP HausdorffMeasure MeasureUP MeasureBasic
  MeasureRestriction MetricDensities MetricDensityNumericalBounds PositiveRadiusLimits ExtendedRealBounds
  NonnegativeRealLowerTests MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Density.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation N:=(inner_norm (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Local Notation pi:=(@CircularTrigonometry.half_period R).
Local Notation S:=(@CircularTrigonometry.sine R).
Local Notation mu:=(@hausdorff_measure R [the metricType R of E] 1).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.
Variable A:set E.
Hypothesis hA:is_circular_disc_limit H A.
Variable eta:nat->partial_function E E.
Hypothesis hEta:forall j,is_circular_disc_radial_map H j (eta j).

(** Source for [circular_disc_projection_conical_upper_density]:
    the exact lower bound 1/(2pi) for the original
    H1 restriction to A intersect X(a,infinity,ker p,s),
    at every common original angular-tail point and every
    original projection p and 0<s<1, in 3.3.19,
    p. 305. Local smaller apertures repair the strict
    auxiliary inclusion; the numbered conclusion is unchanged. *)
Theorem circular_disc_projection_conical_upper_density (a:E):
  A a ->(forall v,closure (circular_disc_radial_tail eta a v)= @PlanarUnitCircleGeometry.planar_unit_circle R) ->
  forall (p:euclidean_projection_space R 2 1) (s:R),0<s ->s<1 ->
  ((1/(2* pi))%:E<=upper_metric_density 1
    (measure_restrict mu (A `&` structure_cone (structure_projection_kernel (leqnSn 1) p) a +oo s)) a)%E.
Proof.
move=>ha hDense p s hs hs1.
have [u hNormal]:= @planar_projection_unit_normal_exists R p.
have hp:= real_trigonometry_pi_positive (circular_trig_basic (@CircularTrigonometry.laws R)).
have hConstant:0<1/(2* pi) by rewrite divr_gt0 //;lra.
have hMu:= @hausdorff_measure_is_measure R E 1.
pose nu:= measure_restrict mu (A `&` structure_cone (structure_projection_kernel (leqnSn 1) p) a +oo s).
have hNu:is_measure nu:= measure_restrict_is_measure hMu _.
have hNonnegative:=(@metric_densities_nonnegative R E 1 nu a hNu).2.
apply:(@nonnegative_ereal_positive_lower_tests R (upper_metric_density 1 nu a) (1/(2* pi)) hNonnegative hConstant)=>k hk hkBound.
have [alpha [beta [eps [hAlpha [hAlphaHalf [hSigma [hSigmaS [hBeta [hBetaPi [hEps hRatio]]]]]]]]]]:=
  @circular_conical_density_parameters R s k hs hs1 hk hkBound.
have [J hMass]:= @circular_disc_buffered_cone_mass R H hH A hA p u alpha beta s eps
  hNormal hAlpha hAlphaHalf hSigma hSigmaS hBeta hBetaPi hEps.
rewrite /upper_metric_density /positive_radius_upper_limit.
apply:extended_real_inf_greatest=>b [d [hd ->]].
have hCutoff:0<d/(2* s) by rewrite divr_gt0 //;lra.
have [J2 hRadiusSmall]:= @factorial_disc_radius_small R (@FactorialDiscScales.count R) rho
  (@FactorialDiscScales.laws R) (d/(2* s)) hCutoff.
have hNearRadius:0<s-S alpha by lra.
have [j [v [hj [hGraph hNear]]]]:= @circular_disc_late_normal_approximation R eta a hDense
  u (s-S alpha) (maxn J J2) hNormal.1 hNearRadius.
have hj1:(J<=j)%N:= leq_trans (leq_maxl J J2) hj.
have hj2:(J2<=j)%N:= leq_trans (leq_maxr J J2) hj.
have hLower:= hMass j (eta j) a v hj1 (hEta j) ha hGraph hNear.
have hrho:= @factorial_disc_radius_positive R (@FactorialDiscScales.count R) rho (@FactorialDiscScales.laws R) j.
have hBall:= @structure_cone_original_ball_ratio_bound R mu A p a (rho j) s
  ((alpha-beta)/pi-2* eps) hMu hrho hs hLower.
have hRadius:0<2* rho j* s by nra.
have hSmall:2* rho j* s<d.
  have h:= hRadiusSmall j hj2.
  rewrite ltr_pdivlMr in h;last by lra.
  nra.
apply:(le_trans (lee_tofin (ltW hRatio)) (le_trans hBall _)).
apply:extended_real_sup_upper.
exists (2* rho j* s);split=>//;by apply/andP;split.
Qed.

(** Source for [circular_disc_all_planes_conical_upper_density]:
    every original line V is an actual projection kernel,
    so the previous original-set theorem gives the full
    all-V assertion of 3.3.19, p. 305 at one common
    angular-tail point. No plane is excluded. *)
Theorem circular_disc_all_planes_conical_upper_density (a:E):
  A a ->(forall v,closure (circular_disc_radial_tail eta a v)= @PlanarUnitCircleGeometry.planar_unit_circle R) ->
  forall (V:G (R_n R 2) 1) (s:R),0<s ->s<1 ->
  ((1/(2* pi))%:E<=upper_metric_density 1
    (measure_restrict mu (A `&` structure_cone V a +oo s)) a)%E.
Proof.
move=>ha hDense V s hs hs1.
have [p hKernel]:= @structure_projection_kernel_onto R 2 1 (leqnSn 1) V.
have h:= circular_disc_projection_conical_upper_density ha hDense p hs hs1.
by rewrite hKernel in h.
Qed.

(** Source for [circular_disc_conical_upper_density_almost]:
    for H1 almost every original a in A, simultaneously
    every original line plane V and every 0<s<1 satisfy
    the exact 1/(2pi) lower bound, as asserted in
    3.3.19, p. 305. The sole exceptional set is the
    already proved common angular-tail exception. *)
Theorem circular_disc_conical_upper_density_almost:
  measure_almost_everywhere_on mu A [set a:E|forall (V:G (R_n R 2) 1) (s:R),
    0<s ->s<1 ->((1/(2* pi))%:E<=upper_metric_density 1
      (measure_restrict mu (A `&` structure_cone V a +oo s)) a)%E].
Proof.
have hAlmost:= @circular_disc_angular_tails_dense_almost R H hH A hA eta hEta.
have hAbsolute:=(@measure_almost_everywhere_on_implication R E mu A _).1 hAlmost.
apply:(@measure_almost_everywhere_on_implication R E mu A _).2.
apply:(@measure_almost_everywhere_mono R E mu (@hausdorff_measure_is_measure R E 1) _ _ _ hAbsolute).
move=>a hGood ha;exact:(circular_disc_all_planes_conical_upper_density ha (hGood ha)).
Qed.
End Density.
