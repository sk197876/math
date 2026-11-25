(** Federer (1969), 3.3.19, p. 305: quantitative
    mass in the actual original strict cones, from uniform
    actual cap masses and local original radial coordinates. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets constructive_ereal topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric MetricClosedBalls
  FactorialDiscScalesUP FactorialDiscScalesSealed FactorialDiscScaleLaws
  RealTrigonometryUP CircularTrigonometryUP CircularTrigonometrySealed
  CircularDiscTreeUP CircularDiscLimitUP CircularDiscRadialMapUP CircularDiscRadialReconstruction
  CircularDiscCaps CircularDiscUniformCapMass CircularCapThresholdTail CircularDiscExactMass
  CircularSineOrder CircularCosineReflection NaturalScaledReciprocalTail
  PlanarCircleCapCoordinates PlanarCapConeCoordinates PlanarProjectionUnitNormal PlanarBufferedCapCone
  EuclideanProjectionSpace StructureProjectionKernel StructureCone PartialFunctionUP
  HausdorffMeasure MeasureUP MeasureBasic NormalizedBinaryMeasureRemainder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Mass.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation N:=(inner_norm (@euclidean_inner_productP R 2)).
Local Notation B:=(@euclidean_inner_product R 2).
Local Notation rho:=(@FactorialDiscScales.radius R).
Local Notation pi:=(@CircularTrigonometry.half_period R).
Local Notation C:=(@CircularTrigonometry.cosine R).
Local Notation S:=(@CircularTrigonometry.sine R).
Local Notation mu:=(@hausdorff_measure R [the metricType R of E] 1).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.
Variable A:set E.
Hypothesis hA:is_circular_disc_limit H A.

(** Source for [circular_disc_buffered_cone_mass]: every late
    original eta_j(a) sufficiently near a prescribed actual
    normal gives the lower normalized ORIGINAL cone mass
    (alpha-beta)/pi-2epsilon. All original cap masses,
    radial deficits and strict cone conditions are proved;
    alpha is acute and sin(alpha)<s is only an auxiliary
    choice in the proof of 3.3.19, p. 305. *)
Theorem circular_disc_buffered_cone_mass
    (p:euclidean_projection_space R 2 1) (u:E) (alpha beta s eps:R):
  is_planar_projection_unit_normal p u ->0<alpha ->alpha<pi/2 ->
  0<S alpha ->S alpha<s ->0<beta ->beta<=pi ->0<eps ->
  exists J:nat,forall j (eta:partial_function E E) (a v:E),
  (J<=j)%N ->is_circular_disc_radial_map H j eta ->A a ->
  partial_function_graph eta a v ->N (u-v)<s-S alpha ->
  ((((alpha-beta)/pi-2* eps)%:E<=
    mu (A `&` structure_cone (structure_projection_kernel (leqnSn 1) p)
      a (2* rho j* s)%:E s)/(2* rho j)%:E)%E).
Proof.
move=>hNormal hAlpha hAlphaHalf hSigma hSigmaS hBeta hBetaPi hEps.
have hPi:= real_trigonometry_pi_positive (circular_trig_basic (@CircularTrigonometry.laws R)).
have hAlpha0:0<=alpha:= ltW hAlpha.
have hAlphaPi:alpha<=pi by lra.
have hHalf0:0<=pi/2 by lra.
have hHalfPi:pi/2<=pi by lra.
have hCos:0<C alpha.
  have h:= @circular_trig_cosine_decreases R S C (@CircularTrigonometry.arcsine R)
    (@CircularTrigonometry.arccosine R) pi (@CircularTrigonometry.laws R)
    alpha (pi/2) hAlpha0 hAlphaPi hHalf0 hHalfPi hAlphaHalf.
  by rewrite circular_cosine_quarter_turn in h.
have hUnit:C alpha^+2+S alpha^+2= 1:= circular_trig_unit (@CircularTrigonometry.laws R) alpha.
have [J1 hUniform]:= @circular_disc_uniform_cap_mass R H hH A hA eps hEps.
have [J2 hThreshold]:= @circular_cap_threshold_angle_tail R beta hBeta hBetaPi.
have hTwo:0<(2:R) by rewrite ltr0n.
have hBuffer:0<2*(s-S alpha) by lra.
have [J3 hSmall]:= @natural_scaled_reciprocal_tail R 2 (2*(s-S alpha)) hTwo hBuffer.
exists (maxn (maxn J1 J2) J3)=>j eta a v hj hEta ha hGraph hNear.
have hj1:(J1<=j)%N:= leq_trans (leq_trans (leq_maxl J1 J2) (leq_maxl _ J3)) hj.
have hj2:(J2<=j)%N:= leq_trans (leq_trans (leq_maxr J1 J2) (leq_maxl _ J3)) hj.
have hj3:(J3<=j+4)%N:= leq_trans (leq_trans (leq_maxr (maxn J1 J2) J3) hj) (leq_addr 4 j).
have [_ hSmallN]:= hSmall _ hj3.
have hThresholdN:= hThreshold j hj2.
have [z [hz [d [hd [hdr [hDeficit [hVertex hVUnit]]]]]]]:=
  @circular_disc_radial_vertex_reconstruction R H hH A hA j eta a v hEta ha hGraph.
have [e hFrame]:= @planar_circle_frame_exists R v hVUnit.
pose w:= planar_rotated_frame_direction v e (C alpha) (S alpha).
have [hWUnit hWPair]:= @planar_rotated_frame_direction_laws R v e (C alpha) (S alpha) hFrame hUnit.
have [hCapLower _]:= hUniform j z w alpha hj1 hz hWUnit hAlpha0 hAlphaPi.
have hBeta0:0<=beta:= ltW hBeta.
have [_ hCapUpper]:= hUniform j z v beta hj1 hz hVUnit hBeta0 hBetaPi.
pose T:= A `&` circular_disc_cap z (rho j) w alpha.
pose D:= A `&` circular_disc_cap z (rho j) v beta.
pose K:= A `&` structure_cone (structure_projection_kernel (leqnSn 1) p)
  a (2* rho j* s)%:E s.
have hr:= @factorial_disc_radius_positive R (@FactorialDiscScales.count R) rho
  (@FactorialDiscScales.laws R) j.
have hCover:T `<=` K `|` D.
  move=>x [hxA [hxBall hxCap]].
  case:(pselect (circular_disc_cap z (rho j) v beta x))=>hxBeta.
  - by right;split.
  - left;split=>//.
    have hCoordinate:B (x-z) v<rho j* C beta.
      rewrite ltNge;apply/negP=>hBad;apply:hxBeta;by split.
    have hThresholdScaled:rho j* C beta<rho j*(1-2/(j+4)%:R) by rewrite ltr_pM2l.
    have hBelow:B (x-z) v<rho j-2* rho j/(j+4)%:R by nra.
    have hd0:0<=d:= ltW hd.
    have hCone:= @planar_buffered_cap_cone_inclusion R p u v e z x (rho j) d
      (C alpha) (S alpha) s (j+4)%N hNormal hFrame hr hd0 hdr hDeficit
      hCos hSigma hUnit hSigmaS hSmallN hNear hxBall hxCap hBelow.
    by rewrite -hVertex in hCone.
have hMu:= @hausdorff_measure_is_measure R E 1.
have hConeFinite:(mu K< +oo)%E.
  have hBound:= @measure_mono R E mu hMu K A (fun x hx=>hx.1).
  rewrite (@circular_disc_hausdorff_mass R H hH A hA) in hBound.
  exact:le_lt_trans hBound (ltry (2:R)).
have hDen:0<2* rho j by lra.
have hRemainder:= @normalized_binary_measure_remainder R E mu hMu T K D
  (2* rho j) (alpha/pi-eps) (beta/pi+eps) hDen hConeFinite hCover
  (ltW hCapLower) (ltW hCapUpper).
have hScalar:alpha/pi-eps-(beta/pi+eps)=(alpha-beta)/pi-2* eps by rewrite mulrBl;ring.
by rewrite hScalar in hRemainder.
Qed.
End Mass.
