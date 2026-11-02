(** Federer (1969), 3.2.35, p. 272:
    integrate the actual distance-level masses
    and evaluate every coefficient of the
    lower-degree tube polynomial. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex CoveringFamilyUP
  MetricSetDistanceUP SteinerTubePolynomial SteinerDistanceLevelAverage SteinerIntegratedCoefficient
  RadialWeightedPowerIntegral ConvexIntrinsicVolumeIntegrals IntegralGeometricGauge ProjectionBeta
  EuclideanBallVolume HausdorffMeasure RealOpenIntervals LebesgueScalarMeasure
  ExtendedRealOrderTopology PartialFunctionBasic MeasureIntegralUP MeasureSubsetIntegral
  SubsetFiniteNonnegativeIntegral SubsetIntegralTotalAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [steiner_distance_level_integral]: the
    last radius integration in Federer 3.2.35,
    p. 272. Under the lower-dimensional induction,
    the whole original level has the proved
    pointwise mass polynomial. Actual weighted
    monomial integrals, finite subset-integral
    interchange and the proved alpha/beta identity
    evaluate its integral. Only positive interval
    values enter; original partial domains and
    all natural coefficient endpoints remain. *)
Theorem steiner_distance_level_integral (R:realType) k
    (S:set (inner_metric_space (@euclidean_inner_productP R k.+1))) d (r:R):
  (forall (A:set (inner_metric_space (@euclidean_inner_productP R k))) e,
    A!=set0 ->is_inner_convex A ->metric_set_bounded A ->is_metric_set_distance A e ->
    is_steiner_tube_volume A e) ->
  S!=set0 ->is_inner_convex S ->metric_set_bounded S ->is_metric_set_distance S d ->(0<r)%R ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) (real_open_interval 0 r)
    (partial_function_total (fun t:R=>(@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R k.+1)) k [set x|d x=t]:extended_real_line R)))
    (\sum_(i:'I_k.+1) @integral_geometric_gauge R k.+1 i
      (leq_trans (steiner_dimension_guard i) (leqnSn k)) 1 S*
      (euclidean_unit_ball_volume R (k.+1-i)*r^+(k.+1-i))%R%:E).
Proof.
move=>hIH hNonempty hS hBound hD hr.
pose mu:=@lebesgue_scalar_measure R.
pose hm:=lebesgue_scalar_is_measure R.
pose A:=real_open_interval 0 r.
pose rho (i:'I_k.+1):R:=(@projection_beta R k.+1 i (leq_trans (steiner_dimension_guard i) (leqnSn k)) 1 /
  @projection_beta R k i (steiner_dimension_guard i) 1)%R.
pose G (i:'I_k.+1): \bar R :=@integral_geometric_gauge R k.+1 i
  (leq_trans (steiner_dimension_guard i) (leqnSn k)) 1 S.
pose c (i:'I_k.+1): \bar R :=(euclidean_unit_ball_volume R (k-i))%:E*((rho i)%:E*G i).
pose outer:=(2/ @projection_beta R k.+1 k (leqnSn k) 1)%R%:E.
have hRhoPositive i:(0<=rho i)%R.
  apply:divr_ge0.
  - exact:ltW (@projection_beta_positive R k.+1 i (leq_trans (steiner_dimension_guard i) (leqnSn k)) 1 (lexx 1)).
  - exact:ltW (@projection_beta_positive R k i (steiner_dimension_guard i) 1 (lexx 1)).
have hGPositive i:0<=G i.
  exact:(@convex_intrinsic_volume_nonnegative_finite R k.+1 i
    (leq_trans (steiner_dimension_guard i) (leqnSn k)) 1 S hNonempty hS hBound (lexx 1)).1.
have hCPositive i:0<=c i.
  apply:mule_ge0; first exact:lee_tofin (ltW (euclidean_unit_ball_volumeE R (k-i)).2).
  exact:mule_ge0 (lee_tofin (hRhoPositive i)) (hGPositive i).
pose u (i:'I_k.+1) (t:R):extended_real_line R:=c i*(t^+(k-i))%R%:E.
pose a (i:'I_k.+1): \bar R :=c i*(r^+(k-i).+1/(k-i).+1%:R)%R%:E.
have hUPositive i t:A t ->0<=u i t.
  move=>[ht0 _]; apply:mule_ge0; first exact:hCPositive.
  rewrite lee_fin; apply:exprn_ge0; exact:ltW ht0.
have hIntegral i:is_measure_subset_integral mu A (partial_function_total (u i)) (a i).
  exact:(@radial_weighted_power_integral R (k-i) r (c i) hr (hCPositive i)).
have hSum:=@subset_finite_nonnegative_integral R R [the finType of 'I_k.+1] mu hm A u a hUPositive hIntegral.
have hSumPositive t:A t ->0<= \sum_i u i t.
  move=>ht; apply:sume_ge0=>i _; exact:hUPositive i t ht.
have hOuterPositive:0<=outer.
  rewrite lee_fin; apply:divr_ge0; first exact:ler0n.
  exact:ltW (@projection_beta_positive R k.+1 k (leqnSn k) 1 (lexx 1)).
have hScaled:=@subset_nonnegative_extended_scale_integral R R mu hm A
  (fun t:R=>(\sum_i u i t:extended_real_line R)) (\sum_i a i) outer hSumPositive hOuterPositive hSum.
have hActual:is_measure_subset_integral mu A
    (partial_function_total (fun t:R=>(@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R k.+1)) k [set x|d x=t]:extended_real_line R)))
    (outer* \sum_i a i).
  apply:(@subset_integral_total_agreement R R mu A
    (fun t:R=>(outer* \sum_i u i t:extended_real_line R))
    (fun t:R=>(@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R k.+1)) k
      [set x|d x=t]:extended_real_line R)) (outer* \sum_i a i) _).1 hScaled.
  move=>t [ht0 _]; symmetry.
  rewrite (@steiner_distance_level_average R k S d t hIH hNonempty hS hBound hD ht0).
  congr (outer*_); apply:eq_bigr=>i _.
  change ((euclidean_unit_ball_volume R (k-i)*t^+(k-i))%R%:E*((rho i)%:E*G i)=
    ((euclidean_unit_ball_volume R (k-i))%:E*((rho i)%:E*G i))*(t^+(k-i))%R%:E).
  rewrite EFinM; exact:muleAC.
have hAPositive i:0<=a i.
  apply:mule_ge0; first exact:hCPositive.
  rewrite lee_fin; apply:divr_ge0; last exact:ler0n.
  apply:exprn_ge0; exact:ltW hr.
have hReorder (b e f q:R) (z: \bar R):
    b%:E*((e%:E*(f%:E*z))*q%:E)=(b*e*f*q)%R%:E*z.
  rewrite !EFinM !muleA; exact:muleAC.
have hValue:outer* \sum_i a i=\sum_(i:'I_k.+1) G i*
    (euclidean_unit_ball_volume R (k.+1-i)*r^+(k.+1-i))%R%:E.
  rewrite ge0_sume_distrr; last by move=>i _; exact:hAPositive.
  apply:eq_bigr=>i _; rewrite /a /c /outer hReorder.
  have hCoefficient:
    ((2/ @projection_beta R k.+1 k (leqnSn k) 1)*euclidean_unit_ball_volume R (k-i)*rho i*
      (r^+(k-i).+1/(k-i).+1%:R))%R=
    (euclidean_unit_ball_volume R (k.+1-i)*r^+(k.+1-i))%R.
    exact:(@steiner_integrated_coefficient R k i (steiner_dimension_guard i) r).
  rewrite hCoefficient; exact:muleC.
by rewrite hValue in hActual.
Qed.
