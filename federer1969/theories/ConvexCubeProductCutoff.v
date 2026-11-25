(** Supporting the covering passage in Federer (1969),
    3.2.45, p. 280. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanCoordinateCubeUP EuclideanCartesianMap EuclideanBlockCoordinates MetricProductRectangles
  ConvexCubeSubdivisionCostBound UniformMeshCountUP UniformMeshCount UniformMeshCountLaws
  IntegralGeometricGauge IntegralGeometricMeasure IntegralGeometricMeasureUP IntegralGeometricClosedCovers
  ProjectionMeasureUP MetricScaleCutoffCost MetricScaleEnvelopeUP MetricScaleEnvelope MetricScaleWeightedBound
  CaratheodoryLimitUP CaratheodoryBorelRegular MetricRectangleSliceMeasure
  MetricDiameter MeasureUP MeasureBasic TopologicalBorel BorelClosedProjection ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_cube_product_cutoff_bound]: expanded
    second-factor covering step in Federer 3.2.45, p. 280.
    For a fixed target cutoff, the original Q_1 cost of
    the second factor bounds a cube rectangle with coefficient
    (s+e)^m for each e>0. Actual sealed subdivision counts
    make the first mesh small; a smaller second cutoff
    controls its ratio to that mesh. Arbitrary second-factor
    sets and infinite masses are retained at this stage. *)
Theorem convex_cube_product_cutoff_bound (R : realType) n k (hKN : (k <= n)%N) :
  forall m (a : R_n R m) (s : R)
    (P : set (inner_metric_space (@euclidean_inner_productP R m)))
    (V : set (inner_metric_space (@euclidean_inner_productP R n)))
    (delta : \bar R)
    (xi : set (inner_metric_space (@euclidean_inner_productP R (m+n))) -> \bar R),
    is_euclidean_coordinate_cube a s P -> 0 < delta ->
    is_metric_scale_envelope
      (fun j : closed_convex_euclidean_sets R (m+n) => val j)
      (fun j => @integral_geometric_gauge R (m+n) (m+k) (leq_add (leqnn m) hKN) 1 (val j))
      delta xi -> forall e : R, (0 < e)%R ->
    xi (euclidean_cartesian_set P V) <= ((s+e)^+m)%R%:E *
      @convex_integral_geometric_measure R n k hKN 1 V.
Proof.
move=> m a s P V delta xi hP hDelta hXi e hE.
have [M [hM hSubdivision]] := @convex_cube_subdivision_cutoff_bound R n k hKN.
pose X := inner_metric_space (@euclidean_inner_productP R m).
pose Y := inner_metric_space (@euclidean_inner_productP R n).
pose Z := inner_metric_space (@euclidean_inner_productP R (m+n)).
pose J := closed_convex_euclidean_sets R (m+n).
pose K := closed_convex_euclidean_sets R n.
pose c := fun j : J => @integral_geometric_gauge R (m+n) (m+k) (leq_add (leqnn m) hKN) 1 (val j).
pose d := fun j : K => @integral_geometric_gauge R n k hKN 1 (val j).
have hC (j : J) : 0 <= c j.
  apply: integral_geometric_gauge_nonnegative; first exact: lexx.
  apply: metric_borel_suslin; exact: closed_borel_set (set_valP j).1.
have hD (j : K) : 0 <= d j.
  apply: integral_geometric_gauge_nonnegative; first exact: lexx.
  apply: metric_borel_suslin; exact: closed_borel_set (set_valP j).1.
have hXiMeasure : is_measure xi := metric_scale_envelope_is_measure hXi hC.
pose rho := fun B : set Y => xi (euclidean_cartesian_set P B).
have hRho : is_measure rho := @metric_rectangle_second_slice_is_measure R
  [the metricType R of Z] [the metricType R of X] [the metricType R of Y]
  (fun z => (euclidean_block_split z).1) (fun z => (euclidean_block_split z).2) P xi hXiMeasure.
have [q [hQ0 hQDelta]] := @extended_rationals_order_dense R 0 delta hDelta.
pose b : R := ratr q.
have hB : (0 < b)%R := hQ0.
pose h : R := (b/(2*(m%:R+1)))%R.
have hM1 : (0 < m%:R+1 :> R)%R by have hNat := ler0n R m; lra.
have hH : (0 < h)%R by rewrite /h divr_gt0 // mulr_gt0 //; lra.
pose v := @uniform_mesh_count R s h hP.1 hH.
have hCount := @uniform_mesh_count_specification R s h hP.1 hH.
have hV : (0 < v)%N := uniform_mesh_count_positive_law hCount.
have hVR : (0 < v%:R :> R)%R by rewrite ltr0n.
have hMPositive : (0 < M)%R := lt_trans ltr01 hM.
have hDenominator : (0 < v%:R*M)%R := mulr_gt0 hVR hMPositive.
pose eta : R := Order.min (b/2)%R (e/(v%:R*M))%R.
have hHalfPositive : (0 < b/2)%R by rewrite divr_gt0 // ltr0n.
have hRatioPositive : (0 < e/(v%:R*M))%R by rewrite divr_gt0.
have hEta : (0 < eta)%R by rewrite /eta lt_min hHalfPositive hRatioPositive.
have hEtaB : (eta <= b/2)%R by rewrite /eta ge_min lexx.
have hEtaE : (eta <= e/(v%:R*M))%R by rewrite /eta ge_min lexx orbT.
have hError : (v%:R*M*eta <= e)%R.
  by move: hEtaE; rewrite ler_pdivlMr // mulrC.
have hWidth : (s/v%:R <= h)%R := uniform_mesh_count_cell_width hCount.
have hIdentity : ((m%:R+1)*h = b/2)%R.
  rewrite /h; field; by rewrite (lt0r_neq0 hM1) ?pnatr_eq0.
have hFirst : (m%:R*(s/v%:R) <= b/2)%R.
  have hScaledWidth := ler_wpM2l (ler0n R m) hWidth.
  rewrite mulrDl mul1r in hIdentity; have hH0 := ltW hH; lra.
have hProductCutoff : ((m%:R*(s/v%:R)+eta)%R)%:E <= delta.
  apply: le_trans _ (ltW hQDelta); rewrite lee_fin.
  have hSum := lerD hFirst hEtaB; by rewrite -splitr in hSum.
pose B : R := ((s+e)^+m)%R.
have hCoefficient : (0 < B)%R.
  apply: exprn_gt0; have hS := hP.1; lra.
pose zeta := metric_scale_envelope (fun j : K => val j) d eta%:E.
have hZeta := @metric_scale_envelope_specification R [the metricType R of Y] K
  (fun j => val j) d eta%:E.
have hGenerator (j : K) : extended_metric_diameter (val j) <= eta%:E ->
    rho (val j) <= B%:E*d j.
  move=> hSize.
  case: (pselect (val j !=set0))=> [hNonempty|hEmpty].
  - have hBound := hSubdivision m v a s eta P (val j) delta xi hV hP hNonempty
      (set_valP j).1 (set_valP j).2 (ltW hEta) hSize hProductCutoff hXi.
    have hSumNonnegative : (0 <= s+v%:R*M*eta)%R.
      exact: addr_ge0 hP.1 (mulr_ge0 (ltW hDenominator) (ltW hEta)).
    have hSide : (s+v%:R*M*eta <= s+e)%R := lerD (lexx s) hError.
    have hPower : ((s+v%:R*M*eta)^+m <= B)%R.
      apply: lerXn2r.
      - exact hSumNonnegative.
      - exact: addr_ge0 hP.1 (ltW hE).
      - exact hSide.
    have hScaled := lee_wpmul2l (hD j) (lee_tofin hPower).
    rewrite [X in _ <= X]muleC in hScaled.
    exact (le_trans hBound hScaled).
  - have hEmptyValue : val j = set0.
      apply/seteqP; split=> y hY; last by [].
      exfalso; apply: hEmpty; by exists y.
    have hProductEmpty : euclidean_cartesian_set P (val j) = set0.
      rewrite hEmptyValue; apply/seteqP; split=> z; last by [].
      by move=> [_ hFalse].
    rewrite /rho hProductEmpty (measure_empty hXiMeasure).
    exact: mule_ge0 (lee_tofin (ltW hCoefficient)) (hD j).
have hBound := @measure_bounded_by_scaled_metric_envelope R [the metricType R of Y]
  K (fun j => val j) d eta%:E zeta rho B hZeta hRho hCoefficient hGenerator V.
apply: le_trans hBound _; apply: lee_wpmul2l; first exact: lee_tofin (ltW hCoefficient).
exact: (@caratheodory_limit_upper R [the metricType R of Y] K (fun j => val j) d
  (@convex_integral_geometric_measure R n k hKN 1)
  (@convex_integral_geometric_closed_cover_specification R n k hKN 1 (lexx 1))
  V eta%:E zeta (lte_tofin hEta) hZeta).
Qed.
