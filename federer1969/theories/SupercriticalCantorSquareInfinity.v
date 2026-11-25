(** Federer (1969), 3.3.20, pp. 306–307: the actual supercritical infinity integral-geometric mass. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets
  constructive_ereal topology lra.
From Federer Require Import RealMetricBackground EuclideanInnerProduct InnerMetric EuclideanCantorProduct
  PowerCantorPairUP PowerCantorSquarePure PureFiniteInfinityMassZero EuclideanProjectionSpace
  EuclideanLebesgueDimensions ProjectedVolumeMeasurability IntegralGeometricMeasure IntegralGeometricNullSets
  OrthogonalProjectionProbability SupercriticalProjectionOpen SupercriticalOriginalProjectionMass
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [supercritical_original_cantor_square_infinity]:
    I_infinity^1(E)=infinity for every original fixed-binary exponent
    1/2<m<1, the positive-mass assertion of 3.3.20, p. 307,
    combined with its no-finite-positive-subset conclusion on p. 306.
    Actual positive-probability full projections exclude zero mass by
    the original Borel-hull null characterization; proved original
    pure unrectifiability then excludes every finite value. *)
Theorem supercritical_original_cantor_square_infinity (R:realType) (c m:R)
    (A:set (real_line_metric R)) (f:R->R):
  (0<c)%R ->(1/2<m)%R ->(m<1)%R ->
  is_power_cantor_pair c m (fun _:nat=>2%N) A f ->
  @integral_geometric_measure R 2 1 (leqnSn 1) +oo (euclidean_cantor_product A A)=+oo.
Proof.
move=>hc hSuper hm1 hPair.
have hm:(0<m)%R by lra.
pose X:=inner_metric_space (@euclidean_inner_productP R 2).
pose E:=euclidean_cantor_product A A.
pose I:=@integral_geometric_measure R 2 1 (leqnSn 1) +oo.
pose theta:=@orthogonal_projection_probability R 2 1 (leqnSn 1).
pose U:=binary_projection_strict_overlap_locus (real_power 2 (-m^-1)).
have hTheta:is_measure theta:=@theta_star_is_measure R 2 1 (leqnSn 1).
have hU:0<theta U:=@supercritical_original_overlap_positive_probability R m hSuper hm1.
have hNonzero:I E!=0.
  apply/eqP=>hZero.
  have [B [hEB [_ hAE]]]:=(@integral_geometric_projection_null_iff R 2 1 (leqnSn 1) +oo E (leey 1)).1 hZero.
  have hSubset:U `<=` ~` [set p|projected_volume_function (m:=1) B p=0].
    move=>p hp hNull.
    have [hPositive hMass]:=@supercritical_original_overlap_projection_mass R c m A f p hc hm hm1 hPair hp.
    have hPos:0<euclidean_lebesgue_measure 1 (euclidean_projection_linear p @` E)
      by rewrite hMass lte_fin.
    have hImage:euclidean_projection_linear p @` E `<=` euclidean_projection_linear p @` B.
      move=>y [x hx hValue];exists x=>//;exact:hEB x hx.
    have hBound:=measure_mono (@euclidean_lebesgue_is_measure R 1) hImage.
    change (euclidean_lebesgue_measure 1 (euclidean_projection_linear p @` B)=0) in hNull.
    rewrite hNull in hBound.
    have hFalse:=lt_le_trans hPos hBound;by rewrite ltxx in hFalse.
  have hNullU:=@measure_null_subset R _ theta hTheta U _ hSubset hAE.
  by rewrite hNullU ltxx in hU.
case:(pselect ((I E)=(@EPInf R)))=>[hEqual|hNotInfinite];first exact:hEqual.
have hNotEqual:I E!=(@EPInf R) by apply/eqP.
have hFinite:(I E < +oo)%E by rewrite lt_neqAle hNotEqual leey.
have hPure:=@power_cantor_original_square_pure_length R c m (fun _:nat=>2%N) A f hc hm hm1 hPair.
have hNull:=@pure_original_finite_infinity_mass_zero R 2 1 (leqnSn 1) E E hPure
  (fun _ h=>h) hFinite.
change (I E=0) in hNull.
by rewrite hNull eqxx in hNonzero.
Qed.
