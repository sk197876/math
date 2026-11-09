(** Federer (1969), 3.3.20, p. 307: actual full projections throughout the supercritical open family. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground EuclideanInnerProduct InnerMetric EuclideanRealPlane
  EuclideanCantorProduct PowerCantorPairUP BinaryCantorSquareLevelsUP BinaryCantorFullIntervalProjection
  EuclideanProjectionSpace EuclideanOneCoordinate EuclideanLebesgueDimensions EuclideanScalarLength
  PlanarProjectionCoefficientLaws SupercriticalProjectionOpen LebesgueScalarMeasure RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [supercritical_original_overlap_projection_mass]: each
    actual original direction in the strict overlap family has projected
    volume u_1+u_2>0 on the original E, 3.3.20, p. 307. The original
    compact-limit interval theorem and exact scalar/Euclidean measure
    compatibility prove the mass, without a supplied image premise. *)
Theorem supercritical_original_overlap_projection_mass (R:realType) (c m:R)
    (A:set (real_line_metric R)) (f:R->R) (p:euclidean_projection_space R 2 1):
  0<c ->0<m ->m<1 ->is_power_cantor_pair c m (fun _:nat=>2%N) A f ->
  binary_projection_strict_overlap_locus (real_power 2 (-m^-1)) p ->
  let u:=planar_projection_first_coefficient p in
  let v:=planar_projection_second_coefficient p in
  0<u+v /\euclidean_lebesgue_measure 1
    (euclidean_projection_linear p @` euclidean_cantor_product A A)=(u+v)%:E.
Proof.
move=>hc hm hm1 [J [H [hJ [hTree [hA _]]]]] [hv [hVU [hMiddle hSide]]] u v.
change (is_true (0<v)) in hv.
change (is_true (v<u)) in hVU.
change (is_true ((1-2 * real_power 2 (-m^-1)) * u<v)) in hMiddle.
change (is_true ((1-2 * real_power 2 (-m^-1)) * v<real_power 2 (-m^-1) * u)) in hSide.
have hu:0<u:=lt_trans hv hVU.
have hSum:0<u+v by lra.
have [G hG]:=binary_cantor_square_levels_exist H.
have hFull:=@binary_original_cantor_square_full_interval_projection R c m u v J H G A
  hc hm hm1 hu (ltW hv) (ltW hVU) hJ hTree hA hG (ltW hMiddle) (ltW hSide).
have [_ hFormula]:=planar_projection_actual_coefficient_laws p.
split;first exact:hSum.
rewrite euclidean_one_measure_scalar_image image_comp.
have hFunction:(fun x:inner_metric_space (@euclidean_inner_productP R 2)=>
    euclidean_one_project (euclidean_projection_linear p x))=
    (fun x:inner_metric_space (@euclidean_inner_productP R 2)=>
      u * euclidean_real_plane_first x+v * euclidean_real_plane_second x)
  by apply:funext=>x;exact:hFormula x.
change (lebesgue_scalar_measure
  ((fun x:inner_metric_space (@euclidean_inner_productP R 2)=>
    euclidean_one_project (euclidean_projection_linear p x)) @` euclidean_cantor_product A A)=(u+v)%:E).
by rewrite hFunction hFull (lebesgue_scalar_segment (ltW hSum)) subr0.
Qed.
