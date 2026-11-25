(** Federer (1969), 4.1.12, p. 369: the
    actual original sum S has mass
    exactly 2 sum k^(-2), which is
    finite. One actual coordinate test
    calibrates every positive weighted interval;
    the proved numerical tails give the upper bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate CurrentSpaces
  CurrentMassSealed SmoothCompactSet NonnegativeSum NonnegativeSumScale ReciprocalPowerSeriesBounds
  WeightedIntervalEndpoints WeightedIntervalCurrentUP WeightedIntervalCurrentExistence WeightedIntervalCurrentSealed
  WeightedIntervalCurrentLaws ScalarCurrentCalibrationTest ScalarSegmentCalibration CurrentCalibratedSeriesMass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section WeightedIntervalCurrentMass.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1%N).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>
  norm_full_domain_interior (inner_norm (@euclidean_inner_productP R 1%N)) x).
Local Notation S := (@WeightedIntervalCurrent.value R h2).
Local Notation M := (@CurrentMass.value R h2 1%N 1%N Full hFull).
Local Notation cost := (weighted_interval_current_mass_cost R).

(** Source for [weighted_interval_current_mass_series]:
    the original S has mass equal
    to the sum of its exact positive
    interval masses, supporting the printed
    identity in Federer 4.1.12, p. 369. *)
Theorem weighted_interval_current_mass_series:
  M S=nonnegative_sum setT (fun k=>(cost k)%:E).
Proof.
have[phi [hUnit hCoordinate]]:=@scalar_current_calibration_test_exists R h2 0
  (weighted_interval_support_endpoint R).
have hCost k:0<=cost k.
  apply:mulr_ge0;first by rewrite ler0n.
  exact:ltW (reciprocal_power_series_weight_positive R 2%N k).
have hAction k:@current_value R h2 1%N Full hFull 1%N
    (@weighted_interval_current_term R h2 k) phi=cost k.
  rewrite /weighted_interval_current_term
    (linZ (hom_linear (@current_value R h2 1%N Full hFull 1%N))) hom_scaleE.
  have[hu [huv hvNext]]:=@weighted_interval_endpoint_order R k.
  rewrite (@scalar_segment_calibration_value R h2 0 (weighted_interval_support_endpoint R)
    (weighted_interval_left_endpoint R k) (weighted_interval_right_endpoint R k) phi
    hu (ltW huv) (le_trans (ltW hvNext) (weighted_interval_left_endpoint_bound R k.+1)) hCoordinate).
  exact:weighted_interval_mass_coefficient.
exact:(@current_calibrated_series_mass R h2 1%N 1%N Full hFull
  (@weighted_interval_current_term R h2) S cost phi hCost
  (@weighted_interval_current_mass_cost_finite R) (fun x _=>hUnit x)
  hAction (@WeightedIntervalCurrent.laws R h2) (@weighted_interval_current_flat_and_tails R h2).2).
Qed.

(** Source for [weighted_interval_current_mass]: the
    literal printed identity M(S)=2 sum
    k^(-2), Federer 4.1.12, p. 369. *)
Theorem weighted_interval_current_mass:
  M S=((2:R)%:E*nonnegative_sum setT
    (fun k=>(reciprocal_power_series_weight R 2%N k)%:E))%E.
Proof.
rewrite weighted_interval_current_mass_series.
have hInput:(fun k=>(cost k)%:E)=
    (fun k=>(2:R)%:E*(reciprocal_power_series_weight R 2%N k)%:E)%E.
  apply:funext=>k;by rewrite /weighted_interval_current_mass_cost EFinM.
rewrite hInput;apply:nonnegative_sum_scale;first by rewrite ler0n.
move=>k _;rewrite lee_fin;exact:ltW (reciprocal_power_series_weight_positive R 2%N k).
Qed.

(** Source for [weighted_interval_current_finite_mass]:
    the original S has finite mass,
    exactly as in Federer 4.1.12, p. 369. *)
Corollary weighted_interval_current_finite_mass:(M S< +oo)%E.
Proof. rewrite weighted_interval_current_mass_series;exact:weighted_interval_current_mass_cost_finite. Qed.
End WeightedIntervalCurrentMass.
