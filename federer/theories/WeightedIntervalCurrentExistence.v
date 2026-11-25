(** Federer (1969), 4.1.12, p. 369: the
    actual original weighted interval series exists
    and is flat in its printed
    common compact. Apply the proved
    summable normal-current series theorem to
    the actual 2k^(-2) mass bounds. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import Hom ModuleQuotient RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate
  EuclideanOneNormDifferential CurrentSpaces CurrentMassSealed CurrentFiniteMassLinearBound
  NormalCurrentsUP NormalCurrentSpaces FlatCurrentsUP OrientedSegmentCurrentSealed OrientedSegmentNormal
  OrientedSegmentMass ScalarSegmentCoordinateValues ScalarCurrentIntervalCompact
  NonnegativeSum NonnegativeSumScale NonnegativeSequenceTail ReciprocalPowerSeriesBounds WeightedIntervalEndpoints
  WeightedIntervalCurrentUP CurrentSummableNormalSeries.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section WeightedIntervalCurrentExistence.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1%N).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>
  norm_full_domain_interior (inner_norm (@euclidean_inner_productP R 1%N)) x).
Local Notation C := (@current_space R h2 1%N Full hFull 1%N).
Local Notation K := (weighted_interval_current_compact R).
Local Notation term := (@weighted_interval_current_term R h2).
Local Notation prefix := (@weighted_interval_current_prefix R h2).
Local Notation cost := (weighted_interval_current_mass_cost R).
Local Notation M := (@CurrentMass.value R h2 1%N 1%N Full hFull).

(** Source for [weighted_interval_current_term_normal]:
    every original weighted segment is normal
    and has support in the exact
    printed compact interval, supporting Federer
    4.1.12, p. 369. *)
Theorem weighted_interval_current_term_normal k:
  @normal_currents_supported_in R h2 1%N Full hFull 1%N K (term k).
Proof.
have[hu [huv hvNext]]:=@weighted_interval_endpoint_order R k.
pose Q:=@OrientedSegmentCurrent.value R h2 1%N Full hFull
  (euclidean_one_embed (weighted_interval_left_endpoint R k))
  (euclidean_one_embed (weighted_interval_right_endpoint R k))
  (@scalar_segment_full_domain R (weighted_interval_left_endpoint R k) (weighted_interval_right_endpoint R k)).
have hNormal:@normal_currents_supported_in R h2 1%N Full hFull 1%N K Q.
  split.
  - exact:oriented_segment_current_normal.
  - exact:(@scalar_current_segment_interval_support R h2 0 (weighted_interval_support_endpoint R)
      (weighted_interval_left_endpoint R k) (weighted_interval_right_endpoint R k) hu (ltW huv)
      (le_trans (ltW hvNext) (weighted_interval_left_endpoint_bound R k.+1))).
exact:(@subspace_scale R C (@supported_normal_current_subspace R h2 1%N Full hFull 1%N K)
  (k.+1)%:R Q hNormal).
Qed.

(** Source for [weighted_interval_current_term_mass_upper]:
    the actual original kth weighted
    segment has mass at most 2k^(-2),
    supporting convergence of the series in
    Federer 4.1.12, p. 369.
    A later common calibration proves the exact total. *)
Theorem weighted_interval_current_term_mass_upper k:(M (term k)<=(cost k)%:E)%E.
Proof.
have[_ [huv _]]:=@weighted_interval_endpoint_order R k.
pose Q:=@OrientedSegmentCurrent.value R h2 1%N Full hFull
  (euclidean_one_embed (weighted_interval_left_endpoint R k))
  (euclidean_one_embed (weighted_interval_right_endpoint R k))
  (@scalar_segment_full_domain R (weighted_interval_left_endpoint R k) (weighted_interval_right_endpoint R k)).
have hQM:M Q=(weighted_interval_right_endpoint R k-weighted_interval_left_endpoint R k)%:E.
  rewrite /Q oriented_segment_current_mass euclidean_one_norm_coordinate /euclidean_one_embed !ffunE.
  by rewrite ger0_norm // subr_ge0;exact:ltW huv.
have hBound:=@current_finite_mass_scale_bound R h2 1%N 1%N Full hFull (k.+1)%:R Q
  (weighted_interval_right_endpoint R k-weighted_interval_left_endpoint R k)
  (ltac:(by rewrite hQM)).
rewrite (ger0_norm (ltac:(by rewrite ler0n):0<=((k.+1)%:R:R)))
  weighted_interval_mass_coefficient in hBound.
exact:hBound.
Qed.

(** Source for [weighted_interval_current_mass_cost_finite]:
    the exact original mass-coefficient series
    sum 2k^(-2) is finite, supporting
    Federer 4.1.12, p. 369. *)
Theorem weighted_interval_current_mass_cost_finite:
  (nonnegative_sum setT (fun k=>(cost k)%:E)< +oo)%E.
Proof.
pose a:=reciprocal_power_series_weight R 2%N.
have ha k:(0<=(a k)%:E)%E by rewrite lee_fin;exact:ltW (reciprocal_power_series_weight_positive R 2%N k).
have hFinite:=@reciprocal_square_series_finite R.
have hNumber:nonnegative_sum setT (fun k=>(a k)%:E) \is a fin_num.
  rewrite ge0_fin_numE;last exact:nonnegative_sum_nonnegative.
  exact:hFinite.
have hInput:(fun k=>(cost k)%:E)=(fun k=>(2:R)%:E*(a k)%:E)%E.
  apply:funext=>k;by rewrite /weighted_interval_current_mass_cost EFinM.
rewrite hInput (@nonnegative_sum_scale R nat setT (fun k=>(a k)%:E) 2
  (ltac:(by rewrite ler0n)) (fun k _=>ha k)).
rewrite -(fineK hNumber) -EFinM;exact:ltry.
Qed.

(** Source for [weighted_interval_current_model_exists]:
    the independently specified original series
    has an actual flat value and
    every exact numerical mass-tail bound,
    supporting Federer 4.1.12, p. 369. *)
Theorem weighted_interval_current_model_exists:
  exists S:C,@is_weighted_interval_current_series R h2 S /\
    @is_flat_current_supported_in R h2 1%N 1%N Full hFull K S /\
    forall k,(M (S-prefix k)<=nonnegative_sequence_tail (fun j=>(cost j)%:E) k)%E.
Proof.
have hCost k:0<=cost k.
  apply:mulr_ge0;first by rewrite ler0n.
  exact:ltW (reciprocal_power_series_weight_positive R 2%N k).
have[S [hFlat [hWeak hTail]]]:=@current_summable_normal_series_exists R h2 1%N 1%N Full hFull K
  term cost weighted_interval_current_term_normal hCost weighted_interval_current_mass_cost_finite
  weighted_interval_current_term_mass_upper.
exists S;split;first exact:hWeak.
by split.
Qed.

(** Source for [weighted_interval_current_series_exists]:
    the literal original testwise current
    series of Federer 4.1.12, p. 369, exists. *)
Theorem weighted_interval_current_series_exists:exists S:C,@is_weighted_interval_current_series R h2 S.
Proof. have[S [hS _]]:=weighted_interval_current_model_exists;by exists S. Qed.
End WeightedIntervalCurrentExistence.
