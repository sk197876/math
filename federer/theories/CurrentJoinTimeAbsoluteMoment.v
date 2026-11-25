(** Federer (1969), 4.1.11, p. 365: the mass-norm
    scalar factor has the printed factorial time moment.
    The original time measure is concentrated on [0,1],
    where both powers are nonnegative. Outside that band
    the auxiliary absolute value is retained. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom ExtendedRealOrderTopology RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanOneCoordinate CurrentDomain CurrentSpaces CurrentIntegrationCriterion NormalisedCurrentSealed
  CurrentJoinDomain CurrentJoinTimeRepresentation CurrentJoinTimeIntegral
  ScalarUnitMixedPower ScalarBetaCoefficient DistributionIntegrationRepresentationUP
  NormalisedDistributionRepresentationUP PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralAlmostEquality
  MeasureIntegralGraphEquivalence TotalNonnegativeExtendedScaleIntegral SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_unit_mixed_power_nonnegative]: the
    exact scalar time weight is nonnegative on the original
    unit interval, supporting Federer 4.1.11, p. 365. *)
Lemma scalar_unit_mixed_power_nonnegative (R:realType) i j (t:R):
  0<=t<=1->0<=@scalar_unit_mixed_power R i j t.
Proof.
move=>/andP [ht hOne].
have hLeft:0<=1-t by rewrite subr_ge0.
exact:(mulr_ge0 (exprn_ge0 i hLeft) (exprn_ge0 j ht)).
Qed.

Section CurrentJoinTimeAbsoluteMoment.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1%N).
Local Notation Time := (fun _:X=>True).
Local Notation hTime := (fun (t:X) (_:True)=>@norm_full_domain_interior R X
  (inner_norm (@euclidean_inner_productP R 1%N)) t).
Local Notation TT := (current_domain R 1%N Time).
Local Notation I := (@current_join_time_segment R h2).
Variable hI:@is_integration_representable_current R h2 1%N 1%N Time hTime I.
Local Notation alpha := (@NormalisedCurrent.measure R h2 1%N 1%N Time hTime I hI).
Local Notation hAlpha := (distribution_representation_measure (normalised_distribution_representation_laws
  (@NormalisedCurrent.laws R h2 1%N 1%N Time hTime I hI))).
Local Notation q := (fun t:TT=>@euclidean_one_project R (set_val t)).

(** Source for [current_join_time_absolute_beta_moment]: the
    absolute mixed time power has exactly the printed
    factorial moment for the original time-current variation,
    supporting the mass equality in Federer 4.1.11, p. 365. *)
Theorem current_join_time_absolute_beta_moment i j:
  is_measure_integral alpha
    (real_total_integrand (fun t:TT=>`|@scalar_unit_mixed_power R i j (q t)|))
    (@scalar_beta_coefficient R i j)%:E.
Proof.
apply:(measure_integral_almost_equal hAlpha (@current_join_time_beta_moment R h2 hI i j)).
apply:(@measure_almost_everywhere_mono R TT alpha hAlpha _ _ _
  (@current_join_time_band_conull R h2 hI))=>t ht.
exists (@scalar_unit_mixed_power R i j (q t))%:E;split;
  first by rewrite real_total_integrand_graph.
by rewrite real_total_integrand_graph (ger0_norm (scalar_unit_mixed_power_nonnegative i j ht)).
Qed.

(** Source for [current_join_time_extended_beta_moment]:
    any nonnegative extended spatial integral factors out
    of the original time moment, supporting Federer 4.1.11,
    p. 365, including zero and infinite values. *)
Theorem current_join_time_extended_beta_moment i j (c : \bar R):(0<=c)%E->
  is_measure_integral alpha (partial_function_total (fun t:TT=>
    (c*(`|@scalar_unit_mixed_power R i j (q t)|)%:E:extended_real_line R)%E))
    (c*(@scalar_beta_coefficient R i j)%:E)%E.
Proof.
move=>hc.
have hMoment:is_measure_integral alpha (partial_function_total (fun t:TT=>
    (`|@scalar_unit_mixed_power R i j (q t)|)%:E:extended_real_line R))
    (@scalar_beta_coefficient R i j)%:E.
  apply:(@measure_integral_graph_equivalent R TT alpha _ _ _ _
    (current_join_time_absolute_beta_moment i j))=>t z.
  by rewrite real_total_integrand_graph.
apply:(@total_nonnegative_extended_scale_integral R TT alpha hAlpha
  (fun t:TT=>((`|@scalar_unit_mixed_power R i j (q t)|)%:E : extended_real_line R))
  (@scalar_beta_coefficient R i j)%:E c _ hMoment hc)=>t.
rewrite lee_fin;exact:normr_ge0.
Qed.
End CurrentJoinTimeAbsoluteMoment.
