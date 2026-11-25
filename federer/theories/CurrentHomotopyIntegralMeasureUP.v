(** Federer (1969), 4.1.9, p. 363: the original
    integral of weighted slice image measures. Its
    independent specification uses Radon laws and the
    literal time integrals of positive compact scalar
    tests. The weighted product image proves existence;
    downstream variation bounds use the opaque public law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentDomain CurrentSpaces CurrentHomotopyUP
  CurrentIntegrationCriterion CurrentHomotopySliceMeasureIntegral CurrentHomotopyCylinder
  MeasureUP RadonMeasureUP MeasureIntegralUP MeasureIntegralUniqueness MeasureSubsetIntegral
  LebesgueScalarMeasure RealMetricBackground SummableRealFunctionUP FunctionLatticeUP CompactSupportFunctionUP
  CurrentHomotopyTimePartialIntegral RadonCompactScalarIntegral RadonPositiveCompactUniqueness RealIntegralFunctionalUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section CurrentHomotopyIntegralMeasure.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu j:nat.
Variable A:set R.
Variables (U:set (R_n R n)) (V:set (R_n R nu)).
Variables (f g:R_n R n->R_n R nu) (h:R_n R (1+n)%N->R_n R nu).
Hypothesis hHomotopy:@is_smooth_current_homotopy R n nu A U V f g h.
Local Notation hU := (@current_homotopy_source_open R n nu A U V f g h hHomotopy.1).
Variable T:@current_space R h2 n U hU j.
Hypothesis hT:@is_integration_representable_current R h2 n j U hU T.
Local Notation VT := (current_domain R nu V).
Local Notation Kplus := (positive_function_lattice (@compactly_supported_continuous_functions R VT)).
Local Notation Integrand phi := (@current_homotopy_slice_measure_integrand R h2 n nu j A U V f g h hHomotopy T hT phi).
Local Notation TimeIntegrand phi := (@current_homotopy_scalar_time_integrand R A (Integrand phi)).
Local Notation TimeIntegral phi b := (is_measure_subset_integral (@lebesgue_scalar_measure R)
  (`[0,1]:set (real_line_metric R)) (TimeIntegrand phi) b).

(** Source for [is_current_homotopy_integral_measure]: the
    Radon measure denoted by the original integral of
    slice image measures in Federer 4.1.9, p. 363,
    is specified by its literal time integral on
    every positive compact scalar test. No variation
    inequality or existence assertion is assumed here. *)
Record is_current_homotopy_integral_measure (mu:set VT->\bar R):Prop:={
  (** Source for [homotopy_integral_measure_laws]: the original
      integral is a measure, supporting the final
      inequality in Federer 4.1.9, p. 363. *)
  homotopy_integral_measure_laws:is_measure mu;
  (** Source for [homotopy_integral_measure_radon]: the original
      measure integral is Radon under the printed
      properness hypothesis, supporting Federer 4.1.9, p. 363. *)
  homotopy_integral_measure_radon:is_radon_measure mu;
  (** Source for [homotopy_integral_measure_scalar_tests]: the
      exact literal time integral on each positive
      compact scalar test specifies the original measure
      integral in Federer 4.1.9, p. 363. *)
  homotopy_integral_measure_scalar_tests:forall phi,Kplus phi->exists b:R,
    is_measure_integral mu (real_total_integrand phi) b%:E /\TimeIntegral phi b%:E
}.

(** Source for [current_homotopy_integral_measure_unique]: the
    original Radon integral of slice image measures
    is determined on every set by its positive
    compact scalar tests, supporting Federer 4.1.9,
    p. 363, through the preceding 4.1.7 uniqueness
    law and 2.5.14, p. 107. *)
Theorem current_homotopy_integral_measure_unique mu rho:
  is_current_homotopy_integral_measure mu->is_current_homotopy_integral_measure rho->mu=rho.
Proof.
move=>hMu hNu.
pose hm:=homotopy_integral_measure_laws hMu.
pose hn:=homotopy_integral_measure_laws hNu.
pose hr:=homotopy_integral_measure_radon hMu.
pose hs:=homotopy_integral_measure_radon hNu.
pose F:=@radon_positive_compact_integral R VT mu hm hr.
have hF:=@radon_positive_compact_integral_laws R VT mu hm hr.
have hG:is_real_integral_functional rho Kplus F.
  move=>phi hPhi.
  have[b [hMb hTimeB]]:=homotopy_integral_measure_scalar_tests hMu hPhi.
  have[c [hNc hTimeC]]:=homotopy_integral_measure_scalar_tests hNu hPhi.
  have hCanonical:=measure_integral_unique (hF phi hPhi) hMb.
  have hTime:=measure_integral_unique hTimeB hTimeC.
  by rewrite hCanonical hTime.
apply:funext=>B;exact:(@radon_positive_compact_integral_unique R VT mu rho hm hn hr hs F hF hG B).
Qed.
End CurrentHomotopyIntegralMeasure.
