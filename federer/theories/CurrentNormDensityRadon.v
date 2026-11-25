(** Federer (1969), 4.1.7, p. 358:
    gamma restricted by mass(xi) is a Radon
    measure on the original arbitrary open U.
    Finite compact integrals and the earlier compact
    neighbourhood exhaustion prove local finiteness;
    no finiteness near the boundary is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import FiniteCoordinates RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading MetricSubsetBackground CurrentDomain
  CurrentCoefficientNorms OpenCurrentDensityUP CurrentDensityNormMeasurable SmoothDomainCompactOpenCover
  CountableRadonDensity
  PartialFunctionBasic SummableRealFunctionUP MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  PartialExtendedOrderLoci MeasureDensity MeasureIntegralUP MeasureIntegralBounds
  MeasureIntegralUniqueness MeasureSubsetIntegral RadonMeasureUP RadonBorelRegularity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentNormDensityRadon.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation UT := (metric_subset (U:set XT)).
Variable gamma:set UT->\bar R.
Hypothesis hGamma:is_measure gamma.
Hypothesis hRadon:is_radon_measure gamma.
Variable xi:UT->exterior_power X m.
Hypothesis hField:@is_locally_integrable_open_current_density R h2 n m U gamma xi.
Local Notation VN := (@current_vector_mass R h2 n m).
Local Notation H := (real_total_integrand (fun x=>VN (xi x))).
Local Notation lambda := (measure_with_density gamma H).

(** Source for [current_mass_density_nonnegative]:
    the original mass density is nonnegative
    everywhere, supporting Federer 4.1.7, p. 358.
    This uses the actual multivector mass norm. *)
Lemma current_mass_density_nonnegative:
  measure_almost_everywhere gamma (partial_extended_nonnegative_locus H).
Proof.
apply:(@measure_almost_everywhere_mono R UT gamma hGamma
  setT _ _ (measure_almost_everywhere_true hGamma))=>x _.
exists (VN (xi x))%:E; split; first by rewrite real_total_integrand_graph.
rewrite lee_fin; exact:real_seminorm_nonnegative (@current_vector_mass_real_norm R h2 n m).1 (xi x).
Qed.

(** Source for [current_mass_density_compact_finite]:
    finite mass of every original compact K,
    supporting Federer 4.1.7, p. 358. This
    is exactly the printed local integrability
    hypothesis, through the density formula of
    2.4.10, p. 85. *)
Lemma current_mass_density_compact_finite K:compact K->(lambda K< +oo)%E.
Proof.
move=>hK; have [b hb]:=hField.2 K hK.
rewrite (measure_with_density_laws gamma H K) /measure_subset_upper_integral.
have hValue:=@measure_upper_integral_unique R UT gamma _ _ _
  (measure_upper_integral_specification _ _) hb.2.1.
by rewrite hValue ltry.
Qed.

(** Source for [current_mass_density_radon]: the
    original gamma restricted by mass(xi) is
    Radon over U, supporting the exact variation
    formula of Federer 4.1.7, p. 358.
    No unit bound, bounded-set finiteness or whole
    domain integrability is imposed on xi. *)
Theorem current_mass_density_radon:is_radon_measure lambda.
Proof.
have [C [W [hC [hW [hWC [hCover hWCover]]]]]]:=
  @smooth_domain_compact_open_cover R X NX hNX n (@coordinate_basis R n)
    (@coordinate_basisP R n) U hU.
have hMeas:=@current_density_mass_measurable R h2 n m UT gamma hGamma xi hField.1.
exact:(@countable_compact_finite_radon_density R UT gamma lambda hGamma hRadon H C W
  (measure_with_density_laws gamma H) hMeas current_mass_density_nonnegative
  (fun K hK=>@current_mass_density_compact_finite K hK) hC hW hWC hCover hWCover).
Qed.
End CurrentNormDensityRadon.
