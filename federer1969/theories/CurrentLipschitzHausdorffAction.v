(** Federer (1969), 4.1.25, p. 383: the
    actual Lipschitz image of the original compact
    summable Lebesgue-density current has the exact
    Hausdorff-density action of the full-fibre sum.
    Apply the first displayed action and the weighted
    area formula to every original compact target test.
    No normality or Radon hypothesis on ambient H^m
    enters this identification. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness ExteriorGrading AlternatingForms AlternatingPairing
  CurrentSpaces CurrentDensityAction CurrentCoefficientNorms
  CompactSummableMultivectors CompactSummableMultivectorDensity
  CompactSummableMultivectorAmbient LipschitzUP LipschitzBasic
  CurrentFlatLipschitzPushforwardSealed CurrentLipschitzLebesgueActionDensity
  CurrentLipschitzLebesgueAction CurrentAreaNormalisedImageSealed
  CurrentAreaFibreDensitySealed CurrentAreaFibreDensityMeasurable
  CurrentAreaPairingQuotientTestArea CurrentAreaPairingQuotientTestFibreGraph
  HausdorffMeasure MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralAlmostEquality
  MeasurableFunctionUP PartialFunctionUP PartialFunctionExtensionUP
  SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section HausdorffAction.
Variable R : realType.
Hypothesis h2 : (1+1 : R) != 0.
Variables m n : nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation FullX := (fun _ : X => True).
Local Notation FullY := (fun _ : Y => True).
Local Notation hFullX := (fun (x : X) (_ : True) => norm_full_domain_interior NX x).
Local Notation hFullY := (fun (y : Y) (_ : True) => norm_full_domain_interior NY y).
Variable xi : @compact_summable_multivector_space R h2 m m FullX hFullX.
Local Notation raw := (@compact_summable_multivector_ambient_value R h2 m m FullX hFullX xi).
Local Notation T := (@compact_summable_multivector_current R h2 m m FullX hFullX xi).
Local Notation hFlat := (@current_lipschitz_lebesgue_action_density_flat R h2 m m FullX hFullX xi).
Variable f : X -> Y.
Hypothesis hLip : @is_metric_lipschitz R
  (inner_metric_space (@euclidean_inner_productP R m))
  (inner_metric_space (@euclidean_inner_productP R n)) setT f.
Local Notation hLocal := (@metric_lipschitz_is_local R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) setT f hLip).
Local Notation hImage := (fun (x : X) (_ : True) => Logic.I).
Local Notation Q := (@CurrentFlatLipschitzPushforward.value R h2 m n m
  FullX FullY hFullX hFullY f hImage hLocal T hFlat).
Local Notation H := (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m).
Local Notation u := (@CurrentAreaNormalisedImage.value R m n f raw).
Local Notation eta := (@CurrentAreaFibreDensity.value R h2 X n m f u).

(** Source for [current_lipschitz_hausdorff_action]: the
    literal current equality f_#(L^m wedge xi)=H^m wedge eta
    in Federer 4.1.25, p. 383, expressed by
    the independently specified original density action.
    Every graph-preserving total target representative gives
    this same current on every actual compact test. *)
Theorem current_lipschitz_hausdorff_action
    (w : Y -> exterior_power Y m) :
  is_partial_function_total_extension eta w ->
  @is_current_density_action R h2 n m H w Q.
Proof.
move=> hW psi.
have hLeb := @current_lipschitz_lebesgue_action R h2 m n m xi f hLip psi.
have [b [hSource hTarget]] := @current_area_pairing_quotient_test_area_integrals
  R h2 m n f hLip xi psi.
have hValue : b%:E = (@current_value R h2 n FullY hFullY m Q psi)%:E :=
  measure_integral_unique hSource hLeb.
rewrite hValue in hTarget.
apply: (measure_integral_almost_equal
  (@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
  hTarget).
have hDomain := measurable_function_domain
  (@current_area_fibre_density_measurable R h2 m n xi f hLip).
apply: (measure_almost_everywhere_mono
  (@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
  _ hDomain) => y [v hEta].
exists (pairing v (@current_test_value R h2 n FullY hFullY m psi y))%:E; split.
- exact: (@current_area_pairing_quotient_test_original_fibre_value R m n f raw
    (@current_test_value R h2 n FullY hFullY m psi) y v
    ((@CurrentAreaFibreDensity.laws R h2 X n m f u y v).1 hEta)).
- apply/real_total_integrand_graph; by rewrite (hW y v hEta).
Qed.
End HausdorffAction.
