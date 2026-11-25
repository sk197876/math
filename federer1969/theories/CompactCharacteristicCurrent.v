(** Federer (1969), 4.1.23, pp. 379–380:
    the actual current of a measurable
    cell and a constant multivector has
    its exact original mass and compact
    support. In degree zero its total
    is exactly the cell's Lebesgue measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct ExteriorGrading ExteriorPowers AlternatingForms AlternatingZero
  AlternatingPairing CurrentDomain CurrentSpaces CurrentCoefficientNorms
  CurrentCharacteristicDensity CurrentDensityAction CurrentDensityUniqueness
  CurrentDiracDensity CurrentZeroDegreeExteriorLaws CurrentSupportGeometry TopologicalBorel
  CurrentMassSealed CurrentIntegrationCriterion CurrentFiniteMassRepresentation
  NormalCurrentsUP CurrentCompactSmoothValue
  CurrentCompactSmoothAgreement CurrentScalarCutoffs SmoothCompactSet
  EuclideanLebesgueDimensions EuclideanDistributionMeasureContext
  CompactCharacteristicSummableField CompactSummableAmbientFieldLift
  CompactSummableMultivectors CompactSummableMultivectorAmbient
  CompactSummableMultivectorDensity CompactSummableMultivectorSupport
  CompactSummableFullCurrentAction MeasureUP MeasureBasic MeasureIntegralUP
  MeasureIntegralUniqueness MeasureCharacteristicIntegral SummableRealFunctionUP
  CharacteristicFunctionUP CharacteristicFunctionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CharacteristicCurrent.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) => norm_full_domain_interior NX x).
Local Notation FT := (current_domain R n Full).
Local Notation V := (exterior_power X m).
Local Notation VN := (@current_vector_mass R h2 n m).
Local Notation hVN := (@current_vector_mass_real_norm R h2 n m).
Local Notation Leb := (@euclidean_lebesgue_measure R n).
Local Notation hLeb := (euclidean_lebesgue_is_measure R n).
Variable A : set X.
Hypothesis hA : measure_measurable Leb A.
Variable z : V.
Local Notation T := (@current_characteristic_density R h2 n m Leb hLeb
  (@euclidean_distribution_measure_borel R n)
  (@euclidean_distribution_measure_compact_finite R n) A hA z).

(** Source for [compact_characteristic_current_properties]:
    M(Lebesgue^n restricted to A wedge z)
    equals mass(z) times Lebesgue^n(A),
    the exact cost retained in Federer
    4.1.23, pp. 379–380. The original
    measurable A need not be closed;
    its containing compact gives the support bound. *)
Theorem compact_characteristic_current_properties
    (K : smooth_compact_set hNX Full) (hAK : A `<=` smooth_compact_carrier K) :
  @CurrentMass.value R h2 n m Full hFull T=((VN z)%:E*Leb A)%E /\
    @current_support R h2 n Full hFull m T `<=` smooth_compact_carrier K.
Proof.
have hFinite : (Leb A< +oo)%E.
  apply: (le_lt_trans (@measure_mono R X Leb hLeb A (smooth_compact_carrier K) hAK)).
  exact: (@euclidean_distribution_measure_compact_finite R n _
    (smooth_compact_is_compact K)).
have [f [hF [hSize hOff]]] := @compact_characteristic_summable_field_exists R XT V VN hVN
  Leb hLeb A hA hFinite (smooth_compact_carrier K) (smooth_compact_is_compact K) hAK z.
have [xi [hRaw hXiSize]] := @compact_summable_ambient_field_lift R h2 n m f.
pose image := @compact_summable_multivector_current R h2 n m Full hFull xi.
have hAction := @compact_summable_full_current_action R h2 n m xi.
have hFunction : @compact_summable_multivector_ambient_value R h2 n m Full hFull xi=
    (fun x => @CharacteristicFunction.value R X A x*:z).
  rewrite hRaw; apply: funext=> x; exact: (@hF x).
rewrite hFunction in hAction.
have hEqual : T=image.
  apply: (@current_density_action_unique R h2 n m Leb
    (fun x => @CharacteristicFunction.value R X A x*:z)).
  - exact: (@current_characteristic_density_action R h2 n m Leb hLeb
      (@euclidean_distribution_measure_borel R n)
      (@euclidean_distribution_measure_compact_finite R n) A hA z).
  - exact: hAction.
have hXiOff (x : FT) : ~smooth_compact_carrier K (set_val x) ->
    @compact_summable_multivector_value R h2 n m Full hFull xi x=0.
  move=> hx.
  rewrite -(@compact_summable_multivector_ambient_inside R h2 n m Full hFull xi x)
    hRaw; exact: (@hOff (set_val x) hx).
split.
- rewrite hEqual /image compact_summable_multivector_current_mass hXiSize.
  exact: hSize.
- rewrite hEqual; exact: (@compact_summable_multivector_current_support R h2 n m
    Full hFull xi K hXiOff).
Qed.
End CharacteristicCurrent.

Section CharacteristicZeroCurrent.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) => norm_full_domain_interior NX x).
Local Notation Leb := (@euclidean_lebesgue_measure R n).
Local Notation hLeb := (euclidean_lebesgue_is_measure R n).
Local Notation unit := (@current_scalar_multivector_unit R n).
Variable A : set X.
Hypothesis hA : measure_measurable Leb A.
Local Notation T := (@current_characteristic_density R h2 n 0%N Leb hLeb
  (@euclidean_distribution_measure_borel R n)
  (@euclidean_distribution_measure_compact_finite R n) A hA unit).

(** Source for [compact_characteristic_zero_current_properties]:
    S_k=Lebesgue^(n-m) restricted to B_k
    is a normal zero-current with
    M(S_k)=S_k(1)=Lebesgue^(n-m)(B_k),
    Federer 4.1.23, p. 380.
    The smooth total accepts every actual
    compactness witness; no negative boundary is used. *)
Theorem compact_characteristic_zero_current_properties
    (K : smooth_compact_set hNX Full) (hAK : A `<=` smooth_compact_carrier K) :
  @normal_currents_supported_in R h2 n Full hFull 0%N K T /\
    @CurrentMass.value R h2 n 0%N Full hFull T=Leb A /\
    forall hCompact, @current_compact_total R h2 n Full hFull T hCompact=fine (Leb A).
Proof.
have [hMass hSupport] := @compact_characteristic_current_properties R h2 n 0%N A hA unit K hAK.
rewrite /current_scalar_multivector_unit current_vector_mass_zeroth_scalar normr1 mul1e in hMass.
have hCompact := @current_support_compact_bound R h2 n 0%N Full hFull K T hSupport.
have hRepresentable : @is_integration_representable_current R h2 n 0%N Full hFull T.
  have hFinite : (@CurrentMass.value R h2 n 0%N Full hFull T< +oo)%E.
    rewrite hMass; apply: (le_lt_trans (@measure_mono R X Leb hLeb A
      (smooth_compact_carrier K) hAK)).
    exact: (@euclidean_distribution_measure_compact_finite R n _
      (smooth_compact_is_compact K)).
  exact: current_finite_mass_representation hFinite.
split; first exact: conj (conj (conj hRepresentable Logic.I) hCompact) hSupport.
split; first exact: hMass.
move=> hOther.
have [gamma [W [hW [hKW [hWFull hOne]]]]] := @current_compact_scalar_cutoff R h2 n
  Full hFull K.
have hAction := @current_characteristic_density_action R h2 n 0%N Leb hLeb
  (@euclidean_distribution_measure_borel R n)
  (@euclidean_distribution_measure_compact_finite R n) A hA unit gamma.
have hIntegrand : (fun x => pairing (@CharacteristicFunction.value R X A x*:unit)
    (@current_test_value R h2 n Full hFull 0%N gamma x))=
    (@CharacteristicFunction.value R X A).
  apply: funext=> x; rewrite (bilZl (@pairing_bilinear R X R^o 0%N))
    current_scalar_multivector_unit_pairing.
  case: (pselect (A x))=> hx.
  - by rewrite (@hOne x (@hKW x (@hAK x hx))) zero_formK
      (characteristic_on_set (@CharacteristicFunction.laws R X A) hx) scale1r.
  - by rewrite (characteristic_off_set (@CharacteristicFunction.laws R X A) hx) scale0r.
rewrite hIntegrand in hAction.
have hIntegral := @measure_characteristic_integral R X Leb hLeb A
  (@CharacteristicFunction.value R X A) (@CharacteristicFunction.laws R X A) hA.
have hValue : @current_value R h2 n Full hFull 0%N T gamma=fine (Leb A).
  have hFine := congr1 (@fine R) (measure_integral_unique hAction hIntegral).
  exact hFine.
have hTotal := @current_compact_total_cutoff R h2 n Full hFull T hOther gamma W hW
  (subset_trans hSupport hKW) hWFull hOne.
exact: eq_trans (esym hTotal) hValue.
Qed.
End CharacteristicZeroCurrent.
