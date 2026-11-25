(** Federer (1969), 4.1.7, p. 358:
    the original variation of E^n is
    exactly Lebesgue measure, including dimension zero.
    Its existing density current is compared
    with the original full-domain Radon construction;
    the general exact variation formula then applies. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import CurrentEvaluation Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct ExteriorGrading FiniteExteriorPowers
  AlternatingForms AlternatingPairing CurrentDomain CurrentCoefficientNorms CurrentSpaces CurrentMultivectorDual
  MultivectorDualSealed CurrentIntegrationCriterion NormalisedCurrentSealed EuclideanTopCurrentMass
  EuclideanFundamentalCurrent EuclideanFullDomainMeasure OpenCurrentDensityUP OpenCurrentDensitySealed
  CurrentDensityVariation CurrentNormDensityRadon BoundedCurrentDensityUniqueness BoundedBaireFieldLocalIntegral
  CurrentMeasurableMultiplierUP SmoothFunctionSpaceUP SmoothTestEvaluation DistributionVariationDomain
  DistributionIntegralFieldUP DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  OpenFamilyTopologyMathcomp BaireFunctions PartialFunctionBasic MeasureUP MeasureAlmostUP
  MeasurableFunctionUP MeasurableTotalBasic MeasureIntegralUP MeasureIntegralUniqueness SummableRealFunctionUP
  MeasureDensityUP MeasureDensity MeasurePushforward EuclideanLebesgueDimensions
  RealFiniteDensityIntegral BorelRegularMeasureUP RadonBorelRegularity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section EuclideanFundamentalCurrentVariation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation U := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X NX x).
Local Notation FT := (current_domain R n U).
Local Notation Y := (A_m X R^o n).
Local Notation NY := (@current_form_comass R h2 n n).
Local Notation hNY := (@current_form_comass_real_norm R h2 n n).
Local Notation D := (exterior_power X n).
Local Notation DN := (@current_vector_mass R h2 n n).
Local Notation hDN := (@current_vector_mass_real_norm R h2 n n).
Local Notation ed := (@MultivectorDual.evaluation R X n).
Local Notation hE := (@current_smooth_space_laws R h2 n U hFull n).
Local Notation DT := (@current_test_space R h2 n U hFull n).
Local Notation dvalues := (@distribution_domain_values R (real_norm_metric_space hNX) U Y DT
  (smooth_test_values_hom hE)).
Local Notation E := (@euclidean_fundamental_current R h2 n).
Local Notation top := (e_lambda (@coordinate_basis R n) (ord_tuple n)).
Local Notation xi := (fun _:FT=>top).
Local Notation gamma := (@euclidean_full_domain_measure R n).
Let hm:=(@euclidean_full_domain_measure_laws R n).1.
Let hr:=(@euclidean_full_domain_measure_laws R n).2.
Let hWeak:is_measure_measurable_function gamma
  (partial_function_total (fun x:FT=>(top:open_family_topological_space
    (@current_multivector_weak_laws R n n).1))):=
  @measurable_total_constant R FT (open_family_topological_space
    (@current_multivector_weak_laws R n n).1) gamma hm top.
Let hLocal:is_locally_summable_current_field hDN gamma xi.
Proof.
apply:(@bounded_baire_field_locally_summable R FT D DN hDN gamma hm hr xi 1).
- apply:(@continuous_baire_function R FT (real_norm_metric_space hDN) xi).
  move=>x.
  exact (@cvg_cst [the topologicalType of real_norm_metric_space hDN] top FT _
    (@nbhs_filter FT x)).
- exact:ler01.
- by move=>x;rewrite (@euclidean_top_current_vector_mass_one R h2 n).
Qed.
Let hField:@is_locally_integrable_open_current_density R h2 n n U gamma xi:=conj hWeak hLocal.2.
Local Notation C := (@OpenCurrentDensity.value R h2 n n U hFull gamma hm hr xi hField).

(** Source for [euclidean_fundamental_current_radon_representation]:
    the actual original E^n has the
    constant coordinate orientation under the actual
    full-domain Lebesgue measure, supporting Federer
    4.1.7, pp. 357–358. Every original
    test is retained. *)
Theorem euclidean_fundamental_current_radon_representation:
  @is_current_integration_representation R h2 n n U hFull E gamma xi.
Proof.
constructor;[exact:hm|exact:hr|exact:hWeak|exact:hLocal.2|].
move=>phi.
have hOriginal:=@euclidean_fundamental_current_action R h2 n phi.
have hIntegral:=@euclidean_full_domain_real_integral R n
  (fun x=>pairing top (@current_test_value R h2 n U hFull n phi x)) _ hOriginal.
have hValues:(fun x:FT=>pairing top (@current_test_value R h2 n U hFull n phi (set_val x)))=
    (fun x=>ed top (dvalues phi x)).
  by apply:funext=>x;rewrite MultivectorDual.laws.
by rewrite hValues in hIntegral.
Qed.

(** Source for [euclidean_fundamental_current_representable]:
    the original E^n is representable by
    integration, supporting Federer 4.1.7,
    pp. 357–358, in every dimension. *)
Theorem euclidean_fundamental_current_representable:
  @is_integration_representable_current R h2 n n U hFull E.
Proof. exists gamma,xi;exact:euclidean_fundamental_current_radon_representation. Qed.

(** Source for [euclidean_fundamental_current_open_density]:
    the existing original E^n is the
    same actual current as the arbitrary-open
    Radon density constructor, supporting application
    of the exact variation theorem in
    Federer 4.1.7, p. 358. *)
Theorem euclidean_fundamental_current_open_density:E=C.
Proof.
have hC:=@OpenCurrentDensity.laws R h2 n n U hFull gamma hm hr xi hField.
apply:(@current_values_extensional R h2 n n U hFull)=>phi.
exact:(EFin_inj (measure_integral_unique
  (distribution_representation_action euclidean_fundamental_current_radon_representation phi)
  (distribution_representation_action hC phi))).
Qed.

(** Source for [euclidean_fundamental_current_variation]:
    ||E^n|| is exactly original Lebesgue
    measure on its full original current
    domain, Federer 4.1.7, p. 358.
    No exceptional set or normalization factor
    occurs, including at n=0. *)
Theorem euclidean_fundamental_current_variation
    (hT:@is_integration_representable_current R h2 n n U hFull E):
  @NormalisedCurrent.measure R h2 n n U hFull E hT=gamma.
Proof.
pose mu:=@NormalisedCurrent.measure R h2 n n U hFull E hT.
pose eta:=@NormalisedCurrent.auxiliary_density R h2 n n U hFull E hT.
have hR:=@NormalisedCurrent.laws R h2 n n U hFull E hT.
have hC:@is_normalised_current_representation R h2 n n U hFull C mu eta.
  by rewrite -euclidean_fundamental_current_open_density.
have hVariation:=@current_density_exact_variation R h2 n n U hFull gamma hm hr xi hField mu eta hC.
have hDensity:is_measure_density gamma (real_total_integrand (fun _:FT=>1)) mu.
  rewrite hVariation.
  have hWeight:(fun x:FT=>DN (xi x))=(fun _=>1).
    apply:funext=>x;exact:(@euclidean_top_current_vector_mass_one R h2 n).
  rewrite -hWeight;exact:measure_with_density_laws.
have hRegular:=borel_regular_is_regular hm (radon_borel_regular hm hr).
apply:funext=>A;exact:(@regular_measure_unit_density_value R FT gamma mu hm hRegular hDensity A).
Qed.

(** Source for [euclidean_fundamental_current_variation_ambient]:
    on the original ambient R^n the
    variation measure is precisely Lebesgue measure,
    Federer 4.1.7, p. 358. The
    canonical domain inclusion changes no point. *)
Theorem euclidean_fundamental_current_variation_ambient
    (hT:@is_integration_representable_current R h2 n n U hFull E):
  MeasurePushforward.measure_pushforward (set_val:FT->X)
    (@NormalisedCurrent.measure R h2 n n U hFull E hT)=@EuclideanLebesgueDimensions.euclidean_lebesgue_measure R n.
Proof. rewrite euclidean_fundamental_current_variation;exact:euclidean_full_domain_measure_ambient. Qed.

(** Source for [euclidean_fundamental_current_auxiliary_constant]:
    the original normalized auxiliary density
    agrees almost everywhere with the coordinate
    top vector, supporting the everywhere original
    orientation in Federer 4.1.7, p. 358.
    The everywhere conclusion is proved separately
    from the literal original ball quotients. *)
Theorem euclidean_fundamental_current_auxiliary_constant
    (hT:@is_integration_representable_current R h2 n n U hFull E):
  MeasureAlmostUP.measure_almost_everywhere (@NormalisedCurrent.measure R h2 n n U hFull E hT)
    [set x:FT|@NormalisedCurrent.auxiliary_density R h2 n n U hFull E hT x=top].
Proof.
pose mu:=@NormalisedCurrent.measure R h2 n n U hFull E hT.
pose eta:=@NormalisedCurrent.auxiliary_density R h2 n n U hFull E hT.
have hR:=@NormalisedCurrent.laws R h2 n n U hFull E hT.
have hBase:=normalised_distribution_representation_laws hR.
have hMu:=distribution_representation_measure hBase.
have hRadon:=distribution_representation_radon hBase.
have hXi:is_measure_measurable_function mu
    (partial_function_total (fun x:FT=>(top:open_family_topological_space
      (@current_multivector_weak_laws R n n).1))).
  exact:(@measurable_total_constant R FT (open_family_topological_space
    (@current_multivector_weak_laws R n n).1) mu hMu top).
have hXiBound x:DN (xi x)<=1 by rewrite (@euclidean_top_current_vector_mass_one R h2 n).
have hXiAction:is_distribution_integral_action mu ed xi dvalues (@current_value R h2 n U hFull n E).
  rewrite /mu euclidean_fundamental_current_variation.
  exact:distribution_representation_action euclidean_fundamental_current_radon_representation.
exact:(@bounded_current_density_almost_unique R h2 n n U hFull mu hMu hRadon eta xi
  (distribution_representation_weak_measurable hBase) hXi
  (normalised_distribution_density_unit_bound hR) hXiBound (@current_value R h2 n U hFull n E)
  (distribution_representation_action hBase) hXiAction).
Qed.
End EuclideanFundamentalCurrentVariation.
