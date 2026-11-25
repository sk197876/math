(** Federer (1969), 4.1.11, p. 365: the source
    measure is exactly the original three-factor product.
    The opaque coordinate bijections, exact time-product
    variation and preceding partial-domain Fubini theorem
    supply the literal x,t,y repeated integral. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom ExtendedRealOrderTopology RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanCartesianMap CurrentDomain CurrentSpaces CurrentIntegrationCriterion NormalisedCurrentSealed
  CurrentCartesianDomain CurrentCartesianDomainMapsSealed CurrentCartesianMeasureRadon
  CurrentCartesianProductSealed CurrentJoinDomain CurrentJoinRawRepresentation
  CurrentJoinTimeRepresentation CurrentJoinTimeProductRepresentation CurrentJoinTripleCoordinates
  CurrentDomainRadonSigmaFinite DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  MeasureUP ProductMeasure ProductMeasureBijections MeasureBijectionUP MeasureBijectionLaws
  MeasureBijectionIntegralTransport RadonMeasureUP CountablyMeasurableUP
  PartialFunctionUP PartialFunctionPrecomposition ParameterizedIntegral ParameterizedIntegralLaws
  MeasureIntegralUP MeasureIntegralGraphEquivalence TripleProductFubini.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentJoinTripleMeasure.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n i j:nat.
Local Notation X := (R_n R n).
Local Notation Full := (fun _:X=>True).
Local Notation Time := (fun _:R_n R 1%N=>True).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X
  (inner_norm (@euclidean_inner_productP R n)) x).
Local Notation hTime := (fun (t:R_n R 1%N) (_:True)=>@norm_full_domain_interior R (R_n R 1%N)
  (inner_norm (@euclidean_inner_productP R 1%N)) t).
Local Notation TimeSpace := (@euclidean_cartesian_set R 1%N n Time Full).
Local Notation hTimeSpace := (@current_cartesian_domain_open R 1%N n Time Full hTime hFull).
Local Notation Domain := (@current_join_domain R n).
Local Notation XT := (current_domain R n Full).
Local Notation TT := (current_domain R 1%N Time).
Local Notation IT := (current_domain R (1+n)%N TimeSpace).
Local Notation CT := (current_domain R (n+(1+n))%N Domain).
Local Notation PT := (Choice.clone (XT*(TT*XT))%type _).
Variable S:@current_space R h2 n Full hFull i.
Variable T:@current_space R h2 n Full hFull j.
Hypothesis hS:@is_integration_representable_current R h2 n i Full hFull S.
Hypothesis hT:@is_integration_representable_current R h2 n j Full hFull T.
Local Notation Segment := (@current_join_time_segment R h2).
Local Notation hSegment := (@current_join_time_representable R h2).
Local Notation Inner := (@CartesianCurrentProduct.value R h2 1%N n 1%N j Time Full hTime hFull Segment T).
Local Notation hInner := (@current_join_time_product_representable R h2 n j Full hFull T hT).
Local Notation alpha := (@NormalisedCurrent.measure R h2 n i Full hFull S hS).
Local Notation beta := (@NormalisedCurrent.measure R h2 n j Full hFull T hT).
Local Notation rho := (@NormalisedCurrent.measure R h2 1%N 1%N Time hTime Segment hSegment).
Local Notation gamma := (@NormalisedCurrent.measure R h2 (1+n)%N (1+j)%N TimeSpace hTimeSpace Inner hInner).
Local Notation hNS := (@NormalisedCurrent.laws R h2 n i Full hFull S hS).
Local Notation hNT := (@NormalisedCurrent.laws R h2 n j Full hFull T hT).
Local Notation hNI := (@NormalisedCurrent.laws R h2 1%N 1%N Time hTime Segment hSegment).
Local Notation hNP := (@NormalisedCurrent.laws R h2 (1+n)%N (1+j)%N TimeSpace hTimeSpace Inner hInner).
Local Notation hAlpha := (distribution_representation_measure (normalised_distribution_representation_laws hNS)).
Local Notation hBeta := (distribution_representation_measure (normalised_distribution_representation_laws hNT)).
Local Notation hRho := (distribution_representation_measure (normalised_distribution_representation_laws hNI)).
Local Notation hGamma := (distribution_representation_measure (normalised_distribution_representation_laws hNP)).
Local Notation lambda := (@current_join_raw_measure R h2 n i j S T hS hT).
Local Notation J := (@current_join_triple_point R n).
Local Notation D := (@current_join_triple_split R n).
Local Notation mu := (product_measure hAlpha (product_measure_is_measure hRho hBeta)).
Local Notation hm := (product_measure_is_measure hAlpha (product_measure_is_measure hRho hBeta)).

(** Source for [current_join_triple_measure_bijection]: the
    actual source measure is exactly ||S|| times ||[0,1]||
    times ||T|| under its original coordinate bijection,
    supporting the mass integral in Federer 4.1.11, p. 365. *)
Theorem current_join_triple_measure_bijection:is_measure_bijection mu lambda J D.
Proof.
have hInnerBij:=@current_cartesian_measure_bijection R 1%N n Time Full rho beta hRho hBeta.
rewrite -(@current_join_time_product_variation R h2 n j Full hFull T hT hInner) in hInnerBij.
have hProduct:=@measure_bijection_product R XT (Choice.clone (TT*XT)%type _) XT IT
  alpha (product_measure hRho hBeta) alpha gamma hAlpha (product_measure_is_measure hRho hBeta) hAlpha hGamma
  id id (@CartesianCurrentDomain.join R 1%N n Time Full) (@CartesianCurrentDomain.split R 1%N n Time Full)
  (measure_bijection_identity alpha) hInnerBij.
have hOuter:=@current_cartesian_measure_bijection R n (1+n)%N Full TimeSpace alpha gamma hAlpha hGamma.
exact:(measure_bijection_compose hProduct hOuter).
Qed.

(** Source for [current_join_triple_integral_iff]: the
    original source integral is precisely its three-factor
    product integral, supporting Federer 4.1.11, p. 365.
    Every partial integrand and infinite value is retained. *)
Theorem current_join_triple_integral_iff (f:partial_function CT (extended_real_line R)) a:
  is_measure_integral mu (partial_function_precompose J f) a<->is_measure_integral lambda f a.
Proof.
exact:(@measure_bijection_integral_iff R PT CT mu lambda hm J D current_join_triple_measure_bijection f a).
Qed.

(** Source for [current_join_factors_countably_measurable]:
    the original Euclidean Radon factors have countable
    measurable covers, supporting Federer 4.1.11, p. 365,
    through the earlier 2.6.2 Fubini hypotheses. *)
Theorem current_join_factors_countably_measurable:
  measure_countably_measurable alpha setT /\measure_countably_measurable rho setT /\
    measure_countably_measurable beta setT.
Proof.
split.
- exact:(@current_domain_radon_countably_measurable R n Full hFull alpha hAlpha
    (distribution_representation_radon (normalised_distribution_representation_laws hNS))).
- split.
  + exact:(@current_domain_radon_countably_measurable R 1%N Time hTime rho hRho
      (distribution_representation_radon (normalised_distribution_representation_laws hNI))).
  + exact:(@current_domain_radon_countably_measurable R n Full hFull beta hBeta
      (distribution_representation_radon (normalised_distribution_representation_laws hNT))).
Qed.

(** Source for [current_join_triple_fubini]: the actual
    source integral equals the literal original x,t,y
    repeated integral, supporting Federer 4.1.11, p. 365.
    Partial section-integral domains are preserved. *)
Theorem current_join_triple_fubini (f:partial_function CT (extended_real_line R)) a:
  is_measure_integral lambda f a->
  is_measure_integral alpha (parameterized_integral rho (fun x:XT=>
    parameterized_integral beta (fun t:TT=>
      partial_function_precompose (fun y:XT=>J (x,(t,y))) f))) a.
Proof.
move=>hIntegral.
have [hX [hTimeCount hY]]:=current_join_factors_countably_measurable.
have hProduct:=(current_join_triple_integral_iff f a).2 hIntegral.
have hIterated:=@triple_product_vertical_fubini R XT TT XT alpha rho beta hAlpha hRho hBeta
  (partial_function_precompose J f) a hX hTimeCount hY hProduct.
apply:(@measure_integral_graph_equivalent R XT alpha _ _ a _ hIterated)=>x z.
apply:parameterized_integral_graph_equivalent=>x' t v.
apply:parameterized_integral_graph_equivalent=>t' y w.
by [].
Qed.
End CurrentJoinTripleMeasure.
