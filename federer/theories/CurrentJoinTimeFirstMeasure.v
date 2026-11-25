(** Federer (1969), 4.1.11, p. 365: integrate the
    original time factor first in the sharp mass formula.
    Only the preceding countable product association and
    factor swap of 2.6.5, pp. 119–120, are used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom ExtendedRealOrderTopology RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentDomain CurrentSpaces CurrentIntegrationCriterion NormalisedCurrentSealed
  CurrentJoinDomain CurrentJoinRawRepresentation CurrentJoinTripleCoordinates CurrentJoinTripleMeasure
  CurrentJoinTimeRepresentation DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  MeasureUP ProductMeasure ProductMeasureBijections ProductMeasureShuffle MeasureBijectionUP
  MeasureBijectionLaws MeasureBijectionCoordinateTransport MeasureBijectionIntegralTransport CountablyMeasurableUP
  CountablyMeasurableProduct CountablyMeasurableFunctions CountablyMeasurableNullModification
  PartialFunctionUP PartialFunctionPrecomposition PartialProductSections
  ParameterizedIntegral ParameterizedIntegralLaws MeasureIntegralUP MeasureIntegralGraphEquivalence ProductFunctionFubini.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentJoinTimeFirstMeasure.
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
Local Notation XT := (current_domain R n Full).
Local Notation TT := (current_domain R 1%N Time).
Local Notation CT := (current_domain R (n+(1+n))%N (@current_join_domain R n)).
Local Notation PT := (Choice.clone ((XT*XT)*TT)%type _).
Local Notation J := (@current_join_triple_point R n).
Local Notation D := (@current_join_triple_split R n).

(** Source for [current_join_time_first_point]: the
    original ordered point (x,t,y), with the time variable
    grouped last for integration, supporting Federer 4.1.11, p. 365. *)
Definition current_join_time_first_point (u:(XT*XT)*TT):CT:=J (u.1.1,(u.2,u.1.2)).

(** Source for [current_join_time_first_split]: the
    inverse original factor regrouping, supporting the
    mass coefficient calculation in Federer 4.1.11, p. 365. *)
Definition current_join_time_first_split (z:CT):(XT*XT)*TT:=
  (((D z).1,(D z).2.2),(D z).2.1).

Variable S:@current_space R h2 n Full hFull i.
Variable T:@current_space R h2 n Full hFull j.
Hypothesis hS:@is_integration_representable_current R h2 n i Full hFull S.
Hypothesis hT:@is_integration_representable_current R h2 n j Full hFull T.
Local Notation Segment := (@current_join_time_segment R h2).
Local Notation hSegment := (@current_join_time_representable R h2).
Local Notation alpha := (@NormalisedCurrent.measure R h2 n i Full hFull S hS).
Local Notation beta := (@NormalisedCurrent.measure R h2 n j Full hFull T hT).
Local Notation rho := (@NormalisedCurrent.measure R h2 1%N 1%N Time hTime Segment hSegment).
Local Notation hAlpha := (distribution_representation_measure (normalised_distribution_representation_laws
  (@NormalisedCurrent.laws R h2 n i Full hFull S hS))).
Local Notation hBeta := (distribution_representation_measure (normalised_distribution_representation_laws
  (@NormalisedCurrent.laws R h2 n j Full hFull T hT))).
Local Notation hRho := (distribution_representation_measure (normalised_distribution_representation_laws
  (@NormalisedCurrent.laws R h2 1%N 1%N Time hTime Segment hSegment))).
Local Notation delta := (product_measure hAlpha hBeta).
Local Notation hDelta := (product_measure_is_measure hAlpha hBeta).
Local Notation mu := (product_measure hDelta hRho).
Local Notation hm := (product_measure_is_measure hDelta hRho).
Local Notation lambda := (@current_join_raw_measure R h2 n i j S T hS hT).

(** Source for [current_join_time_first_measure_bijection]:
    the original source measure is unchanged by grouping
    the spatial pair first and time last, supporting the
    factorial identity in Federer 4.1.11, p. 365. *)
Theorem current_join_time_first_measure_bijection:
  is_measure_bijection mu lambda current_join_time_first_point current_join_time_first_split.
Proof.
have [hX [hTimeCount hY]]:=@current_join_factors_countably_measurable R h2 n i j S T hS hT.
have hAssociation:=@countable_product_association_bijection R XT XT TT
  alpha beta rho hAlpha hBeta hRho hX hTimeCount.
have hSwap:=measure_bijection_product hAlpha (product_measure_is_measure hBeta hRho)
  hAlpha (product_measure_is_measure hRho hBeta) (measure_bijection_identity alpha)
  (measure_bijection_swap hBeta hRho).
exact:(measure_bijection_compose (measure_bijection_compose hAssociation hSwap)
  (@current_join_triple_measure_bijection R h2 n i j S T hS hT)).
Qed.

(** Source for [current_join_time_first_integral_iff]: the
    regrouped source integral is exactly the original one,
    supporting Federer 4.1.11, p. 365. Every actual partial
    domain and infinite integral value is preserved. *)
Theorem current_join_time_first_integral_iff (f:partial_function CT (extended_real_line R)) a:
  is_measure_integral mu (partial_function_precompose current_join_time_first_point f) a<->
    is_measure_integral lambda f a.
Proof.
exact:(@measure_bijection_integral_iff R PT CT mu lambda hm current_join_time_first_point
  current_join_time_first_split current_join_time_first_measure_bijection f a).
Qed.

(** Source for [current_join_time_first_fubini]: the original
    source integral equals the spatial integral of its
    actual inner time integrals, supporting Federer 4.1.11,
    p. 365. Fubini supplies conull inner integrability. *)
Theorem current_join_time_first_fubini (f:partial_function CT (extended_real_line R)) a:
  is_measure_integral lambda f a->
  is_measure_integral delta (parameterized_integral rho (fun xy:XT*XT=>
    partial_function_precompose (fun t:TT=>J (xy.1,(t,xy.2))) f)) a.
Proof.
move=>hIntegral.
have hProduct:=(current_join_time_first_integral_iff f a).2 hIntegral.
have [hX [hTimeCount hY]]:=@current_join_factors_countably_measurable R h2 n i j S T hS hT.
have hSpatial:=@product_whole_countably_measurable R XT XT alpha beta hAlpha hBeta hX hY.
have hWhole:=@product_whole_countably_measurable R (XT*XT)%type TT delta rho hDelta hRho hSpatial hTimeCount.
have hCount:=@countably_measurable_function_on_countable_source R ((XT*XT)*TT)%type
  (extended_real_line R) mu hm 0%E (partial_function_precompose current_join_time_first_point f)
  (@extended_real_zero_closed R) hWhole hProduct.1.
have hOuter:=(@product_function_fubini R (XT*XT)%type TT delta rho hDelta hRho
  (partial_function_precompose current_join_time_first_point f) a hProduct hCount).1.
apply:(@measure_integral_graph_equivalent R (XT*XT)%type delta _ _ a _ hOuter)=>xy v.
apply:parameterized_integral_graph_equivalent=>xy' t w.
by [].
Qed.
End CurrentJoinTimeFirstMeasure.
