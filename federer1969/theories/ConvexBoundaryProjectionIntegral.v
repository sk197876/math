(** Federer (1969), 3.2.35, p. 272:
    integrating the actual boundary multiplicity
    gives twice the projected volume. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex CoveringFamilyUP
  EuclideanProjectionSpace EuclideanProjectionMetric EuclideanProjectionOpenImage EuclideanProjectionConvexImage
  EuclideanProjectionBoundedImage EuclideanConvexBoundaryNull ConvexBoundaryProjectionMultiplicity
  ConvexBoundaryProjectionImage MappingMultiplicity CountingMeasure MeasureUP MeasureBasic
  MeasureAlmostUP MeasureAlmostBasic CharacteristicFunctionUP CharacteristicFunctionSealed
  EuclideanLebesgueDimensions BorelRegularMeasureUP TopologicalBorel PartialFunctionBasic
  SummableRealFunctionUP MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness
  MeasureIntegralAlmostEquality MeasureFiniteCharacteristicIntegral ProjectionMultiplicityIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_boundary_projection_integral]:
    the inner integral in the first display
    of Federer 3.2.35, p. 272. The
    actual multiplicity equals two on p(S),
    and zero off its closure. Only the
    proved ambient-null boundary of p(S) is
    discarded. Characteristic integration and the
    abstract lower-integral law establish the
    actual existing projection integral value.
    Zero-dimensional targets remain included. *)
Theorem convex_boundary_projection_integral (R:realType) k
    (p:orthogonal_projection_metric_space R k.+1 k)
    (S:set (inner_metric_space (@euclidean_inner_productP R k.+1))):
  S!=set0 ->open S ->is_inner_convex S ->metric_set_bounded S ->
  projection_multiplicity_integral (closure S `\` interior S) p=
    (2:R)%:E*euclidean_lebesgue_measure k (euclidean_projection_linear p @` S).
Proof.
move=>hNonempty hOpen hConvex hBound.
pose Y:=inner_metric_space (@euclidean_inner_productP R k).
pose P:set Y:=euclidean_projection_linear p @` S.
pose B:=@closure [the topologicalType of Y] P `\` @interior [the topologicalType of Y] P.
pose mu:=@euclidean_lebesgue_measure R k.
have hm:=euclidean_lebesgue_is_measure R k.
have hPNonempty:P!=set0 by have [a ha]:=hNonempty; exists (euclidean_projection_linear p a); by exists a.
have hPOpen:@open [the topologicalType of Y] P:=@euclidean_projection_open_image R k.+1 k p S hOpen.
have hPConvex:is_inner_convex P:=@euclidean_projection_convex_image R k.+1 k p S hConvex.
have hPBound:@metric_set_bounded R [the metricType R of Y] P:=@euclidean_projection_bounded_image R k.+1 k p S hBound.
have hBNull:mu B=0:=euclidean_open_convex_boundary_null hPNonempty hPOpen hPConvex hPBound.
have hPMeasurable:measure_measurable mu P.
  apply:(borel_regular_borel_measurable hm (euclidean_lebesgue_borel_regular R k)).
  exact:open_borel_set hPOpen.
pose chi:=@CharacteristicFunction.value R Y P.
have hChi:is_characteristic_function P chi:=@CharacteristicFunction.laws R Y P.
pose f:=projection_multiplicity_integrand (closure S `\` interior S) p.
pose g:=real_total_integrand (fun y:Y=>(2*chi y)%R).
have hG:is_measure_integral mu g ((2:R)%:E*mu P).
  exact:(@measure_positive_characteristic_integral R Y mu hm P chi 2 hChi hPMeasurable (ltr0n R 2)).
have hAgreement:measure_almost_equal mu g f.
  apply:(@measure_null_subset R Y mu hm _ B _ hBNull)=>y hNotAgreement.
  apply:contrapT=>hOutside.
  have hValue:@mapping_multiplicity R _ _ (euclidean_projection_linear p) (closure S `\` interior S) y=(2*chi y)%R%:E.
    case:(pselect (P y))=>hy.
    - rewrite (characteristic_on_set hChi hy) mulr1.
      exact:convex_boundary_projection_multiplicity hOpen hConvex hBound hy.
    - rewrite (characteristic_off_set hChi hy) mulr0.
      have hNoClosure:~@closure [the topologicalType of Y] P y.
        move=>hc; apply:hOutside; split=>// hi; apply:hy; exact:interior_subset hi.
      have hEmpty:mapping_fibre (euclidean_projection_linear p) (closure S `\` interior S) y=set0.
        apply/seteqP; split=>x; last by [].
        move=>[hx hp]; apply:hNoClosure.
        rewrite -(@convex_boundary_projection_closure R k p S hOpen hConvex hBound).
        by exists x.
      rewrite /mapping_multiplicity hEmpty; exact:measure_empty (counting_measure_is_measure R _).
  apply:hNotAgreement; exists (2*chi y)%R%:E; split.
  - apply/real_total_integrand_graph; reflexivity.
  - exact hValue.
have hF:=@measure_integral_almost_equal R Y mu hm g f _ hG hAgreement.
exact:(@measure_lower_integral_unique R Y mu f _ _ (measure_lower_integral_specification mu f) hF.2.2).
Qed.
