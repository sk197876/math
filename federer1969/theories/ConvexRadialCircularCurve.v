(** Federer (1969), 3.3.19, p. 304:
    the original bounded open convex boundary admits
    an actual simple periodic Lipschitz parameter. Use
    the corrected radial map proved in 3.2.35,
    p. 271, after the body contains zero. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness NormMetric RealNormUP InnerConvex CoveringFamilyUP
  MinkowskiGaugeUP RadialGaugeMapUP PartialFunctionUP PartialMetricLipschitz
  NormConvexRadialBoundaryImage NormConvexRadialBoundaryLipschitz NormRadialGaugeMapInjectivity
  CircularTrigonometrySealed CircularUnitVectors CircularUnitCurve CircularPrincipalParameter CircularUnitVectorInjective
  LipschitzUP RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Boundary.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation N:=(inner_norm (@euclidean_inner_productP R 2)).
Local Notation hN:=(inner_norm_real_norm (@euclidean_inner_productP R 2)).
Local Notation p:=(@CircularTrigonometry.half_period R).

(** Source for [convex_radial_circular_curve_exists]:
    supporting actual boundary parametrization for the
    cyclic ordering in 3.3.19, p. 304.
    The circle and corrected radial map give its exact
    original boundary image, half-open injectivity, full
    period and an actual finite Lipschitz bound. The
    gauge and map remain local existential witnesses. *)
Theorem convex_radial_circular_curve_exists (S:set E):
  @open [the topologicalType of real_norm_metric_space hN] S ->
  is_inner_convex S ->S 0 ->
  @metric_set_bounded R [the metricType R of real_norm_metric_space hN] S ->
  exists (C:R->E) (L:R),
    0<= L /\(forall a b,mdist (C a) (C b)<= L*`|a-b|) /\
    (forall a,C (a+(p+p))= C a) /\
    (forall a b,0<= a ->a<2* p ->0<= b ->b<2* p ->C a= C b ->a= b) /\
    C @` (`[0,2* p[:set R)=
      (@closure [the topologicalType of real_norm_metric_space hN] S `\`
       @interior [the topologicalType of real_norm_metric_space hN] S).
Proof.
move=>hOpen hConvex hZero hBound.
have [g [f [hG [hF hImage]]]]:= @norm_convex_radial_boundary_map_exists R (R_n R 2) N hN S
  hOpen hConvex hZero hBound.
have [L [hL hLipschitz]]:= @norm_convex_radial_boundary_lipschitz R (R_n R 2) N hN S g f
  hG hOpen hConvex hZero hBound hF.
pose C:R->E:= fun t=>(g (circular_unit_vector t))^-1 *: circular_unit_vector t.
have hGraph t:partial_function_graph f (circular_unit_vector t) (C t).
  apply:((@radial_gauge_map_graph_law R (R_n R 2) N g f hF _ _).2).
  split;first exact:circular_unit_vector_norm;exact:erefl.
exists C,(2* L);split;first by nra.
split.
- move=>a b.
  have hMap:= hLipschitz _ _ _ _ (hGraph a) (hGraph b).
  have hCircle:= @circular_unit_vector_lipschitz R a b.
  have hScaled:= ler_wpM2l hL hCircle.
  change (is_true (mdist (C a) (C b)<= L* mdist (circular_unit_vector a) (circular_unit_vector b))) in hMap.
  apply:(le_trans hMap);nra.
split.
- by move=>a;rewrite /C circular_unit_vector_period.
split.
- move=>a b ha haP hb hbP hEqual.
  have hSame: circular_unit_vector a= circular_unit_vector b.
    apply:(@norm_convex_radial_boundary_injective R (R_n R 2) N hN S g f hG hZero hBound hF
      _ _ (C a) (hGraph a)).
    by rewrite hEqual;exact:hGraph.
  exact:(@circular_unit_vector_principal_injective R a b ha haP hb hbP hSame).
- rewrite -hImage;apply/seteqP;split=>z.
  + move=>[t _ <-];exists (circular_unit_vector t);exact:hGraph.
  + move=>[u hu].
    have [hU hValue]:=(@radial_gauge_map_graph_law R (R_n R 2) N g f hF u z).1 hu.
    have [t [ht0 [htP htU]]]:= @circular_principal_parameter_exists R u hU.
    exists t;first by rewrite /= in_itv /= ht0 htP.
    by rewrite /C htU.
Qed.
End Boundary.
