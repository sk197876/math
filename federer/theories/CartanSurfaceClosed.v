(** Federer (1969), 3.4.5, p. 321, citing Cartan
    (1957), p. 97: continuity of the original coefficient
    makes the actual cubic surface closed. No analyticity
    at its flat endpoint is used for this assertion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  NormMetric NormDifferentialUP NormClassOneUP NormOpenDomainLaws NormRegularity NormClassZeroTopology NormClassZeroComposition
  NormClassHigherRestriction NormClassZeroScalarProduct NormAnalyticUP NormAnalyticLocal
  NormAnalyticOperations NormAnalyticScalarProducts EuclideanScalarCoordinateAnalytic
  FlatExponentialSealed CartanCoefficientAnalytic CartanSurfaceUP CartanSurfaceSealed ContinuousEqualizerClosed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [cartan_surface_closed]: the actual
    adapted Cartan surface is closed in the original Euclidean
    norm topology, supporting the local/global example cited
    at 3.4.5, p. 321. *)
Theorem cartan_surface_closed (R:realType):
  @closed (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R 3)))
    (@CartanSurface.set R).
Proof.
pose X:=R_n R 3.
pose NX:=inner_norm (@euclidean_inner_productP R 3).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R 3).
pose N:=fun t:R^o=>`|t|.
pose hN:=@scalar_absolute_value_norm R.
pose T:=real_norm_metric_space hNX.
pose Y:=real_norm_metric_space hN.
pose x:=fun v:X=>v ord0.
pose y:=fun v:X=>v (Ordinal (isT:(1<3)%N)).
pose z:=fun v:X=>v ord_max.
pose c:=fun v:X=>FlatExponential.value (1-z v).
have hX:=@euclidean_scalar_coordinate_analytic R 3 ord0.
have hY:=@euclidean_scalar_coordinate_analytic R 3 (Ordinal (isT:(1<3)%N)).
have hZ:=@euclidean_scalar_coordinate_analytic R 3 ord_max.
have hFAnalytic:=norm_analytic_scalar_product hZ
  (norm_analytic_add (norm_analytic_scalar_power 2%N hX) (norm_analytic_scalar_power 2%N hY)).
pose F:=fun v:X=>z v*((x v)^+2+(y v)^+2).
pose G:=fun v:X=>(x v)^+3*c v.
have hF:norm_class_zero NX N setT F:=norm_class_continuous
  (norm_analytic_class_all_orders hFAnalytic 0%N).
have hZContinuous:=norm_class_continuous (norm_analytic_class_all_orders hZ 0%N).
have hComp:=norm_class_zero_composition hZContinuous (@cartan_coefficient_continuous R).
have hCoefficient:norm_class_zero NX N setT c.
  exact:(norm_class_zero_open_restriction (fun v (_:setT v)=>conj Logic.I Logic.I)
    (fun v (_:setT v)=>norm_full_domain_interior NX v) hComp).
have hCube:=norm_class_continuous
  (norm_analytic_class_all_orders (norm_analytic_scalar_power 3%N hX) 0%N).
have hG:norm_class_zero NX N setT G:=norm_class_zero_scalar_product hN hCube hCoefficient.
have hFContinuous:continuous (fun v:T=>(F v:Y)).
  move=>v;exact:(@norm_class_zero_continuous_at R X R^o NX N hNX hN setT F v hF Logic.I).
have hGContinuous:continuous (fun v:T=>(G v:Y)).
  move=>v;exact:(@norm_class_zero_continuous_at R X R^o NX N hNX hN setT G v hG Logic.I).
have hClosed:=@continuous_equalizer_closed [the topologicalType of T] [the topologicalType of Y]
  (fun v:T=>(F v:Y)) (fun v:T=>(G v:Y)) (@metric_hausdorff R [the metricType R of Y]) hFContinuous hGContinuous.
have hEquation:@CartanSurface.set R=[set v:X|F v=G v].
  apply/seteqP;split=>v hv.
  - exact:(cartan_surface_membership (@CartanSurface.laws R) v).1 hv.
  - exact:(cartan_surface_membership (@CartanSurface.laws R) v).2 hv.
by rewrite hEquation.
Qed.
