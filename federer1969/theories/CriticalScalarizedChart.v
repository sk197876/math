(** Federer (1969), 3.4.2(7), p. 314: the scalar function
    alpha composed with f and the inverse projection chart. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom ModuleQuotient GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness RealNormUP NormDifferentialUP NormDifferentialLinear
  NormDifferentialFiniteCalculus NormClassOneUP NormRegularity NormRegularityLinearMaps
  NormCoordinateSystemUP NormCoordinateTangent RelativeClassUP PartialFunctionUP
  RelativeDifferential RelativeCoordinateDifferential ParametricDifferentialUP
  EuclideanProjectionSpace CriticalManifoldFamilyUP CriticalChartCoordinates
  CriticalChartRetractionClass CriticalRelativeComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_scalarized_chart_class]: the class-k
    function F=alpha composed with f composed with (p|S)^(-1)
    in 3.4.2(7), p. 314. Relative class on S suffices for
    composition with the original inverse chart; the bounded
    functional preserves that class. *)
Theorem critical_scalarized_chart_class (R:realType) m mu k
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (Z:subspace (R_n R m)) (S:set (R_n R m))
    (p:euclidean_projection_space R m mu) g (f:R_n R m->Y) (alpha:Hom Y R^o):
  is_critical_manifold_chart k Z S p g ->
  norm_class_relative (inner_norm_real_norm (@euclidean_inner_productP R m))
    hNY S S f k ->norm_bounded_linear NY (fun t:R^o=>`|t|) alpha ->
  norm_class (inner_norm_real_norm (@euclidean_inner_productP R mu))
    (@scalar_absolute_value_norm R) (euclidean_projection_linear p @` S)
    (fun w=>alpha (f (g w))) k.
Proof.
move=>hChart hf hAlpha.
pose NX:=inner_norm (@euclidean_inner_productP R m).
pose NV:=inner_norm (@euclidean_inner_productP R mu).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose hNV:=inner_norm_real_norm (@euclidean_inner_productP R mu).
have hMap u (hu:(euclidean_projection_linear p @` S) u):S (g u):=
  (critical_chart_right_inverse hChart hu).1.
have hComp:=@critical_relative_class_composition R (R_n R mu) (R_n R m) Y NV NX NY
  hNV hNX hNY (euclidean_projection_linear p @` S) S g f k
  (critical_chart_inverse_class hChart) hMap hf.
exact:(norm_class_postcompose_linear (@scalar_absolute_value_norm R) hAlpha hComp).
Qed.

(** Source for [critical_scalarized_chart_direction]: the identity
    DF[p(a)]p(z)=alpha(Df(a)z) used in 3.4.2(7), p. 314.
    The relative-coordinate criterion of 3.1.22 transports the
    genuine derivative through the original inverse chart. Its
    inverse tangent identity identifies the parameter vector p(z).
    No ambient differentiability of the original f is assumed. *)
Theorem critical_scalarized_chart_direction (R:realType) m mu
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (Z:subspace (R_n R m)) (S:set (R_n R m))
    (p:euclidean_projection_space R m mu) g (f:R_n R m->Y)
    (alpha:Hom Y R^o) a z y (L:partial_function (R_n R m) Y):
  is_critical_manifold_chart 1 Z S p g ->S a ->
  norm_bounded_linear NY (fun t:R^o=>`|t|) alpha ->
  partial_function_graph (relative_norm_differential
    (inner_norm_real_norm (@euclidean_inner_productP R m)) hNY S S f) a L ->
  partial_function_graph L z y ->
  exists D:Hom (R_n R mu) R^o,
    has_norm_differential (inner_norm (@euclidean_inner_productP R mu))
      (fun t:R^o=>`|t|) (euclidean_projection_linear p @` S)
      (fun w=>alpha (f (g w))) (euclidean_projection_linear p a) D /\
    D (euclidean_projection_linear p z)=alpha y.
Proof.
move=>hChart ha hAlpha hOuter hInner.
pose X:=R_n R m;pose V:=R_n R mu.
pose NX:=inner_norm (@euclidean_inner_productP R m).
pose NV:=inner_norm (@euclidean_inner_productP R mu).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose hNV:=inner_norm_real_norm (@euclidean_inner_productP R mu).
pose P:=hom_of_linear (euclidean_projection_linear p).
pose U:=fun x=>(euclidean_projection_linear p @` S) (P x).
pose W:=euclidean_projection_linear p @` S.
have hc:=critical_chart_coordinate_system hChart.
have haU:U a by exists a.
have haW:W (P a):=haU.
have hPInterior:norm_domain_interior NX U a:=
  (norm_class_continuous (norm_coordinate_class_forward hc) haU).1.
have hP:=@norm_differential_linear R X V NX NV hNX hNV U a P hPInterior
  (critical_projection_bounded_linear p).
have [J hJ]:=(norm_class_firstP hNV hNX W g).1 (critical_chart_inverse_class hChart).
have hG:=norm_class_one_differential hJ haW.
have hRelative:=(@relative_norm_differential_graph R X Y NX NY hNX hNY S S f a L).1 hOuter.
have [Q [hQ hRestriction]]:=(@relative_coordinate_differential_criterion R X V Y NX NV NY
  hNX hNV hNY S S U W (euclidean_projection_linear p) g f a P (J (P a)) L
  hc ha haU (fun x hx=>hx) hP hG).1 hRelative.
have [hLeft _]:=norm_coordinate_tangent_inverse hc ha haU hP hG.
have [w [hw hQy]]:=(hRestriction z y).1 hInner.
have hParameter:euclidean_projection_linear p z=w by rewrite -hw;exact:hLeft.
exists (hom_comp alpha Q);split.
- exact:(norm_differential_postcompose hNV hQ hAlpha).
- by rewrite hom_compE hParameter hQy.
Qed.
