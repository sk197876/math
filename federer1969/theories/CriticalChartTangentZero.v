(** Federer (1969), 3.4.2(7), pp. 312–313: testing the tangent
    zero locus with the ambient derivative of f composed with r. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom ModuleQuotient GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness RealNormUP NormDifferentialUP PartialFunctionUP
  RelativeDifferential TangentConeUP EuclideanProjectionSpace CriticalManifoldFamilyUP
  CriticalManifoldChartLaws CriticalFlatPiecesUP CriticalChartCompositeDerivative
  CriticalChartRetractionDifferential CriticalRelativeDifferentialLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_chart_tangent_zero_iff]: the closed set B
    and derivative functions f_i in the proof of 3.4.2(7),
    pp. 312–313. The original relative derivative vanishes on
    Z intersect Tan(S,a) exactly when the derivative of f composed
    with r vanishes on all of Z. The retraction maps Z into the
    original tangent domain and fixes every tangent vector. *)
Theorem critical_chart_tangent_zero_iff (R:realType) m mu k
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (Z:subspace (R_n R m)) (S:set (R_n R m))
    (p:euclidean_projection_space R m mu) g (f:R_n R m->Y)
    a (Dr:Hom (R_n R m) (R_n R m)) (D:Hom (R_n R m) Y):
  is_critical_manifold_chart k Z S p g ->S a ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R m))
    (fun x=>(euclidean_projection_linear p @` S) (euclidean_projection_linear p x))
    (fun x=>g (euclidean_projection_linear p x)) a Dr ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R m)) NY
    (fun x=>(euclidean_projection_linear p @` S) (euclidean_projection_linear p x))
    (fun x=>f (g (euclidean_projection_linear p x))) a D ->
  (critical_tangent_zero_locus hNY Z S f a <->forall z,Z z ->D z=0).
Proof.
move=>hChart ha hDr hD.
pose X:=R_n R m.
pose NX:=inner_norm (@euclidean_inner_productP R m).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose U:=fun x=>(euclidean_projection_linear p @` S) (euclidean_projection_linear p x).
pose r:=fun x=>g (euclidean_projection_linear p x).
pose F:=fun x=>f (r x).
have hFix:r a=a:=critical_chart_left_inverse hChart ha.
have hDb:has_norm_differential NX NY U F (r a) D by rewrite hFix.
have [L [hOuter hInner]]:=
  @critical_chart_composite_relative_derivative R m mu k Z S p g hChart Y NY hNY
    f a Dr D D hDr hD hDb.
have hOuterA:partial_function_graph (relative_norm_differential hNX hNY S S f) a L.
  by rewrite -hFix;exact:hOuter.
split.
- move=>[_ [L0 [hOuter0 hZero]]] z hz.
  have hSame:L0=L:=partial_function_single_valued hOuter0 hOuterA.
  have hTest:partial_function_graph L0 (Dr z) (D z) by rewrite hSame;exact:hInner.
  apply:(hZero (Dr z) (D z));last exact:hTest.
  exact:(critical_retraction_differential_preserves_subspace hChart hDr hz).
- move=>hZero;split;first exact:ha.
  have hAgree x (hx:S x) (hxU:U x):f x=F x.
    by rewrite /F /r (critical_chart_left_inverse hChart hx).
  have [L0 [hOuter0 hValues]]:=@critical_relative_differential_from_extension
    R X Y NX NY hNX hNY U S F f a D ha hAgree hD.
  exists L0;split;first exact:hOuter0.
  move=>z y hz hy.
  have hValue:=(hValues z y).1 hy.
  by rewrite (hZero z hz) in hValue;exact:esym hValue.2.
Qed.
