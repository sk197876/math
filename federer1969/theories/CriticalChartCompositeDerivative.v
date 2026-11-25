(** Federer (1969), 3.4.2(6)–(7), pp. 312–313: the original
    relative derivative in the chain formula for f composed with r. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom ModuleQuotient GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness NormMetric RealNormUP NormDifferentialUP
  PartialFunctionUP RelativeDifferential TangentConeUP EuclideanProjectionSpace
  CriticalManifoldFamilyUP CriticalChartRetractionDifferential
  CriticalRetractionCompositeDifferential CriticalRelativeDifferentialLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Section Composite.
Variable R:realType.
Variables m mu k:nat.
Local Notation X:=(R_n R m).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R m)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R m)).
Variable Z:subspace X.
Variable S:set X.
Variable p:euclidean_projection_space R m mu.
Variable g:R_n R mu->X.
Hypothesis hChart:is_critical_manifold_chart k Z S p g.
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable f:X->Y.
Local Notation r:=(fun x=>g (euclidean_projection_linear p x)).
Local Notation U:=(fun x=>(euclidean_projection_linear p @` S) (euclidean_projection_linear p x)).
Local Notation F:=(fun x=>f (r x)).

(** Source for [critical_chart_composite_relative_derivative]: the
    relative chain formula used in 3.4.2(6), p. 312, and the functions
    f_i of (7), p. 313. Actual differentials of F=f composed with r
    satisfy DF(a)v=Df(r(a))[Dr(a)v]. The image vector lies in the
    original tangent domain; no ambient derivative of f is assumed. *)
Theorem critical_chart_composite_relative_derivative a (Dr:Hom X X) (D E:Hom X Y):
  has_norm_differential NX NX U r a Dr ->
  has_norm_differential NX NY U F a D ->
  has_norm_differential NX NY U F (r a) E ->
  exists L:partial_function X Y,
    partial_function_graph (relative_norm_differential hNX hNY S S f) (r a) L /\
    forall v,partial_function_graph L (Dr v) (D v).
Proof.
move=>hDr hDF hDFb.
have haU:U a:=norm_domain_interior_member hNX (norm_differential_interior hDr).
have hRaS:S (r a):=(critical_chart_right_inverse hChart haU).1.
have hMap x (hx:U x):U (r x).
  have hRxS:S (r x):=(critical_chart_right_inverse hChart hx).1.
  by exists (r x).
have hEqual x (hx:U x):F (r x) = F x.
  have hRxS:S (r x):=(critical_chart_right_inverse hChart hx).1.
  have hFix:r (r x) = r x:=critical_chart_left_inverse hChart hRxS.
  exact:(congr1 f hFix).
have hIdentity:=@critical_retraction_composite_differential R X Y NX NY hNX hNY
  U r F a Dr D E hMap hEqual hDr hDF hDFb.
have hAgree x (hx:S x) (hxU:U x):f x=F x.
  by rewrite (critical_chart_left_inverse hChart hx).
have [L [hOuter hL]]:=@critical_relative_differential_from_extension R X Y NX NY
  hNX hNY U S F f (r a) E hRaS hAgree hDFb.
exists L;split;first exact:hOuter.
move=>v;apply:(hL (Dr v) (D v)).2;split.
- exact:(@critical_retraction_differential_tangent R m mu k Z S p g a Dr hChart hDr v).
- exact:(esym (congr1 (fun A:Hom X Y=>A v) hIdentity)).
Qed.
End Composite.
