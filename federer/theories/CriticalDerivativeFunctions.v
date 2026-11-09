(** Federer (1969), 3.4.2(7), p. 313: the derivative functions
    used to lower differentiability class on the common critical set. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom ModuleQuotient GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness RealNormUP NormClassOneUP NormRegularity
  NormRegularityOperations NormRegularityDerivativeField NormRegularityLinearMaps
  RelativeClassUP PartialFunctionUP RelativeDifferential ContinuousMultilinearUP
  ContinuousMultilinearNorm ContinuousMultilinearOne ContinuousMultilinearEvaluationBound
  ContinuousMultilinearSealed EuclideanProjectionSpace CriticalManifoldFamilyUP
  CriticalFlatPiecesUP CriticalChartRetractionClass CriticalChartTangentZero
  CriticalRelativeDifferentialLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_derivative_function_family]: the functions
    f_i(x)=Df(x)[Dr(x)e_i] in 3.4.2(7), p. 313. Each is of class
    k and vanishes on B when f belongs to Φ(S,C,k+1). Their linear
    combinations recover the original relative derivative, including
    its restriction to each smaller piece, on every vector expressed
    in the given family. The operator field and
    representatives are local existence witnesses; the target is
    an arbitrary normed space. *)
Theorem critical_derivative_function_family (R:realType) m mu k
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (Z:subspace (R_n R m)) (S C:set (R_n R m))
    (p:euclidean_projection_space R m mu) g (f:R_n R m->Y)
    (I:finType) (e:I->R_n R m):
  is_critical_manifold_chart k.+1 Z S p g ->
  critical_flat_function_class hNY S C f k.+1 ->(forall i,Z (e i)) ->
  exists fi:I->R_n R m->Y,
    (forall i,critical_flat_function_class hNY S
      (critical_common_tangent_zero_set hNY Z S C k.+1) (fi i) k) /\
    forall T:set (R_n R m),T `<=` S ->forall x,T x ->
    forall (L:partial_function (R_n R m) Y) z y (c:I->R),
      partial_function_graph (relative_norm_differential
        (inner_norm_real_norm (@euclidean_inner_productP R m)) hNY T T f) x L ->
      partial_function_graph L z y ->z=\sum_i c i*:e i ->
      y=\sum_i c i*:fi i x.
Proof.
move=>hChart hf heZ.
pose X:=R_n R m.
pose NX:=inner_norm (@euclidean_inner_productP R m).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose W:=@ContinuousMultilinear.space R 1 X Y NX NY hNX hNY.
pose ev:=@ContinuousMultilinear.evaluation R 1 X Y NX NY hNX hNY.
pose WN:=@ContinuousMultilinear.norm R 1 X Y NX NY hNX hNY.
pose hW:=@ContinuousMultilinear.laws R 1 X Y NX NY hNX hNY.
pose hWN:=continuous_multilinear_norm_is_norm hNY hW.
pose U:=fun x=>(euclidean_projection_linear p @` S) (euclidean_projection_linear p x).
pose r:=fun x=>g (euclidean_projection_linear p x).
pose F:=fun x=>f (r x).
have hSU:S `<=` U by move=>x hx;exists x.
have hR:=critical_chart_retraction_class hChart.
have hFirst:(1<=k.+1)%N by [].
have hR1:=norm_class_lower hFirst hR.
have [Dr hDr]:=(norm_class_firstP hNX hNX U r).1 hR1.
have hF:=critical_chart_relative_composition_class hChart hf.1.
have [G [hG hDiff]]:=@norm_class_derivative_field R X Y NX NY hNX hNY U F k hF.
pose fi i x:=ev [ffun j:'I_1=>e i] (G x).
exists fi;split.
- move=>i;split.
  + have hEvaluation:=@continuous_multilinear_evaluation_bounded R 1 X Y W NX NY hNX
      ev WN hW [ffun j:'I_1=>e i].
    have hClass:=@norm_class_postcompose_linear R X W Y NX WN NY hNX hWN hNY U G
      (ev [ffun j:'I_1=>e i]) k hEvaluation hG.
    apply:(@norm_relative_extension_class R X Y NX NY hNX hNY S S (fi i) k U (fi i)).
    split;first exact:hClass.
    split;first exact:hSU.
    by move=>x hx;split.
  + move=>x hxB.
    have hxS:S x:=(hxB.2 f hf).1.
    have hxU:U x:=hSU x hxS.
    have hIff:=@critical_chart_tangent_zero_iff R m mu k.+1 Y NY hNY Z S p g f x
      (Dr x) (continuous_multilinear_one_operator hW (G x)) hChart hxS
      (norm_class_one_differential hDr hxU) (hDiff x hxU).
    exact:((hIff.1 (hxB.2 f hf)) (e i) (heZ i)).
- move=>T hTS x hx L z y c hOuter hInner hExpansion.
  have hxS:S x:=hTS x hx.
  have hxU:U x:=hSU x hxS.
  have hAgree a (ha:T a) (haU:U a):f a=F a.
    by rewrite /F /r (critical_chart_left_inverse hChart (hTS a ha)).
  have [L0 [hOuter0 hValues]]:=@critical_relative_differential_from_extension
    R X Y NX NY hNX hNY U T F f x
    (continuous_multilinear_one_operator hW (G x)) hx hAgree (hDiff x hxU).
  have hSame:L=L0:=partial_function_single_valued hOuter hOuter0.
  have hActual:partial_function_graph L0 z y by rewrite -hSame.
  have hValue:continuous_multilinear_one_operator hW (G x) z=y:=((hValues z y).1 hActual).2.
  rewrite -hValue hExpansion linear_sum.
  apply:eq_bigr=>i _.
  by rewrite linearZ.
Qed.
