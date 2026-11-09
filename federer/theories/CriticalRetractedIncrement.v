(** Federer (1969), 3.4.2(6), p. 312: the increment estimate
    obtained by integrating along the retracted segment. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import Hom ModuleQuotient GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness RealNormUP NormDifferentialUP NormClassOneUP
  NormDifferentialAffineLine NormHigherCurveDerivativeUP EuclideanProjectionSpace CriticalManifoldFamilyUP
  CriticalManifoldChartLaws CriticalCompactTube CriticalRetractedSegment
  CriticalChartRetractionDifferential CriticalChartCompositeDerivative
  CriticalLocalDerivativeBound CriticalZetaVectorBound CriticalOscillationScalarBound
  CriticalCurveEndpointBound CriticalOscillation RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Increment.
Variable R:realType.
Variables m mu k:nat.
Local Notation X:=(R_n R m).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R m)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R m)).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable Z:subspace X.
Variable S C T:set X.
Variable p:euclidean_projection_space R m mu.
Variable g:R_n R mu->X.
Hypothesis hChart:is_critical_manifold_chart k Z S p g.
Variable f:X->Y.
Local Notation P:=(euclidean_projection_linear p).
Local Notation r:=(fun x=>g (P x)).
Local Notation U:=(fun x=>(P @` S) (P x)).
Local Notation F:=(fun x=>f (r x)).

(** Source for [critical_retracted_increment_bound]: the estimate
    for |f(x)-f(c)| in the proof of 3.4.2(6), p. 312. The original
    relative differential and ζ bound the derivative of f composed
    with the retracted segment. Apply the mean-value estimate on
    positive parameter intervals and use continuity at zero. The
    target is an arbitrary normed space. *)
Theorem critical_retracted_increment_bound e M lambda delta b x c:
  is_critical_source_tube C e T ->C `<=` S ->T `<=` U ->1<=M ->
  (forall a b,T a ->T b ->NX (r a-r b)<=M*NX (a-b)) ->
  norm_class_one NX NX U r ->norm_class_one NX NY U F ->
  1<=lambda ->0<=b ->
  critical_zeta hNY Z S C f (lambda-1) (M*delta)=b%:E ->
  S x ->C c ->Z (x-c) ->0<NX (x-c)<=delta ->delta<e ->
  NY (f x-f c)<=real_power M lambda*b*real_power (NX (x-c)) lambda.
Proof.
move=>hTube hCS hTU hM hLip [Dr hDr] [DF hDF] hLambda hb hValue
  hx hc hZ hDist hDelta.
pose w:=x-c.
pose K:=real_power M lambda*b*real_power (NX w) lambda.
have hK:0<=K.
  exact:(mulr_ge0 (mulr_ge0 (real_power_nonnegative M lambda) hb)
    (real_power_nonnegative (NX w) lambda)).
pose A:=fun t:R^o=>U (c+t*:w).
pose q:=fun t:R^o=>F (c+t*:w).
have hcS:S c:=@hCS c hc.
have hcU:U c by exists c.
have hD0:has_norm_differential NX NY U F (c+0*:w) (DF c).
  rewrite scale0r addr0;exact:(norm_class_one_differential hDF hcU).
have hQ0:norm_differentiable_at (fun t:R^o=>`|t|) NY A q 0.
  exists (hom_comp (DF c) (scalar_coefficient_linear_map w)).
  exact:(norm_differential_along_affine_line hNX hNY hD0).
have hQ t (ht:0<t) (ht1:t<=1):exists L:Hom R^o Y,
    has_norm_differential (fun s:R^o=>`|s|) NY A q t L /\
    forall s:R^o,NY (L s)<=K*`|s|.
  have hTime:0<t<=1 by apply/andP;split.
  have [hInterior [haS [haZ [haDist haBound]]]]:=
    @critical_retracted_segment_geometry R m mu k Z S C T p g hChart e M
      hTube hCS hTU hM hLip x c delta t hx hc hZ hDist hDelta hTime.
  pose a:=c+t*:w.
  have haT:T a:=norm_domain_interior_member hNX hInterior.
  have haU:U a:=@hTU a haT.
  have hbU:U (r a) by exists (r a).
  have hDR:=norm_class_one_differential hDr haU.
  have hDA:=norm_class_one_differential hDF haU.
  have hDB:=norm_class_one_differential hDF hbU.
  have [L [hOuter hInner]]:=
    @critical_chart_composite_relative_derivative R m mu k Z S p g hChart Y NY hNY
      f a (Dr a) (DF a) (DF (r a)) hDR hDA hDB.
  have hZw:Z w:=hZ.
  have hZSpeed:=critical_retraction_differential_preserves_subspace hChart hDR hZw.
  have hDerivative:=@critical_zeta_tangent_vector_bound R m Y NY hNY Z S C f
    (lambda-1) (M*delta) b (r a) c (Dr a w) L (DF a w)
      hValue haS hc haZ haDist hZSpeed hOuter (hInner w).
  have hSpeed:=@critical_local_lipschitz_differential_bound R X X NX NX hNX hNX
    U T r a (Dr a) M hDR hInterior hLip w.
  have hMpositive:0<M:=lt_le_trans ltr01 hM.
  have hScalar:=@critical_power_derivative_factor_bound R
    (NX (Dr a w)) (NX (r a-c)) M (NX w) b lambda
    (inner_norm_nonnegative _ _) (inner_norm_nonnegative _ _) hMpositive
    (andP hDist).1 hb hLambda hSpeed haBound.
  have hResult:NY (DF a w)<=K:=le_trans hDerivative hScalar.
  exists (hom_comp (DF a) (scalar_coefficient_linear_map w));split.
  - exact:(norm_differential_along_affine_line hNX hNY hDA).
  - move=>s;change (is_true (NY (DF a (s*:w))<=K*`|s|)).
    rewrite (Bilinear.linZ (hom_linear (DF a))) (real_seminorm_scale hNY.1).
    have hh:=ler_wpM2l (normr_ge0 s) hResult.
    by rewrite (mulrC K) in hh |- *.
have hBound:=critical_curve_positive_parameter_bound hNY hK hQ0 hQ.
have hQ1:q 1=f x.
  rewrite /q scale1r (addrC c w) /w subrK.
  by rewrite (critical_chart_left_inverse hChart hx).
have hQzero:q 0=f c.
  rewrite /q scale0r addr0.
  by rewrite (critical_chart_left_inverse hChart hcS).
by rewrite hQ1 hQzero in hBound.
Qed.
End Increment.
