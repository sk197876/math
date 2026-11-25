(** Federer (1969), 3.4.8(11), pp. 333–335:
    after choosing one sufficiently small radius,
    every smaller positive ball outside an original
    analytic zero set has finitely many components.
    This is the exact uniform input used by
    the nested Weierstrass-neighbourhood construction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology lra.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
  EuclideanInnerProduct InnerNorm HilbertFormCompactness NormDifferentialUP NormOpenDomainLaws
  NormAnalyticUP NormAnalyticLocal NormAnalyticOperations NormRegularity SetGermUP
  FiniteAnalyticVarietyUP GermVanishingSealed AnalyticDepthSealed AnalyticBallComponentsInduction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmallBalls.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n.+1).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n.+1)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n.+1)).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation germ:=(@set_germ T 0).
Local Notation depth:=(@AnalyticDepth.value R X (@euclidean_inner_product R n.+1)
  (@euclidean_inner_productP R n.+1) n.+1 (@coordinate_basis R n.+1) (@coordinate_basisP R n.+1)
  (dual_basis (@coordinate_basisP R n.+1))).
Local Notation ideal:=(@AnalyticSetIdeal.value R X NX hNX 0).

(** Source for [analytic_small_ball_components_from_lower_depth]:
    the uniform original base-ball component bound
    in 3.4.8(11), pp. 333–335. The
    radius is chosen from the original analytic
    domain; all positive radii below it remain
    admissible. The only induction input concerns
    strictly smaller original depths. *)
Theorem analytic_small_ball_components_from_lower_depth (A:set X) (phi:X->R^o):
  A 0 ->
  @norm_analytic R X R^o NX (fun z:R^o=>`|z|) hNX (@scalar_absolute_value_norm R) A phi ->
  (forall W L:set X,W 0 ->@is_finite_analytic_variety R X NX hNX W L ->
    germ L<>germ set0 ->(depth (ideal (germ L))<n.+1)%N ->
    exists U:set X,@open T U /\U 0 /\
      finite_set (@connected_component T L @` (L `&` U))) ->
  exists r:R,0<r /\[set x|NX x<=r] `<=` A /\
    forall s:R,0<s ->s<=r ->finite_set
      (@connected_component T [set x|NX x<s /\phi x<>0] @`
        [set x|NX x<s /\phi x<>0]).
Proof.
move=>hA0 hAnalytic hInduction.
have hClassZero:=norm_class_continuous (norm_analytic_class_all_orders hAnalytic 0%N).
have [rho [hRho hDomain]]:=(hClassZero 0 hA0).1.
pose B:set X:=[set x|NX x<rho].
have hBA:B `<=` A.
  move=>x hx;have h:=hDomain x hx;by rewrite add0r in h.
have hInterior x (hx:B x):norm_domain_interior NX B x.
  have hBall:=@norm_open_ball_domain_interior R X NX hNX 0 rho x.
  have hBallX:is_true (NX (x-0)<rho) by rewrite subr0.
  have hOriginal:=hBall hBallX.
  have hEqual:(fun y=>is_true (NX (y-0)<rho)) = B.
    apply:funext=>y;change (is_true (NX (y-0)<rho) = is_true (NX y<rho));by rewrite subr0.
  by rewrite hEqual in hOriginal.
have hAnalyticB:=@norm_analytic_open_restriction R X R^o NX (fun z:R^o=>`|z|)
  hNX (@scalar_absolute_value_norm R) A B phi hBA hInterior hAnalytic.
exists (rho/2);split;first by lra.
split.
- move=>x hx;change (is_true (NX x<=rho/2)) in hx.
  apply:hBA;change (is_true (NX x<rho));by lra.
- move=>s hs hSR.
  have hSmall:s<rho by lra.
  exact:(@analytic_ball_components_from_lower_depth R n phi rho s hs hSmall hAnalyticB hInduction).
Qed.
End SmallBalls.
