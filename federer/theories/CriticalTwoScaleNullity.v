(** Federer (1969), 3.4.2(8), pp. 315–316: the actual
    two-scale cube cover has zero real-dimensional Hausdorff cost. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra ring.
From Federer Require Import ModuleQuotient GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric RealNormUP NormMetric RealPower RealPowerContinuity
  EuclideanCoordinateCubeUP EqualCoordinateCubeGridUP MetricDiameterUP MetricDiameter
  MetricScaleEnvelopeUP HausdorffLengthUP MetricRealPowerCost MetricRealPowerMeasure
  CaratheodoryLimitUP CaratheodoryBorelRegular MeasureUP MeasureBasic
  ExtendedRealReciprocalBounds RealPowerCutoffFiniteCover CriticalTwoScaleGrid
  CriticalTwoScaleBudget CriticalTwoScaleMesh CriticalTwoScaleDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_two_scale_cube_nullity]: the limiting
    finite-cover argument in 3.4.2(8), pp. 315–316. An original
    subset of a product of two equal-side cubes has null image
    at degree b+a/lambda when its first-block oscillation tends
    to zero at order lambda and its second-block increments are
    Lipschitz. These are supporting hypotheses to be derived for
    the original projection chart. No source measurability, target
    dimension, completeness, or covering conclusion is assumed. *)
Theorem critical_two_scale_cube_nullity (R:realType) a b
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (F:R_n R a->R_n R b->Y) (P:set (R_n R a*R_n R b))
    (u:R_n R a) (v:R_n R b) (r D M lambda c:R)
    (QA:set (inner_metric_space (@euclidean_inner_productP R a)))
    (QB:set (inner_metric_space (@euclidean_inner_productP R b))):
  (0<a)%N ->0<r ->0<lambda ->0<=D ->0<=M ->0<=c ->
  is_euclidean_coordinate_cube u r QA ->is_euclidean_coordinate_cube v r QB ->
  (forall z,P z ->QA z.1 /\QB z.2) ->
  (forall eps,0<eps ->exists delta,0<delta /\forall q w x,
    P (q,w) ->QA x ->inner_norm (@euclidean_inner_productP R a) (x-q)<=delta ->
    NY (F x w-F q w)<=eps*D*real_power
      (inner_norm (@euclidean_inner_productP R a) (x-q)) lambda) ->
  (forall x w z,QA x ->QB w ->QB z ->NY (F x w-F x z)<=
    M*inner_norm (@euclidean_inner_productP R b) (w-z)) ->
  @metric_real_power_measure R (real_norm_metric_space hNY) c (b%:R+a%:R/lambda)
    ((fun z=>F z.1 z.2) @` P)=0%E.
Proof.
move=>ha hr hLambda hD hM hc hQA hQB hP hFlat hLip.
pose X:=real_norm_metric_space hNY.
pose A:set X:=(fun z:R_n R a*R_n R b=>F z.1 z.2) @` P.
pose t:=a%:R/lambda.
pose sigma:=(b%:R:R)+t.
have ht:0<t by rewrite /t divr_gt0 // ltr0n.
have hSigma:0<=sigma by apply:addr_ge0;[exact:ler0n|exact:ltW ht].
pose N:=D*real_power a%:R lambda+M*b%:R+1.
have hFirst:0<=D*real_power a%:R lambda:=mulr_ge0 hD (real_power_nonnegative _ _).
have hSecond:0<=M*b%:R:=mulr_ge0 hM (ler0n R b).
have hN:0<N by rewrite /N;lra.
pose K:=c*real_power N sigma*r^+(a+b).
have hK:0<=K:=mulr_ge0 (mulr_ge0 hc (real_power_nonnegative _ _))
  (exprn_ge0 _ (ltW hr)).
have hKOne:0<K+1 by lra.
apply/eqP;rewrite eq_le
  (measure_nonnegative (@metric_real_power_measure_is_measure R X c sigma hc)) andbT.
apply:(caratheodory_limit_least (@metric_real_power_measure_specification R X c sigma))
  =>cutoff nu hCutoff hNu.
apply:(@extended_real_reciprocal_upper_bound R (nu A) 0)=>n;rewrite add0r.
pose e:=(n.+1%:R:R)^-1.
have he:0<e by rewrite /e invr_gt0 ltr0n.
pose root:=real_power (e/(K+1)) t^-1.
have hArgument:0<e/(K+1) by rewrite divr_gt0.
have hRoot:0<root:=real_power_strictly_positive _ hArgument.
pose eps:=root/2.
have hEps:0<eps by rewrite /eps divr_gt0 // ltr0n.
have hPower:real_power (2*eps) t=e/(K+1).
  have hEq:2*eps=root by rewrite /eps;field.
  rewrite hEq;exact:real_power_inverse_power (ltW hArgument) ht.
have hSmallCost:K*real_power (2*eps) t<=e.
  rewrite hPower.
  have hIncrease:K<=K+1 by lra.
  have hBound:=ler_wpM2r (ltW hArgument) hIncrease.
  have hEq:(K+1)*(e/(K+1))=e by field;by rewrite gt_eqF.
  by rewrite hEq in hBound.
have [delta [hDelta hEstimate]]:=hFlat eps hEps.
have [nCut hCap]:=reciprocal_metric_cutoffs_cofinal hCutoff.
pose cap:=(nCut.+1%:R:R)^-1.
have hPositiveCap:0<cap by rewrite /cap invr_gt0 ltr0n.
have [alpha [beta [h [j hMesh]]]]:=@critical_two_scale_mesh_exists R a
  r eps lambda delta N cap hr hEps hLambda hDelta hN hPositiveCap.
have [hAlpha [hBeta [hh [hj [hAH [hBJ [hSource [hLow [hHigh hImage]]]]]]]]]:=hMesh.
have [AG hAG]:=equal_coordinate_cube_grid_exists u hAlpha (ltW hh).
have [BG hBG]:=equal_coordinate_cube_grid_exists v hBeta (ltW hj).
have [S [hCover hDiam]]:=@critical_two_scale_grid_cover R a b alpha beta Y NY hNY
  F P u v r h j (eps*D) M lambda delta QA QB AG BG hQA hQB hAG hBG
  (esym hAH) (esym hBJ) (mulr_ge0 (ltW hEps) hD) hM hLambda hSource hP hEstimate hLip.
pose I:finType:=[the finType of (coordinate_cube_grid_indices a alpha*
  coordinate_cube_grid_indices b beta)%type].
have hDiamBound i:(extended_metric_diameter (S i)<=(N*j)%:E)%E.
  apply:(le_trans (hDiam i));rewrite lee_fin.
  exact:critical_two_scale_diameter_bound (ltW hh) (ltW hj) (ltW hEps) hD hM hLow.
have hRho:0<=N*j:=mulr_ge0 (ltW hN) (ltW hj).
have hRhoCap:((N*j)%:E<=cutoff)%E.
  apply:(le_trans _ hCap);by rewrite lee_fin.
have hBound:=@real_power_cutoff_finite_equal_diameter_cover R X I c sigma
  cutoff nu A S (N*j) hNu hc hSigma hRho hRhoCap hDiamBound hCover.
have hCard:(#|I|%:R:R)=(alpha%:R)^+a*(beta%:R)^+b.
  by rewrite /I /coordinate_cube_grid_indices card_prod !card_ffun !card_ord natrM !natrX.
rewrite hCard in hBound.
have hBudget:=@critical_two_scale_power_budget R a b alpha beta r h j eps N c lambda
  ha hLambda hr hh hj hEps (ltW hN) hc hAH hBJ hHigh.
apply:(le_trans hBound);rewrite lee_fin.
exact:le_trans hBudget hSmallCost.
Qed.
