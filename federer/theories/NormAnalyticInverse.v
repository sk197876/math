(** Federer (1969), 3.1.24, pp. 239–240: a class-one map
    with an analytic inverse is analytic, on its actual open domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals ring lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearUP ContinuousMultilinearSealed
  ContinuousMultilinearNorm NormClassOneUP NormClassZeroTopology NormClassZeroLocalBound
  NormClassZeroComposition NormRegularity NormRegularityOperations NormLinearDomainLaws NormOpenDomainLaws
  NormHigherDifferentialUP NormHigherDifferentialLocal NormHigherDifferentialUnique NormSmoothFields
  NormAnalyticUP NormAnalyticLocal NormAnalyticBoundNonnegative
  InverseMajorantUP InverseMajorantSealed InverseDifferentialMajorant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_analytic_inverse_from_first]: the inverse
    assertion in Federer 3.1.24, p. 239, with the scalar
    majorant proof on p. 240. The first derivative is locally
    bounded by M>0. Choose gamma>0 bounding the inverse derivatives
    and beta=(M gamma)^-1. The proved opaque majorant sequence bounds
    every higher derivative and has a finite exponential bound.
    Neither completeness nor finite dimension is assumed. *)
Theorem norm_analytic_inverse_from_first (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:X->Prop) (B:Y->Prop) (f:X->Y) (g:Y->X) :
  (forall x,A x -> B (f x)) -> (forall y,B y -> A (g y)) ->
  (forall x,A x -> g (f x)=x) -> (forall y,B y -> f (g y)=y) ->
  norm_class hNX hNY A f 1%N -> @norm_analytic R Y X NY NX hNY hNX B g ->
  @norm_analytic R X Y NX NY hNX hNY A f.
Proof.
move=>hfmap hgmap hgf hfg hf1 hgAnal.
have hg:=norm_analytic_class_all_orders hgAnal.
have hf:norm_class_all_orders hNX hNY A f.
  move=>k; exact (@norm_class_inverse_from_first R Y X NY NX hNY hNX B A g f k
    hgmap hfmap hfg hgf (hg k) hf1).
pose Z i:=@ContinuousMultilinear.space R i X Y NX NY hNX hNY.
pose ez i:=@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY.
pose ZN i:=@ContinuousMultilinear.norm R i X Y NX NY hNX hNY.
pose hZ i:=@ContinuousMultilinear.laws R i X Y NX NY hNX hNY.
have [F hF]:=@norm_smooth_fields_exist R X Y NX NY hNX hNY A f hf.
move=>a ha.
have [U [c [hfa [hUB [hgU hGb]]]]]:=hgAnal (f a) (hfmap a ha).
have hc:=norm_analytic_operator_witness_nonnegative hfa hgU hGb.
pose gamma:=c+1.
have hgamma:0<gamma by rewrite /gamma; lra.
have hcg:c<=gamma by rewrite /gamma; lra.
have [r [M [hr [hM hball]]]]:=@norm_class_zero_local_bound R X (Z 1%N) NX (@ZN 1%N) hNX
  (continuous_multilinear_norm_is_norm hNY (hZ 1%N)) A (F 1%N) a (hF 1%N).2 ha.
pose V:=fun x=>NX (x-a)<r /\ A x /\ U (f x).
have hVa:V a by rewrite /V subrr (real_seminorm_zero hNX.1); split=>//; by split.
have hVOpen x (hx:V x):norm_domain_interior NX V x.
  apply:norm_domain_intersection_interior.
  - exact (@norm_open_ball_domain_interior R X NX hNX a r x hx.1).
  - exact (@norm_class_zero_composite_interior R X Y X NX NY NX A U f g
      (hf 0%N).1 (hgU 0%N).1 x hx.2).
have hfV:norm_class_all_orders hNX hNY V f.
  move=>k; exact (@norm_class_open_restriction R X Y NX NY hNX hNY A V f k
    (fun x hx=>hx.2.1) hVOpen (hf k)).
pose beta:=(M*gamma)^-1.
have hbeta:0<beta by rewrite /beta invr_gt0 mulr_gt0.
pose lambda:=@InverseMajorant.sequence R beta gamma hbeta hgamma.
have hLambda:=@InverseMajorant.laws R beta gamma hbeta hgamma.
have hFirstEq:lambda 1%N=M.
  rewrite /lambda hLambda.2.1 /beta.
  have hM0:M!=0 by rewrite gt_eqF.
  have hg0:gamma!=0 by rewrite gt_eqF.
  by field; rewrite hM0 hg0.
have hFirst x (hx:V x) (z:Z 1%N):
    has_norm_higher_differential NX ez ZN V f 1%N x z -> ZN 1%N z<=lambda 1%N.
  move=>hz; rewrite hFirstEq.
  have hzA:=(@norm_higher_differential_open_restriction R X Y NX NY hNX hNY Z ez ZN hZ
    1%N A V f (fun t ht=>ht.2.1) hVOpen x hx z).2 hz.
  have heq:=norm_higher_differential_unique hNX hNY hZ hzA ((hF 1%N).1 x hx.2.1).
  rewrite heq; exact (hball x hx.1).2.
have hOuter m (hm:(2<=m)%N) y (hy:U y)
    (z:@ContinuousMultilinear.space R m Y X NY NX hNY hNX):
    has_norm_higher_differential NY
      (fun j=>@ContinuousMultilinear.evaluation R j Y X NY NX hNY hNX)
      (fun j=>@ContinuousMultilinear.norm R j Y X NY NX hNY hNX) U g m y z ->
    @ContinuousMultilinear.norm R m Y X NY NX hNY hNX z<=gamma^+m*(m`!)%:R.
  move=>hz.
  apply:le_trans (hGb m (leq_trans (leqnSn 1%N) hm) y hy z hz) _.
  have hpow:c^+m<=gamma^+m.
    apply:lerXn2r; [exact hc|exact (ltW hgamma)|exact hcg].
  exact (ler_wpM2r (ler0n _ _) hpow).
have hBound:=@inverse_differential_majorant R X Y NX NY hNX hNY A B V U f g
  beta gamma lambda hfmap hgmap hgf hfg (fun x hx=>hx.2) hUB hfV hgU
  hbeta hgamma hLambda hFirst hOuter.
have [C [hC hCb]]:=@InverseMajorant.exponential_bound R beta gamma hbeta hgamma.
exists V,C; split; first exact hVa.
split; first by move=>x hx; exact hx.2.1.
split; first exact hfV.
move=>p hp x hx z hz.
apply:le_trans (hBound p hp x hx z hz) _.
exact (ler_wpM2r (ler0n _ _) (hCb p hp)).
Qed.
