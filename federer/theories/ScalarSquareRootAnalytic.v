(** Federer (1969), 3.1.24, p. 240: the
    positive square root in the quadratic scalar inverse is
    analytic. The factorial bounds are proved from its actual
    derivative sequence on a small positive interval. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals ring lra.
From Federer Require Import Hom RealNormUP NormHigherCurveDerivativeUP NormDifferentialUP NormDifferentialLocal NormOpenDomainLaws
  NormAnalyticUP NormScalarDerivativeAnalytic AnalyticArithmeticBounds
  ScalarSquareRootCoefficients ScalarSquareRootHigherDifferentials.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_square_root_local_coefficient_bound]:
    supporting the square root in Federer 3.1.24, p. 240.
    On |x-a|<a/2, its mth derivative has absolute value
    at most m! sqrt(2a) (2/a)^m. Absorbing the fixed
    factor in a positive mth power proves condition (1). *)
Lemma scalar_square_root_local_coefficient_bound (R:realType) (a x:R) m :
  0<a -> `|x-a|<a/2 -> (1<=m)%N ->
  `|scalar_square_root_derivative_coefficient m x|<=
    (((Num.sqrt (2*a)+1)*(2/a))^+m)*(m`!)%:R.
Proof.
move=>ha hx hm.
have hdist1:=ler_norm (x-a); have hdist2:=ler_norm (-(x-a)).
rewrite normrN in hdist2.
have hx0:0<x by lra.
have hxa:a/2<=x by lra.
have hx2:x<=2*a by lra.
have hs:0<=Num.sqrt x:=sqrtr_ge0 _.
have hM:0<=Num.sqrt (2*a):=sqrtr_ge0 _.
have hroot:Num.sqrt x<=Num.sqrt (2*a):=ler_wsqrtr hx2.
have hrec:0<=x^-1 by rewrite invr_ge0; exact: ltW.
have htwo:0<=2/a by rewrite divr_ge0 ?ler0n //; exact: ltW.
have hxinv:x^-1<=2/a.
  rewrite ler_pdivlMr //.
  have hxx:x*x^-1= 1 by rewrite mulfV // gt_eqF.
  nra.
have hpower:(x^-1)^+m<=(2/a)^+m:=lerXn2r m hrec htwo hxinv.
rewrite /scalar_square_root_derivative_coefficient !normrM normrX
  (ger0_norm hs) (ger0_norm hrec).
have hbase:=ler_wpM2r (exprn_ge0 m hrec)
  (le_trans (ler_wpM2r hs (square_root_falling_factorial_bound R m))
    (ler_wpM2l (ler0n R (m`!)) hroot)).
have hbound:=le_trans hbase (ler_wpM2l (mulr_ge0 (ler0n R (m`!)) hM) hpower).
have hscl:=@analytic_scalar_factor_bound R (Num.sqrt (2*a)) (2/a) m hM htwo hm.
have hEq:(m`!)%:R*Num.sqrt (2*a)*(2/a)^+m=
  (Num.sqrt (2*a)*(2/a)^+m)*(m`!)%:R by ring.
rewrite hEq in hbound.
exact (le_trans hbound (ler_wpM2r (ler0n R (m`!)) hscl)).
Qed.

(** Source for [scalar_square_root_analytic_at]: the positive
    square root is analytic at every positive argument,
    supporting the explicitly solved quadratic inverse in Federer
    3.1.24, p. 240. The proof uses actual scalar
    derivatives on an open ball contained in the positive domain. *)
Theorem scalar_square_root_analytic_at (R:realType) (a:R) :
  0<a -> @norm_analytic_at R R^o R^o (fun t=>`|t|) (fun t=>`|t|)
    (scalar_absolute_value_norm R) (scalar_absolute_value_norm R) (fun t=>0<t) Num.sqrt a.
Proof.
move=>ha.
pose U:=fun x:R=>`|x-a|<a/2.
have hUa:U a by rewrite /U subrr normr0 divr_gt0 // ltr0n.
have hopen x (hx:U x):norm_domain_interior (fun t:R^o=>`|t|) U x.
  exact (@norm_open_ball_domain_interior R R^o (fun t=>`|t|) (scalar_absolute_value_norm R) a (a/2) x hx).
have hUpos x (hx:U x):0<x.
  change (is_true (`|x-a|<a/2)) in hx.
  have hh:=ler_norm (-(x-a)); rewrite normrN in hh; lra.
have hF m x (hx:U x):has_norm_differential (fun t:R^o=>`|t|) (fun t:R^o=>`|t|)
    U (scalar_square_root_derivative_coefficient m) x
    (@scalar_coefficient_linear_map R R^o (scalar_square_root_derivative_coefficient m.+1 x)).
  exact (@norm_differential_restrict R R^o R^o (fun t=>`|t|) (fun t=>`|t|)
    (fun t=>0<t) U (scalar_square_root_derivative_coefficient m) x
    (@scalar_coefficient_linear_map R R^o (scalar_square_root_derivative_coefficient m.+1 x))
    hUpos (hopen x hx) (scalar_square_root_derivative_step m (hUpos x hx))).
have hh:=@norm_scalar_derivative_analytic_at R U (@scalar_square_root_derivative_coefficient R)
  a ((Num.sqrt (2*a)+1)*(2/a)) hUa hF
  (fun m hm x hx=>@scalar_square_root_local_coefficient_bound R a x m ha hx hm).
have he:(@scalar_square_root_derivative_coefficient R 0)= Num.sqrt.
  apply: funext=>x; exact: scalar_square_root_derivative_zero.
rewrite he in hh.
move:hh=>[V [c [haV [hVU [hc hb]]]]].
exists V,c; split; first exact haV.
split; first by move=>x hx; exact (hUpos x (hVU x hx)).
by split.
Qed.
