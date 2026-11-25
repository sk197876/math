(** Federer (1969), 4.1.15, p. 372: for each
    fixed r>0 the actual coincidence set lies in the
    displayed smoothing agreement locus when epsilon is small.
    A common Lipschitz bound gives an explicit open tube.
    The set need not be the whole original compact K. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology ring.
From Federer Require Import RealNormUP NormMetric InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct LipschitzUP MetricOpenThickening.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section RadialAgreementNeighbourhood.
Variable R:realType.
Variables n nu:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation MX:=(real_norm_metric_space hNX).
Local Notation MY:=(real_norm_metric_space hNY).
Variables F G:X->Y.
Variable A:set X.
Variables Lf Lg:R.
Hypothesis hF:@is_metric_lipschitz_bound R MX MY setT F Lf.
Hypothesis hG:@is_metric_lipschitz_bound R MX MY setT G Lg.
Hypothesis hAgreement:forall x,A x->F x=G x.

(** Source for [radial_agreement_neighbourhood_ball]: the
    final support containment in Z_(r,epsilon) on p. 372
    of Federer 4.1.15. The explicit smallness condition
    keeps the whole closed smoothing ball in the strict
    agreement region, including dimension zero and zero bounds. *)
Theorem radial_agreement_neighbourhood_ball (r epsilon:R):
  0<epsilon ->2*(Lf+Lg)*epsilon<r ->
  forall x,@metric_open_thickening R MX A epsilon x ->
    forall z,NX (x-z)<=epsilon ->NY (G z-F z)<r.
Proof.
move=>hEpsilon hSmall x [a ha hNear] z hBall.
have hNearValue:NX (a-x)<epsilon:=hNear.
have hNearSym:NX (x-a)<=epsilon.
  rewrite (real_seminorm_subtract hNX.1);exact:ltW hNearValue.
have hBallSym:NX (z-x)<=epsilon.
  rewrite (real_seminorm_subtract hNX.1);exact:hBall.
have hSumVector:(z-x)+(x-a)=z-a by rewrite addrA subrK.
have hTriangleX:=real_seminorm_triangle hNX.1 (z-x) (x-a).
rewrite hSumVector in hTriangleX.
have hDistance:NX (z-a)<=2*epsilon.
  have hValue:=le_trans hTriangleX (lerD hBallSym hNearSym).
  have hTwice:epsilon+epsilon= 2*epsilon by ring.
  by rewrite hTwice in hValue.
have hDifference:(G z-G a)+(-(F z-F a))=G z-F z.
  by rewrite (@hAgreement a ha) opprB addrA subrK.
have hTriangleY:=real_seminorm_triangle hNY.1 (G z-G a) (-(F z-F a)).
rewrite hDifference (real_seminorm_negate hNY.1) in hTriangleY.
have hFirst:=hG.2 z a Logic.I Logic.I.
have hSecond:=hF.2 z a Logic.I Logic.I.
change (is_true (NY (G z-G a)<=Lg*NX (z-a))) in hFirst.
change (is_true (NY (F z-F a)<=Lf*NX (z-a))) in hSecond.
have hTerms:=lerD hFirst hSecond.
have hFactor:Lg*NX (z-a)+Lf*NX (z-a)=(Lf+Lg)*NX (z-a) by ring.
rewrite hFactor in hTerms.
have hCap:=ler_wpM2l (addr_ge0 hF.1 hG.1) hDistance.
have hReorder:(Lf+Lg)*(2*epsilon)= 2*(Lf+Lg)*epsilon by ring.
rewrite hReorder in hCap.
exact:(le_lt_trans (le_trans hTriangleY (le_trans hTerms hCap)) hSmall).
Qed.
End RadialAgreementNeighbourhood.
