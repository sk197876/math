(** Federer (1969), 3.2.35, p. 271:
    openness supplies radial room at every point
    of the body, before any gauge is chosen. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra.
From Federer Require Import RealNormUP NormMetric.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_open_radial_room]: supporting
    the strict gauge sublevel identification in
    Federer 3.2.35, p. 271. The original
    open set contains a slightly enlarged radial
    multiple of each member. This normed-space
    helper includes zero and assumes no convexity,
    boundedness or gauge representation. *)
Lemma norm_open_radial_room (R:realType) (V:lmodType R)
    (N:V->R) (hN:is_real_norm N) (S:set (real_norm_metric_space hN)) x:
  open S ->S x ->exists c:R,1<c /\S (c*:x).
Proof.
move=>hOpen hx.
have [d hd hBall]:=proj1 (metricType_numDomainType.nbhs_mdistP
  (x:real_norm_metric_space hN) S) (open_nbhs_nbhs (conj hOpen hx)).
have hNx:0<=N x:=real_seminorm_nonnegative hN.1 x.
have hDenominator:0<N x+1 by lra.
pose s:R:=d/(N x+1).
have hs:0<s by rewrite /s divr_gt0.
pose c:R:=1+s.
have hc:1<c by rewrite /c ltrDl.
have hRatio:N x/(N x+1)<1.
  by rewrite ltr_pdivrMr // mul1r ltrDl.
have hProduct:s*N x=d*(N x/(N x+1)).
  by rewrite /s mulrAC -mulrA.
have hSmall:s*N x<d.
  by rewrite hProduct -{2}(mulr1 d) ltr_pM2l.
have hVector:x-c*:x= -s*:x.
  by rewrite -{1}(scale1r x) -scalerBl /c opprD addrA subrr add0r.
exists c; split; first exact hc.
apply:hBall.
change (is_true (N (x-c*:x)<d)).
by rewrite hVector (real_seminorm_scale hN.1)
  normrN (ger0_norm (ltW hs)).
Qed.
