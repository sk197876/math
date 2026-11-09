(** Federer (1969), 3.3.19, p. 302: all
    three large-subdivision inequalities in the original
    choice of delta. The positive numerical margins
    are proved from actual scalar laws, not supplied. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets lra.
From Federer Require Import RealTrigonometryUP CircularTrigonometryUP CircularTrigonometrySealed
  CircularHalfPeriodLower CircularCoefficientLimit NaturalScaledReciprocalTail.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Margins.
Variable R:realType.
Local Notation S:=(@CircularTrigonometry.sine R).
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation ht:=(@CircularTrigonometry.laws R).
Local Notation hb:=(circular_trig_basic ht).

(** Source for [circular_coefficient_large_subdivision]:
    for every original 0<lambda<pi, all sufficiently
    large n satisfy n>=5, (n-1)sin(pi/n)>lambda
    and (n-1)sin(pi/n)-1>lambda(1/2+1/(n+1)),
    exactly the three inequalities in 3.3.19, p. 302. *)
Theorem circular_coefficient_large_subdivision (lam:R):0<lam ->lam<p ->
  exists N:nat,forall n,(N<=n)%N ->
  (5<=n)%N /\lam<(n%:R-1)* S (p/n%:R) /\
    lam*(1/2+(n.+1)%:R^-1)<(n%:R-1)* S (p/n%:R)-1.
Proof.
move=>hlam hlamP.
have hp3:=@circular_half_period_at_least_three R.
have hMargin1:0<p-lam by lra.
have hMargin2:0<p-1-lam/2 by lra.
pose e:R:=Num.min ((p-lam)/4) ((p-1-lam/2)/4).
have he1:0<(p-lam)/4 by rewrite divr_gt0 ?ltr0n.
have he2:0<(p-1-lam/2)/4 by rewrite divr_gt0 ?ltr0n.
have he:0<e by rewrite /e lt_min he1 he2.
have hE1:e<=(p-lam)/4 by rewrite /e ge_min lexx.
have hE2:e<=(p-1-lam/2)/4 by rewrite /e ge_min lexx orbT.
have [N1 hCoefficient]:=@circular_coefficient_limit R e he.
have [N2 hTail]:=@natural_scaled_reciprocal_tail R lam e hlam he.
pose N:=maxn 5 (maxn N1 N2).
have hN5:(5<=N)%N:=leq_maxl _ _.
have hN1:(N1<=N)%N:=leq_trans (leq_maxl _ _) (leq_maxr _ _).
have hN2:(N2<=N)%N:=leq_trans (leq_maxr _ _) (leq_maxr _ _).
exists N=>n hn.
have hn5:(5<=n)%N:=leq_trans hN5 hn.
have hn1:(N1<=n)%N:=leq_trans hN1 hn.
have hn2:(N2<=n.+1)%N:=leq_trans (leq_trans hN2 hn) (leqnSn n).
have [_ hApprox]:=hCoefficient n hn1.
have /andP[hLower hUpper]:(-e<(n%:R-1)* S (p/n%:R)-p<e).
  by move:hApprox;rewrite ltr_norml.
have [_ hSmall]:=hTail n.+1 hn2.
split=>//;split;first by lra.
have hInv:(lam*(1/2+n.+1%:R^-1)=lam/2+lam/n.+1%:R) by rewrite mulrDr div1r.
rewrite hInv.
have hStep1:lam/2+lam/n.+1%:R<lam/2+e by rewrite ltrD2l.
have hStep2:lam/2+e<=p-e-1 by lra.
have hStep3:p-e-1<(n%:R-1)* S (p/n%:R)-1 by lra.
exact:lt_trans hStep1 (le_lt_trans hStep2 hStep3).
Qed.
End Margins.
