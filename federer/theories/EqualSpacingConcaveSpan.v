(** Federer (1969), 2.10.28(4), proof p. 193: the convex-combination
    calculation for a span of equally spaced equal-cost intervals. Set
    u=p/(n-1), where p is the difference of two child indices. The weighted
    cost is (p+1)h(s). *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import ConcaveIntervalGaugeUP ConcaveIntervalGaugeLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [equal_spacing_concave_span_bound]: supporting
    h(p*t+s)>=(p+1)h(s) calculation in
    2.10.28(4), p. 193, with n>=2,
    0<=p<=n-1 and h(s)=h(d)/n.
    State the scalar calculation for real n;
    the interval-family application uses n%:R. *)
Lemma equal_spacing_concave_span_bound (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) (d s N t p : R) :
  0<d -> 0<s -> 1<N -> 0<=p -> p<=N-1 ->
  h s=h d/N -> t=(d-s)/(N-1) -> (p+1)*h s<=h (p*t+s).
Proof.
move=> hd hs hN hp hpN hcost ht.
have hN0 : 0<N by lra.
have hden : 0<N-1 by rewrite subr_gt0.
have hden0 : N-1!=0 by rewrite gt_eqF.
pose u := p/(N-1).
have hu : 0<=u by rewrite /u divr_ge0 //; exact: ltW hden.
have hu1 : u<=1 by rewrite /u ler_pdivrMr // mul1r.
have hprod : u*(N-1)=p by rewrite /u divfK.
have hcostN : h d=N*h s by rewrite hcost mulrC divfK ?gt_eqF.
have hpoint : (1-u)*s+u*d=p*t+s by rewrite /u ht; lra.
have hcoefficient : (1-u)*h s+u*h d=(p+1)*h s.
  rewrite hcostN.
  have hh := congr1 (fun v : R=>v*h s) hprod.
  lra.
have hh := @concave_interval_gauge_concavity R h hg s d u (ltW hs) (ltW hd) hu hu1.
by rewrite hpoint hcoefficient in hh.
Qed.
