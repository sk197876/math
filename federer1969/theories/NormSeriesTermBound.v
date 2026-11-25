(** Federer (1969), 3.1.24, p. 238: uniform
    convergence of a series bounds its sufficiently late terms.
    This supporting estimate uses only the triangle inequality. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import RealNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_uniform_series_late_terms]: supporting the
    choice of r in the implication (4) to (1),
    Federer 3.1.24, p. 238. Consecutive uniformly accurate
    partial sums differ by one term, of norm at most 1. *)
Lemma norm_uniform_series_late_terms (R:realType) (X:Type) (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_seminorm NY) (U:X->Prop)
    (f:X->Y) (P:nat->X->Y) :
  (forall eps:R,0<eps -> exists n:nat,forall N,(n<=N)%N ->
    forall x,U x -> NY (f x-\sum_(m<N.+1) P m x)<eps) ->
  exists n:nat,forall m,(n<m)%N -> forall x,U x -> NY (P m x)<=1.
Proof.
move=>hc.
have he:0<(1:R)/2 by rewrite divr_gt0 // ltr0n.
have [n hn]:=hc (1/2) he.
exists n; move=>[|m] hm; first by [].
move=>x hx.
have hn0:(n<=m)%N by move:hm; rewrite ltnS.
have hn1:(n<=m.+1)%N:=leq_trans hn0 (leqnSn m).
have ha:=hn m hn0 x hx.
have hb:=hn (m.+1) hn1 x hx.
pose S:=\sum_(i<m.+1) P i x.
have hid:(f x-S)-(f x-(S+P (m.+1) x))= P (m.+1) x.
  have hs:f x-(S+P (m.+1) x)= (f x-S)-P (m.+1) x.
    by rewrite opprD addrA.
  by rewrite hs subKr.
have ht:=real_seminorm_triangle hNY (f x-S) (-(f x-(S+P (m.+1) x))).
rewrite hid (real_seminorm_negate hNY) in ht.
rewrite big_ord_recr /= -/S in hb.
have hs:=ltrD ha hb.
have heq:(1:R)/2+1/2= 1 by lra.
rewrite heq in hs.
exact (le_trans ht (ltW hs)).
Qed.
