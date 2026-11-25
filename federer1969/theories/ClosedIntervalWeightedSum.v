(** Federer (1969), 3.3.20, p. 307:
    the actual projection of a coordinate rectangle is an interval. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets lra ring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [closed_interval_weighted_sum]: supporting
    exact projection intervals in 3.3.20, p. 307.
    Every point between the weighted endpoint sums has
    an actual pair of original interval coordinates.
    Zero weights and degenerate intervals are included. *)
Theorem closed_interval_weighted_sum (R:realType) (a b c d u v z:R):
  a<=b ->c<=d ->0<=u ->0<=v ->
  (u*a+v*c<=z<=u*b+v*d <->
    exists x y,a<=x<=b /\c<=y<=d /\z=u*x+v*y).
Proof.
move=>hab hcd hu hv;split.
- move=>/andP[hl hh].
  pose D:=u*(b-a)+v*(d-c).
  have hD:0<=D by rewrite /D;apply:addr_ge0;apply:mulr_ge0=>//;lra.
  case:(eqVneq D (0:R))=>[hZero|hNonzero].
  + exists a,c;split;first by rewrite lexx hab.
    split;first by rewrite lexx hcd.
    rewrite /D in hZero;nra.
  + have hPositive:0<D by rewrite lt_neqAle eq_sym hNonzero hD.
    pose t:=(z-(u*a+v*c))/D.
    have ht0:0<=t by rewrite /t divr_ge0 // subr_ge0.
    have ht1:t<=1 by rewrite /t ler_pdivrMr // mul1r /D;nra.
    have hCancel:t*D=z-(u*a+v*c) by rewrite /t divfK.
    rewrite /D mulrDr in hCancel.
    exists (a+t*(b-a)),(c+t*(d-c)).
    split;first by apply/andP;split;nra.
    split;first by apply/andP;split;nra.
    nra.
- move=>[x [y [/andP[hax hxb] [/andP[hcy hyd] ->]]]].
  apply/andP;split;nra.
Qed.
