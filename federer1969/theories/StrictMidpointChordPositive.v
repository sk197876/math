(** Federer (1969), 3.3.19, p. 302: elementary
    scalar support for the strict circular chord estimate.
    A continuous strictly midpoint-concave graph lies strictly
    above its endpoint chord. Prove the zero-endpoint form
    by compact minima, using only general topology. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets
  topology num_normedtype pseudometric_normed_Zmodule normed_module lra ring.
From Federer Require Import CompactMaximum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [strict_midpoint_chord_positive]: supporting
    sin(x)>2x/pi for 0<x<pi/2 in 3.3.19, p. 302.
    The generic continuous midpoint argument is proved here;
    no external concavity or calculus theorem is imported. *)
Theorem strict_midpoint_chord_positive (R:realType) (f:R^o->R^o) (L:R):
  0<L ->continuous f ->f 0= 0 ->f L= 0 ->
  (forall u v,0<=u ->u<v ->v<=L ->
    (f u+f v)/2<f ((u+v)/2)) ->
  forall x,0<x ->x<L ->0<f x.
Proof.
move=>hL hf h0 hEnd hStrict.
have hNoMinimum t:0<t ->t<L ->
    (forall u,0<=u ->u<=L ->f t<=f u) ->False.
  move=>ht htL hMin.
  pose d:=Num.min t (L-t)/2.
  have hMinPositive:0<Num.min t (L-t) by rewrite lt_min ht subr_gt0.
  have hTwo:(0<(2:R)) by rewrite ltr0n.
  have hd:0<d by rewrite /d divr_gt0.
  have hdT:d<=t.
    have hm:Num.min t (L-t)<=t by rewrite ge_min lexx.
    rewrite /d; lra.
  have hdL:d<=L-t.
    have hm:Num.min t (L-t)<=L-t by rewrite ge_min lexx orbT.
    rewrite /d; lra.
  have hu:0<=t-d by lra.
  have hv:t+d<=L by lra.
  have huv:t-d<t+d by lra.
  have hS:=hStrict (t-d) (t+d) hu huv hv.
  have hMid:((t-d)+(t+d))/2=t by field.
  rewrite hMid in hS.
  have huL:t-d<=L by lra.
  have hv0:0<=t+d by lra.
  have hA:=hMin (t-d) hu huL.
  have hB:=hMin (t+d) hv0 hv.
  lra.
have hNonempty:(`[0,L]:set R^o)!=set0.
  exists 0;by rewrite /= in_itv /= lexx (ltW hL).
have hNeg:continuous (fun t:R^o=> -f t).
  move=>t;exact:continuousN (hf t).
have [t [ht hMin]]:=@continuous_compact_maximum R R^o `[0,L]
  (fun u=> -f u) hNonempty (@segment_compact R 0 L) hNeg.
have hMin' u:0<=u ->u<=L ->f t<=f u.
  move=>hu huL;have huI:(`[0,L]:set R^o) u by rewrite /= in_itv /= hu huL.
  have hh:=hMin u huI;by rewrite lerN2 in hh.
have /andP[ht0 htL]:(0<=t<=L) by move:ht;rewrite /= in_itv /=.
have htNonnegative:0<=f t.
  case:(eqVneq t 0)=>[->|htN];first by rewrite h0.
  case:(eqVneq t L)=>[->|htNL];first by rewrite hEnd.
  exfalso;apply:(hNoMinimum t).
  - by rewrite lt_neqAle eq_sym htN ht0.
  - by rewrite lt_neqAle htNL htL.
  - exact:hMin'.
have hAll u:0<=u ->u<=L ->0<=f u.
  move=>hu huL;exact:le_trans htNonnegative (hMin' u hu huL).
move=>x hx hxL;case:(ltP 0 (f x))=>hfx=>//.
have hx0:f x= 0 by have hh:=hAll x (ltW hx) (ltW hxL);lra.
exfalso;apply:(hNoMinimum x hx hxL)=>u hu huL.
rewrite hx0;exact:hAll.
Qed.
