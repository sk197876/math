(** Federer (1969), 3.3.20, p. 307:
    exact overlap criterion for the four original projected intervals. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets lra ring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_projected_interval_union]: the four
    intervals printed in 3.3.20, p. 307,
    for original nonnegative ordered direction coordinates.
    This auxiliary scalar union makes no measure or
    overlap assertion in its definition. *)
Definition binary_projected_interval_union (R:realType) (s u v:R):set R:=
  (`[0,s*(u+v)] `|` `[(1-s)*v,s*u+v] `|`
    `[(1-s)*u,u+s*v] `|` `[(1-s)*(u+v),u+v])%classic.

(** Source for [binary_projected_interval_overlap]: the
    necessary and sufficient overlap condition of 3.3.20,
    p. 307, in division-free form. Sorted
    endpoints prove sufficiency; a midpoint of either
    possible gap proves necessity. *)
Theorem binary_projected_interval_overlap (R:realType) (s u v:R):
  0<s ->s<1/2 ->0<u ->0<=v ->v<=u ->
  (binary_projected_interval_union s u v=(`[0,u+v]:set R) <->
    (1-2*s)*u<=v /\(1-2*s)*v<=s*u).
Proof.
move=>hs hsHalf hu hv hvu.
have hS1:s<1 by lra.
have hOrder:(1-s)*v<=(1-s)*u by nra.
have hEnd:s*(u+v)<=s*u+v by nra.
have hEnd2:s*u+v<=u+s*v by nra.
split.
- move=>hEqual;split.
  + case:(leP ((1-2*s)*u) v)=>[//|hNo].
    have hGap:s*u+v<(1-s)*u by nra.
    pose z:=((s*u+v)+(1-s)*u)/2.
    have hzLow:s*u+v<z by rewrite /z;lra.
    have hzHigh:z<(1-s)*u by rewrite /z;lra.
    have hz:0<=z<=u+v by rewrite /z;apply/andP;split;nra.
    have hZ:binary_projected_interval_union s u v z by rewrite hEqual.
    move:hZ;rewrite /binary_projected_interval_union /= !in_itv /=.
    move=>[[[/andP[_ h0]|/andP[_ h1]]|/andP[h2 _]]|/andP[h3 _]];
      nra.
  + case:(leP ((1-2*s)*v) (s*u))=>[//|hNo].
    have hGap:s*(u+v)<(1-s)*v by nra.
    pose z:=(s*(u+v)+(1-s)*v)/2.
    have hzLow:s*(u+v)<z by rewrite /z;lra.
    have hzHigh:z<(1-s)*v by rewrite /z;lra.
    have hz:0<=z<=u+v by rewrite /z;apply/andP;split;nra.
    have hZ:binary_projected_interval_union s u v z by rewrite hEqual.
    move:hZ;rewrite /binary_projected_interval_union /= !in_itv /=.
    move=>[[[/andP[_ h0]|/andP[h1 _]]|/andP[h2 _]]|/andP[h3 _]];
      nra.
- move=>[hMiddle hSide];apply/seteqP;split=>z.
  + rewrite /binary_projected_interval_union /= !in_itv /=.
    move=>[[[/andP[h0 h1]|/andP[h0 h1]]|/andP[h0 h1]]|/andP[h0 h1]];
      apply/andP;split;nra.
  + rewrite /= in_itv /=;move=>/andP[hz0 hz1].
    case:(leP z (s*(u+v)))=>h0.
    * left;left;left;rewrite /= in_itv /=;apply/andP;by split.
    * case:(leP z (s*u+v))=>h1.
      -- left;left;right;rewrite /= in_itv /=;apply/andP;split=>//;nra.
      -- case:(leP z (u+s*v))=>h2.
         ++ left;right;rewrite /= in_itv /=;apply/andP;split=>//;nra.
         ++ right;rewrite /= in_itv /=;apply/andP;split=>//;nra.
Qed.
