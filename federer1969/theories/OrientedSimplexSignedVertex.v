(** Federer (1969), 4.1.11, p. 366: the
    alternating prism coefficients can be included in
    the orientation of each simplex, without changing
    its set of vertices. Use the already proved
    original first-vertex transposition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals fingroup perm.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentSimplexFirstSwap
  OrientedSimplexCurrentSealed OrientedSimplexFirstSwap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [oriented_simplex_signed_vertices]: a signed
    positive-dimensional original simplex is an oriented
    simplex with the same original vertices, supporting
    the factorial rectangular sum in Federer 4.1.11,
    p. 366. *)
Lemma oriented_simplex_signed_vertices (R:realType) (h2:(1+1:R)!=0) n m
    (v:'I_(m.+2)->R_n R n) k:
  exists w:'I_(m.+2)->R_n R n,
    @OrientedSimplexCurrent.value R h2 n m.+1 w=
      (-1:R)^+k*:@OrientedSimplexCurrent.value R h2 n m.+1 v /\
    forall l,exists r,w l=v r.
Proof.
rewrite -signr_odd;case:(odd k).
- exists (current_simplex_first_swap v);split.
  + by rewrite oriented_simplex_current_first_swap expr1 scaleN1r.
  + move=>l;exists (tperm (ord0:'I_(m.+2)) (lift ord0 (ord0:'I_(m.+1))) l).
    by [].
- exists v;split;first by rewrite expr0 scale1r.
  move=>l;by exists l.
Qed.
