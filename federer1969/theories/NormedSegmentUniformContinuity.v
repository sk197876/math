(** Federer (1969), 3.1.11, pp. 220–221:
    uniform control of a continuous normed-vector function
    on a scalar segment. This is the compactness step
    in the normed-vector fundamental theorem used for Taylor. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals topology normedtype.
From Federer Require Import RealNormUP NormMetric RealMetricBackground
  NormClassOneUP CompactNearbyUniformContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_class_zero_real_segment_uniform]:
    continuity gives uniform control on the compact
    path interval used in the Taylor formula of
    Federer 3.1.11, pp. 220–221. The
    target need not be complete. *)
Theorem norm_class_zero_real_segment_uniform (R : realType) (Y : lmodType R)
    (NY : Y->R) (hNY : is_real_norm NY)
    (A : R->Prop) (f : R->Y) (a b : R) :
  (forall t, a<=t<=b -> A t) ->
  norm_class_zero (fun t : R^o=>`|t|) NY A f ->
  forall e : R, 0<e -> exists d, 0<d /\
    forall x y, a<=x<=b -> a<=y<=b -> `|x-y|<d -> NY (f x-f y)<e.
Proof.
move=> hAB hf e he.
pose K : set (real_line_metric R) := [set t | a<=t<=b].
have hK : compact K.
  have hset : K=`[a,b].
    by apply/seteqP; split=> t; rewrite /K /= in_itv /=.
  rewrite hset; exact: segment_compact.
have hKA : K `<=` A by move=> t ht; exact: hAB.
have hc c : K c -> forall u : R, 0<u ->
    exists r, 0<r /\ forall y, A y -> mdist c y<r ->
      mdist (f c : real_norm_metric_space hNY) (f y)<u.
  move=> hkc u hu; have [r [hr hb]] := (hf c (hKA c hkc)).2 u hu.
  exists r; split=> // y hy hs.
  have hshift : c+(y-c)=y by rewrite addrC subrK.
  have hAy : A (c+(y-c)) by rewrite hshift.
  have hsmall : `|y-c|<r by rewrite distrC; exact hs.
  have hh := hb (y-c) hAy hsmall; rewrite hshift in hh.
  change (is_true (NY (f c-f y)<u)).
  by rewrite (real_seminorm_subtract hNY.1).
have [d [hd hb]] := @metric_compact_uniform_nearby R (real_line_metric R)
  (real_norm_metric_space hNY) A K f hK hKA hc e he.
exists d; split=> // x y hx hy hs.
exact: hb x y hx (hAB y hy) hs.
Qed.
