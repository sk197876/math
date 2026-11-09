(** Federer (1969), 3.3.19, p. 302: actual cyclic
    directions of the original child discs. Prove the exact
    minimum pair distance from scalar reflection and order;
    no separation or injectivity premise is supplied. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra ring.
From Federer Require Import EuclideanInnerProduct InnerMetric CircularTrigonometryUP
  CircularTrigonometrySealed RealTrigonometryUP CircularUnitVectors CircularChordLengths
  CircularCosineReflection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Directions.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation C:=(@CircularTrigonometry.cosine R).
Local Notation S:=(@CircularTrigonometry.sine R).
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation ht:=(@CircularTrigonometry.laws R).
Local Notation hb:=(circular_trig_basic ht).

(** Source for [circular_regular_direction]: the actual
    exp(2 pi i k/n) occurring in F_n(D), 3.3.19,
    p. 302, with the proved cyclic zero-based indexing. *)
Definition circular_regular_direction n (k:'I_n):E:=
  circular_unit_vector (2* p* k%:R/n%:R).

(** Source for [circular_regular_ordered_pair_distance]: every
    ordered pair of original distinct cyclic directions has
    distance at least 2 sin(pi/n), supporting the exact
    minimum centre distance in 3.3.19, p. 302. *)
Lemma circular_regular_ordered_pair_distance n (k l:'I_n):
  (2<=n)%N ->(k<l)%N ->
  2* S (p/n%:R)<=mdist (circular_regular_direction k) (circular_regular_direction l).
Proof.
move=>hn hkl.
have hp:=real_trigonometry_pi_positive hb.
have hnp:(0<n%:R:>R) by rewrite ltr0n;exact:leq_trans (erefl true : (1<=2)%N) hn.
have hnN:(n%:R:R)!= 0 by rewrite gt_eqF.
have hn2:(2<=n%:R:>R) by rewrite ler_nat.
pose a:R:= 2* p/n%:R.
have ha:0<a by rewrite /a divr_gt0 // mulr_gt0 // ltr0n.
have hAN:a* n%:R= 2* p by rewrite /a divfK.
have hap:a<=p by nra.
have hk:(0<=k%:R:>R) by rewrite ler0n.
have hkL:((val k).+1%:R<=l%:R:>R) by rewrite ler_nat.
have hSucc (j:nat):(j.+1%:R:R)=j%:R+1 by rewrite -addn1 natrD.
rewrite hSucc in hkL.
have hLn:(l%:R+1<=n%:R:>R).
  rewrite -hSucc ler_nat;exact:ltn_ord.
have hGap:(1<=l%:R-k%:R:>R) by lra.
have hGapN:(l%:R-k%:R+1<=n%:R:>R) by lra.
have hLower:a<=a*(l%:R-k%:R).
  have hh:=ler_wpM2l (ltW ha) hGap;by rewrite mulr1 in hh.
have hUpper:a*(l%:R-k%:R)<= 2* p-a.
  have hh:=ler_wpM2l (ltW ha) hGapN;rewrite mulrDr mulr1 hAN in hh;lra.
have hC:=@circular_cosine_between_symmetric_endpoints R a (a*(l%:R-k%:R))
  (ltW ha) hap hLower hUpper.
have hD:=@circular_unit_vector_distance_square R (a* k%:R) (a* l%:R).
have hAngles k0:2* p* k0%:R/n%:R=a* k0%:R by rewrite /a;ring.
have hDiff:a* k%:R-a* l%:R= -(a*(l%:R-k%:R)) by ring.
rewrite hDiff (circular_trig_cosine_even ht) in hD.
pose x:R:=p/n%:R.
have hx:0<x by rewrite /x divr_gt0.
have hxn:x* n%:R=p by rewrite /x divfK.
have hxp:x<=p by nra.
have hSin:=@circular_sine_nonnegative_semicircle R x (ltW hx) hxp.
have hTwice:a=x+x by rewrite /a /x;ring.
have hCos:C a= 1-2*(S x)^+2.
  rewrite hTwice (circular_trig_cosine_add ht).
  have hUnit:=circular_trig_unit ht x;nra.
have hDistance:=mdist_ge0 (circular_unit_vector (a* k%:R):E) (circular_unit_vector (a* l%:R)).
change (is_true (2* S x<=mdist (circular_unit_vector (2* p* k%:R/n%:R):E)
  (circular_unit_vector (2* p* l%:R/n%:R)))).
rewrite !hAngles;rewrite hCos in hC;nra.
Qed.

(** Source for [circular_regular_pair_distance]: minimum
    chord lower bound for EVERY original distinct pair,
    including cyclic wraparound, 3.3.19, p. 302. *)
Theorem circular_regular_pair_distance n (k l:'I_n):
  (2<=n)%N ->k!=l ->
  2* S (p/n%:R)<=mdist (circular_regular_direction k) (circular_regular_direction l).
Proof.
move=>hn hne;case:(ltngtP (val k) (val l))=>hkl.
- exact:(@circular_regular_ordered_pair_distance n k l hn hkl).
- rewrite metric_sym;exact:(@circular_regular_ordered_pair_distance n l k hn hkl).
- have hEq:k=l:=val_inj hkl;by move:hne;rewrite hEq eqxx.
Qed.
End Directions.
