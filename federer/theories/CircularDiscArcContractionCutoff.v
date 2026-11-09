(** Federer (1969), 3.3.19, p. 305: the actual
    complementary arc fraction plus 2/n is eventually bounded
    by one fixed positive number strictly smaller than one. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp lra.
From Federer Require Import RealTrigonometryUP CircularTrigonometryUP CircularTrigonometrySealed
  NaturalScaledReciprocalTail.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [circular_disc_arc_contraction_cutoff]: every
    positive-length original arc has a uniform late contraction
    factor for the actual printed a+2/n recurrence in
    3.3.19, p. 305. This uses only the actual
    positive circle half-period and the natural reciprocal tail. *)
Theorem circular_disc_arc_contraction_cutoff (R:realType) (a b:R):
  0<=a ->a<b ->b<=2*(@CircularTrigonometry.half_period R) ->
  exists q:R,exists N:nat,0<q<1 /\forall j,(N<=j)%N ->
    1-(b-a)/(2*(@CircularTrigonometry.half_period R))+2/(j+4)%:R<=q.
Proof.
move=>ha hab hb.
pose p:= @CircularTrigonometry.half_period R.
change (is_true (b<=2* p)) in hb.
have hp:0<p:= real_trigonometry_pi_positive (circular_trig_basic (@CircularTrigonometry.laws R)).
have hTwo:0<2* p by nra.
pose c:R:=(b-a)/(2* p).
have hc:0<c by rewrite /c divr_gt0 // subr_gt0.
have hc1:c<=1 by rewrite /c ler_pdivrMr // mul1r;lra.
pose q:R:= 1-c/2.
have hq:0<q<1 by apply/andP;split;rewrite /q;nra.
have hHalf:0<c/2 by lra.
have hTwoPositive:(0<(2:R)) by rewrite ltr0n.
have [N hN]:= @natural_scaled_reciprocal_tail R 2 (c/2) hTwoPositive hHalf.
exists q,N;split=>//;move=>j hj.
have hIndex:(N<=j+4)%N:= leq_trans hj (leq_addr 4 j).
have [_ hSmall]:= hN (j+4)%N hIndex.
change (is_true (1-c+2/(j+4)%:R<=q)).
rewrite /q;lra.
Qed.
