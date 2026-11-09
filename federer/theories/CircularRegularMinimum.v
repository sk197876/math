(** Federer (1969), 3.3.19, p. 302: exact
    minimum cyclic chord and injectivity for the actual
    regular circular directions of the original disc children. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra ring.
From Federer Require Import EuclideanInnerProduct InnerMetric CircularTrigonometryUP
  CircularTrigonometrySealed RealTrigonometryUP CircularUnitVectors CircularChordLengths
  CircularRegularDirections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Minimum.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation S:=(@CircularTrigonometry.sine R).
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation ht:=(@CircularTrigonometry.laws R).
Local Notation hb:=(circular_trig_basic ht).

(** Source for [circular_regular_half_angle_bounds]: positive
    principal half-angle of the original circular children,
    supporting 3.3.19, p. 302. *)
Lemma circular_regular_half_angle_bounds n:(2<=n)%N ->
  0<p/n%:R /\p/n%:R<p.
Proof.
move=>hn;have hp:=real_trigonometry_pi_positive hb.
have hN:(0<n%:R:>R) by rewrite ltr0n;exact:leq_trans (erefl true : (1<= 2)%N) hn.
have hN2:(2<=n%:R:>R) by rewrite ler_nat.
have hNp:(n%:R:R)!= 0 by rewrite gt_eqF.
have hPositive:0<p/n%:R by rewrite divr_gt0.
have hCancel:(p/n%:R)* n%:R=p by rewrite divfK.
split=>//;nra.
Qed.

(** Source for [circular_regular_direction_injective]:
    the original n cyclic child indices give distinct
    directions, supporting exact counts in 3.3.19, p. 302. *)
Lemma circular_regular_direction_injective n:(2<=n)%N ->
  injective (@circular_regular_direction R n).
Proof.
move=>hn k l hEqual;case:(eqVneq k l)=>[h|hne];first exact h.
have [hx hxp]:=@circular_regular_half_angle_bounds n hn.
have hS:=@circular_trig_sine_positive R (@CircularTrigonometry.sine R)
  (@CircularTrigonometry.cosine R) (@CircularTrigonometry.arcsine R)
  (@CircularTrigonometry.arccosine R) p ht (p/n%:R) hx hxp.
have hPair:=@circular_regular_pair_distance R n k l hn hne.
rewrite hEqual mdistxx in hPair.
have hTwo:(0<(2:R)) by rewrite ltr0n.
have hStrict:=mulr_gt0 hTwo hS.
have hFalse:=lt_le_trans hStrict hPair;by rewrite ltxx in hFalse.
Qed.

(** Source for [circular_regular_minimum_attained]: adjacent
    original cyclic indices attain 2 sin(pi/n), completing
    the unit-circle minimum-distance assertion underlying
    the displayed centre distance in 3.3.19, p. 302. *)
Lemma circular_regular_minimum_attained n:(2<=n)%N ->
  exists k l:'I_n,k!=l /\
    mdist (@circular_regular_direction R n k) (@circular_regular_direction R n l)= 2* S (p/n%:R).
Proof.
move=>hn.
have hnP:(0<n)%N:=leq_trans (erefl true : (1<= 2)%N) hn.
pose k0:'I_n:=@Ordinal n 0 hnP.
pose k1:'I_n:=@Ordinal n 1 hn.
exists k0,k1;split.
- apply/eqP=>hEq;have hFalse:(0= 1)%N:=congr1 val hEq;discriminate hFalse.
- have [hx hxp]:=@circular_regular_half_angle_bounds n hn.
  rewrite /circular_regular_direction /k0 /k1 /= mulr0 mul0r mulr1 metric_sym.
  have hAngle:2* p/n%:R= 0+2*(p/n%:R) by ring.
  rewrite hAngle;exact:(@circular_unit_chord_length R 0 (p/n%:R) (ltW hx) (ltW hxp)).
Qed.
End Minimum.
