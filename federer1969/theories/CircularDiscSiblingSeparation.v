(** Federer (1969), 3.3.19, p. 302: distinct
    actual circular sibling discs are separated by more
    than their common child radius. Prove the geometry
    from the original formula, never assume it as a tree law. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra ring.
From Federer Require Import EuclideanInnerProduct InnerNorm InnerMetric MetricClosedBalls
  CircularTrigonometryUP CircularTrigonometrySealed RealTrigonometryUP
  CircularUnitVectors CircularRegularDirections CircularSineChordBound CircularDiscRefinement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Siblings.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation S:=(@CircularTrigonometry.sine R).
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation ht:=(@CircularTrigonometry.laws R).
Local Notation hb:=(circular_trig_basic ht).

(** Source for [circular_disc_sibling_separation]: literal
    strict separation by more than the child radius used
    for the original G_n in 3.3.19, p. 302, first for
    two children of a common original parent. Arbitrary
    original points in their closed discs are retained. *)
Theorem circular_disc_sibling_separation (z:E) (r:R) n (k l:'I_n) (x y:E):
  0<r ->(4<=n)%N ->k!=l ->
  metric_closed_ball (circular_disc_child_center z r k) (r/n%:R) x ->
  metric_closed_ball (circular_disc_child_center z r l) (r/n%:R) y ->
  r/n%:R<mdist x y.
Proof.
move=>hr hn hne hx hy.
have hp:=real_trigonometry_pi_positive hb.
have hpN:p!= 0 by rewrite gt_eqF.
have hnp:(0<n%:R:>R) by rewrite ltr0n;exact:leq_trans (erefl true : (1<= 4)%N) hn.
have hnN:(n%:R:R)!= 0 by rewrite gt_eqF.
have hn4:(4<=n%:R:>R) by rewrite ler_nat.
pose q:R:=n%:R^-1.
pose t:R:=r/n%:R.
pose c:R:=(1-q)* r.
have hq:0<q by rewrite /q invr_gt0.
have hNq:n%:R* q= 1 by rewrite /q mulfV.
have hq4:4* q<= 1 by have hScaled:=ler_wpM2r (ltW hq) hn4;rewrite hNq in hScaled.
have htP:0<t by rewrite /t divr_gt0.
have hOneMinus:0<1-q by lra.
have hcP:0<c.
  rewrite /c;exact:(mulr_gt0 hOneMinus hr).
have hAngleP:(0<p/n%:R) by rewrite divr_gt0.
have hAngleHalf:p/n%:R<p/2.
  have hN2:(2<n%:R:>R) by nra.
  have hInv:q<1/2 by nra.
  change (is_true (p* q<p/2));nra.
have hSine:=@circular_sine_strict_chord R (p/n%:R) hAngleP hAngleHalf.
have hCancel:(p/n%:R)/p=q by rewrite /q mulrAC divff // mul1r.
have hSinCancel:2*(p/n%:R)/p= 2* q by rewrite -mulrA hCancel.
rewrite hSinCancel in hSine.
have hn2:(2<=n)%N:=leq_trans (erefl true : (2<= 4)%N) hn.
have hPair:=@circular_regular_pair_distance R n k l hn2 hne.
have hCentres:
    mdist (circular_disc_child_center z r k) (circular_disc_child_center z r l)=
    c* mdist (@circular_regular_direction R n k) (@circular_regular_direction R n l).
  rewrite !inner_metric_distanceE /circular_disc_child_center /circular_regular_direction -/q -/c.
  have hDifference:
      (z+c*:circular_unit_vector (2* p* k%:R/n%:R))-
      (z+c*:circular_unit_vector (2* p* l%:R/n%:R))=
      c*:(circular_unit_vector (2* p* k%:R/n%:R)-circular_unit_vector (2* p* l%:R/n%:R)).
    by rewrite opprD addrACA subrr add0r -scalerBr.
  by rewrite hDifference inner_normZ (ger0_norm (ltW hcP)).
have hPairScaled:=ler_wpM2l (ltW hcP) hPair.
have hStrict:3* t<mdist (circular_disc_child_center z r k) (circular_disc_child_center z r l).
  have hStrong:4* c* q<2* c* S (p/n%:R) by nra.
  have hBudget:c* q=(1-q)* t by rewrite /c /t /q;ring.
  have hLeft:4* c* q=4*((1-q)* t) by rewrite -mulrA hBudget.
  rewrite -hCentres in hPairScaled;rewrite hLeft in hStrong;nra.
have hTriangle:=metric_triangle (circular_disc_child_center z r k) x
  (circular_disc_child_center z r l).
have hTriangle2:=metric_triangle x y (circular_disc_child_center z r l).
have hy':mdist y (circular_disc_child_center z r l)<=t by rewrite metric_sym;exact hy.
change (is_true (mdist (circular_disc_child_center z r k) x<=t)) in hx.
change (is_true (t<mdist x y));nra.
Qed.
End Siblings.
