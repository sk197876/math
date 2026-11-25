(** Federer (1969), 3.3.19, p. 306: actual
    original balls in a thin parent annulus are
    contained in slightly enlarged circular caps. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric MetricClosedBalls
  CircularTrigonometrySealed CircularDiscCaps CircularBallCapScalar InnerRadialDifferenceSquare.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Cap.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation N:=(inner_norm (@euclidean_inner_productP R 2)).
Local Notation B:=(@euclidean_inner_product R 2).
Local Notation C:=(@CircularTrigonometry.cosine R).

(** Source for [positive_radius_normalized_ball_square]:
    division of the actual squared distance inequality by
    the positive parent radius squared, supporting the final
    density estimate of 3.3.19, p. 306. *)
Lemma positive_radius_normalized_ball_square (r d D t X:R):
  0<r ->D^+2+d^+2-t^+2<=2* d* X ->
  (D/r)^+2+(d/r)^+2-(t/r)^+2<=2*(d/r)*(X/r).
Proof.
move=>hr hDistance.
have hrN:r!=0 by rewrite gt_eqF.
have hSquare:0<r^+2 by rewrite exprn_gt0.
have hIdentity:r^+2*((D/r)^+2+(d/r)^+2-(t/r)^+2-2*(d/r)*(X/r))=
    D^+2+d^+2-t^+2-2* d* X by field.
have hScaled:r^+2*((D/r)^+2+(d/r)^+2-(t/r)^+2-2*(d/r)*(X/r))<=0.
  rewrite hIdentity;nra.
have hZero:r^+2*0= 0 by rewrite mulr0.
rewrite -hZero ler_pM2l // in hScaled;nra.
Qed.

(** Source for [circular_ball_cap_containment]: original
    radial coordinates with deficit at most 2r/n and
    a slightly enlarged normalized ball radius t/r+e
    give an actual cap containing the original ball test,
    whenever 24/n<e^2. All original closed boundaries
    remain. This supports the last assertion of
    3.3.19, p. 306. *)
Theorem circular_ball_cap_containment (z a x eta:E) (r d t e g:R) n:
  0<r ->(4<=n)%N ->N eta= 1 ->a= z+d*:eta ->
  r-2* r/n%:R<=d ->d<=r ->
  r-2* r/n%:R<=N (x-z) ->metric_closed_ball z r x ->
  0<=t ->t<=2* r ->metric_closed_ball a t x ->
  0<e ->24/n%:R<e^+2 ->C g= 1-(t/r+e)^+2/2 ->
  circular_disc_cap z r eta g x.
Proof.
move=>hr hn hEta hVertex hDeficit hdUpper hXDeficit hxParent ht htUpper hxBall he hSmall hAngle.
have hNP:0<(n%:R:R) by rewrite ltr0n;exact:(leq_trans (erefl true:(1<=4)%N) hn).
have hN4:(4<=n%:R:>R) by rewrite ler_nat.
have hInv:0<=(n%:R:R)^-1 by rewrite invr_ge0;exact:ltW hNP.
have hQuarter:1/(n%:R:R)<=1/4.
  rewrite ler_pdivrMr //;lra.
have hHalf:r/2<=d.
  have hProduct:= ler_wpM2l (ltW hr) hQuarter;nra.
have hd:0<=d by lra.
have hSquare:= @inner_radial_difference_square R (R_n R 2) B (@euclidean_inner_productP R 2)
  z a x eta d hEta hd hVertex.
have hTestSquare:(mdist x a)^+2<=t^+2.
  rewrite (ler_sqr (mdist_ge0 x a) ht) (metric_sym x a);exact:hxBall.
have hRaw:(N (x-z))^+2+d^+2-t^+2<=2* d* B (x-z) eta by nra.
have hNormalized:= positive_radius_normalized_ball_square hr hRaw.
have hNormD:1-2/n%:R<=d/r.
  rewrite ler_pdivlMr //;nra.
have hNormDUpper:d/r<=1 by rewrite ler_pdivrMr // mul1r.
have hNormX:1-2/n%:R<=N (x-z)/r.
  rewrite ler_pdivlMr //;nra.
have hT0:0<=t/r by apply:divr_ge0=>//;exact:ltW hr.
have hT2:t/r<=2 by rewrite ler_pdivrMr //.
rewrite div1r in hQuarter.
have hThreshold:= @circular_normalized_ball_cap_threshold R ((n%:R:R)^-1) (d/r) (N (x-z)/r) (t/r) (B (x-z) eta/r)
  hInv hQuarter hNormD hNormDUpper hNormX hT0 hT2 hNormalized.
have hCoordinate:C g<=B (x-z) eta/r.
  rewrite hAngle.
  have hProduct:= mulr_ge0 hT0 (ltW he).
  nra.
split=>//.
change (is_true (r* C g<=B (x-z) eta)).
have hScaled:(C g)* r<=B (x-z) eta by rewrite -ler_pdivlMr.
by rewrite mulrC.
Qed.
End Cap.
