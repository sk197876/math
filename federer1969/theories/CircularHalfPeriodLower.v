(** Federer (1969), 3.3.19, p. 302: elementary
    positive margin behind the printed small-radius choice.
    The actual sine derivative and proved endpoint chords
    imply pi>=3, hence pi>2, without an external
    numerical or calculus theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets lra ring.
From Federer Require Import RealCurveDerivativeUP RealTrigonometryUP CircularTrigonometryUP CircularTrigonometrySealed
  CircularSineOrder CircularSineEndpointChord.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Period.
Variable R:realType.
Local Notation S:=(@CircularTrigonometry.sine R).
Local Notation C:=(@CircularTrigonometry.cosine R).
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation ht:=(@CircularTrigonometry.laws R).
Local Notation hb:=(circular_trig_basic ht).

(** Source for [circular_sine_sixth_chord_slope]: the
    exact endpoint chord slope 3/pi, supporting
    the original small-angle bounds in 3.3.19,
    p. 302. It is derived from sin(pi/6)=1/2. *)
Lemma circular_sine_sixth_chord_slope:S (p/6)/(p/6)= 3/p.
Proof.
rewrite (@circular_sine_twelfth_turn R) invf_div;nra.
Qed.

(** Source for [circular_half_period_at_least_three]:
    elementary lower estimate for the actual scalar
    half-period supporting the positive margins in
    3.3.19, p. 302. No numerical value or
    new normalization hypothesis is supplied. *)
Theorem circular_half_period_at_least_three:3<=p.
Proof.
have hp:=real_trigonometry_pi_positive hb.
have hpN:p!= 0 by rewrite gt_eqF.
case:(leP 3 p)=>[h|hSmall];first by [].
have hPInv:0<p^-1 by rewrite invr_gt0.
have hPCancel:p* p^-1= 1 by rewrite mulfV.
have hSlope:1<3/p by nra.
pose e:R:=(3/p-1)/2.
have he:0<e by rewrite /e;lra.
have hDerivative:=real_sine_derivative hb 0.
rewrite /has_real_curve_derivative (real_cosine_zero hb) in hDerivative.
have [d [hd hD]]:=hDerivative e he.
pose M:R:=Num.min d (p/6).
have hSixth:0<p/6 by rewrite divr_gt0 // ltr0n.
have hM:0<M by rewrite /M lt_min hd hSixth.
pose x:R:=M/2.
have hx:0<x by rewrite /x divr_gt0 // ltr0n.
have hMD:M<=d by rewrite /M ge_min lexx.
have hMS:M<=p/6 by rewrite /M ge_min lexx orbT.
have hxd:x<d by rewrite /x;lra.
have hxs:x<p/6 by rewrite /x;lra.
have hxp:p/6<=p/2 by lra.
have hChord:=@circular_sine_endpoint_chord R (p/6) x hSixth hxp hx hxs.
rewrite circular_sine_sixth_chord_slope in hChord.
have hNorm:`|x|=x:=ger0_norm (ltW hx).
have hInput:0<`|x|<d by rewrite hNorm hx hxd.
have hApprox:=hD x hInput.
rewrite add0r (real_sine_zero hb) subr0 ltr_norml in hApprox.
have /andP[_ hUpper]:=hApprox.
have hXN:x!= 0 by rewrite gt_eqF.
have hRatio:(S x/x)* x=S x by rewrite divfK.
have hStrict:((S x/x)<3/p) by rewrite /e in hUpper;lra.
have hMult:=ler_wpM2r (ltW hx) (ltW hStrict).
rewrite hRatio in hMult.
have hFalse:=lt_le_trans hChord hMult;by rewrite ltxx in hFalse.
Qed.
End Period.
