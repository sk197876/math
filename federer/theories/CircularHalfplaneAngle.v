(** Federer (1969), 3.3.19, p. 302: a child
    meeting a closed halfplane has its original direction
    strictly in a slightly enlarged semicircle. The strict
    estimate retains boundary contacts of the closed discs. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets lra ring.
From Federer Require Import RealTrigonometryUP CircularTrigonometryUP CircularTrigonometrySealed
  CircularSineOrder CircularSineEndpointChord CircularCosineReflection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Angles.
Variable R:realType.
Local Notation C:=(@CircularTrigonometry.cosine R).
Local Notation S:=(@CircularTrigonometry.sine R).
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation ht:=(@CircularTrigonometry.laws R).
Local Notation hb:=(circular_trig_basic ht).

(** Source for [circular_halfplane_angle_interval]: the
    actual cosine lower bound for a disc meeting the
    original halfplane forces its angle into the open
    interval of half-width pi/2+pi/(2n), supporting
    the n/2+1 count in 3.3.19, p. 302.
    No orientation, parity or non-contact premise is added. *)
Lemma circular_halfplane_angle_interval n (d:R):
  (4<=n)%N -> -p<=d ->d<=p -> -(n%:R-1)^-1<=C d ->
  -(p/2+p/(2* n%:R))<d /\d<p/2+p/(2* n%:R).
Proof.
move=>hn hd0 hdp hCos.
have hp:=real_trigonometry_pi_positive hb.
have hN4:(4<=n%:R:>R) by rewrite ler_nat.
have hNP:(0<n%:R:>R) by lra.
have hInv:(0<n%:R^-1:>R) by rewrite invr_gt0.
have hCancel:(n%:R:R)* n%:R^-1= 1 by rewrite mulfV // gt_eqF.
have hQuarter:(4* n%:R^-1<= 1:>R).
  have hh:=ler_wpM2r (ltW hInv) hN4;by rewrite hCancel in hh.
pose a:R:=p/2+p/(2* n%:R).
have hRewrite:p/(2* n%:R)=(p/2)* n%:R^-1 by rewrite invfM;ring.
have ha0:0<=a by rewrite /a hRewrite;nra.
have hap:a<=p by rewrite /a hRewrite;nra.
have hCa:C a= -S (p/(2* n%:R)).
  by rewrite /a (circular_trig_cosine_add ht) (@circular_cosine_quarter_turn R)
    (real_sine_peak hb) mul0r mul1r sub0r.
have hStrong:=@circular_sine_half_step_strict R n hn.
have hNorm:0<=`|d| by exact:normr_ge0.
have hNormBound:`|d|<=p by rewrite ler_norml;apply/andP;split;lra.
have hCosNorm:C `|d|=C d.
  case:(leP 0 d)=>hd.
  - by rewrite ger0_norm.
  - by rewrite (ltr0_norm hd) (circular_trig_cosine_even ht).
have hStrict:`|d|<a.
  case:(ltP `|d| a)=>[h|h];first by [].
  have hWeak:=@circular_cosine_weak_decrease R a `|d| ha0 h hNormBound.
  rewrite hCosNorm hCa in hWeak;exfalso;lra.
move:hStrict;rewrite ltr_norml=>/andP[hLower hUpper].
by split.
Qed.
End Angles.
