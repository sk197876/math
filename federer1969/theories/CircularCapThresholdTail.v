(** Federer (1969), 3.3.19, p. 305: every fixed
    positive small cap eventually contains the original
    threshold cap with cosine 1-2/n. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import RealTrigonometryUP CircularTrigonometryUP CircularTrigonometrySealed
  CircularCosineReflection NaturalScaledReciprocalTail.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [circular_cap_threshold_angle_tail]: for each
    fixed 0<beta<=pi, cos(beta)<1-2/n at every
    sufficiently late original n. Strict cosine order and
    the actual reciprocal cutoff prove the small-beta step
    in 3.3.19, p. 305 without a supplied limit law. *)
Theorem circular_cap_threshold_angle_tail (R:realType) (b:R):
  0<b ->b<=@CircularTrigonometry.half_period R ->exists J:nat,
  forall j,(J<=j)%N ->@CircularTrigonometry.cosine R b<1-2/(j+4)%:R.
Proof.
move=>hb hbp.
pose ht:= @CircularTrigonometry.laws R.
have hPi:= real_trigonometry_pi_positive (circular_trig_basic ht).
have hZero:0<=(0:R):= lexx 0.
have hPi0:(0:R)<=@CircularTrigonometry.half_period R:= ltW hPi.
have hB0:0<=b:= ltW hb.
have hStrict:= @circular_trig_cosine_decreases R (@CircularTrigonometry.sine R)
  (@CircularTrigonometry.cosine R) (@CircularTrigonometry.arcsine R)
  (@CircularTrigonometry.arccosine R) (@CircularTrigonometry.half_period R)
  ht 0 b hZero hPi0 hB0 hbp hb.
rewrite (real_cosine_zero (circular_trig_basic ht)) in hStrict.
have hGap:0<1-@CircularTrigonometry.cosine R b by lra.
have hTwo:0<(2:R) by rewrite ltr0n.
have [J hJ]:= @natural_scaled_reciprocal_tail R 2 (1-@CircularTrigonometry.cosine R b) hTwo hGap.
exists J=>j hj.
have hJN:(J<=j+4)%N:= leq_trans hj (leq_addr 4 j).
have [_ hSmall]:= hJ _ hJN;lra.
Qed.
