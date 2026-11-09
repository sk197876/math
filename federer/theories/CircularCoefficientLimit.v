(** Federer (1969), 3.3.19, p. 302: the
    original coefficient (n-1)sin(pi/n) tends to pi.
    Prove the full all-integer epsilon estimate from
    the actual derivative and Archimedean reciprocal tails. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets lra.
From Federer Require Import RealTrigonometryUP CircularTrigonometryUP CircularTrigonometrySealed
  CircularSineScaledError NaturalScaledReciprocalTail.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Limit.
Variable R:realType.
Local Notation S:=(@CircularTrigonometry.sine R).
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation ht:=(@CircularTrigonometry.laws R).
Local Notation hb:=(circular_trig_basic ht).

(** Source for [circular_coefficient_limit]: exact scalar
    convergence used to choose the original delta in
    3.3.19, p. 302. Every sufficiently large
    integer is covered, without a subsequence or an
    assumed asymptotic sine formula. *)
Theorem circular_coefficient_limit (e:R):0<e ->exists N:nat,
  forall n,(N<=n)%N ->(0<n)%N /\`|(n%:R-1)* S (p/n%:R)-p|<e.
Proof.
move=>he;have hp:=real_trigonometry_pi_positive hb.
have [d [hd hError]]:=@circular_sine_scaled_error R e he.
have [N hTail]:=@natural_scaled_reciprocal_tail R p d hp hd.
exists N=>n hn;have [hnP hxD]:=hTail n hn.
have hNP:(0<n%:R:>R) by rewrite ltr0n.
have hNN:(n%:R:R)!= 0 by rewrite gt_eqF.
have hn1:(1<=n%:R:>R) by rewrite ler1n.
have hx:0<p/n%:R by rewrite divr_gt0.
have hBudget:n%:R*(p/n%:R)=p by rewrite mulrC (divfK hNN).
split=>//;exact:(hError n%:R (p/n%:R) hn1 hx hxD hBudget).
Qed.
End Limit.
