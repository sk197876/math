(** Federer (1969), 3.2.7, p. 246: supporting
    values at successive zeroes and positive peaks.
    Derive these from the opaque full-period laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import RealTrigonometryUP RealTrigonometrySealed RealTrigonometryBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_sine_natural_period_shift]: periodic
    value law supporting the third example of
    Federer 3.2.7, p. 246. Natural translates
    follow by induction from the proved full period. *)
Lemma real_sine_natural_period_shift (R:realType) (x:R) (n:nat):
  RealTrigonometry.sine (x+2*n%:R*(@RealTrigonometry.half_period R))=RealTrigonometry.sine x.
Proof.
elim:n=>[|n ih]; first by rewrite mulr0 mul0r addr0.
have he:x+2*n.+1%:R*(@RealTrigonometry.half_period R)=
  (x+2*n%:R*(@RealTrigonometry.half_period R))+
    ((@RealTrigonometry.half_period R)+(@RealTrigonometry.half_period R)).
  rewrite -[n.+1]addn1 natrD; by ring.
by rewrite he real_sine_period ih.
Qed.

(** Source for [real_sine_cycle_zero]: zero level
    at an even half-period, supporting the finite
    crossing count in Federer 3.2.7, p. 246. *)
Lemma real_sine_cycle_zero (R:realType) (n:nat):
  RealTrigonometry.sine (2*n%:R*(@RealTrigonometry.half_period R))= 0.
Proof.
have hh:=@real_sine_natural_period_shift R 0 n.
by rewrite add0r (real_sine_zero (@RealTrigonometry.laws R)) in hh.
Qed.

(** Source for [real_sine_cycle_peak]: unit value
    at a positive peak, supporting the image
    lower bounds in Federer 3.2.7, p. 246. *)
Lemma real_sine_cycle_peak (R:realType) (n:nat):
  RealTrigonometry.sine (2*n%:R*(@RealTrigonometry.half_period R)+(@RealTrigonometry.half_period R)/2)= 1.
Proof.
rewrite addrC real_sine_natural_period_shift.
exact (real_sine_peak (@RealTrigonometry.laws R)).
Qed.
