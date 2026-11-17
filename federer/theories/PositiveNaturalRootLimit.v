(** Supporting Federer (1969), 3.2.45, p. 279:
    the positive finite probability floor disappears under
    roots of order tending to infinity. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import ExtendedRealOrderLimit RealPower RealPowerExponentLimit
  ReciprocalSequenceLimits RealScalarOrderLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [positive_natural_root_order_limit]: elementary
    endpoint limit supporting the corrected argument of
    Federer 3.2.45, p. 279. This reuses the exponent-zero
    limit of positive real powers and the reciprocal natural
    sequence, including probability floors greater than one. *)
Lemma positive_natural_root_order_limit (R : realType) (a : R) :
  0 < a -> extended_order_limit
    (fun j : nat => (real_power a ((j.+1)%:R)^-1)%:E) 1%E.
Proof.
move=> hA.
have h := @real_power_positive_base_exponent_limit R
  (fun j : nat => ((j.+1)%:R)^-1) 0 a hA (@reciprocal_natural_order_limit R).
by rewrite real_power_zero_exponent in h.
Qed.

(** Source for [positive_natural_root_scalar_order_limit]:
    scaled form of the same endpoint limit for the uniform
    lower approximation in Federer 3.2.45, p. 279.
    The scalar may have either sign and may vanish. *)
Lemma positive_natural_root_scalar_order_limit (R : realType) (a c : R) :
  0 < a -> extended_order_limit
    (fun j : nat => (c * real_power a ((j.+1)%:R)^-1)%:E) c%:E.
Proof.
move=> hA.
have h := @real_scalar_order_limit R
  (fun j : nat => real_power a ((j.+1)%:R)^-1) 1 c
  (@positive_natural_root_order_limit R a hA).
by rewrite mulr1 in h.
Qed.
