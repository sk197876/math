(** Federer (1969), 3.3.21, p. 309: opaque original arbitrary-schedule factor. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets reals.
From Federer Require Import RealMetricBackground ScheduledPowerCantorSetUP ScheduledPowerCantorSetExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type ScheduledPowerCantorSignature.
(** Source for [value]: the actual original arbitrary-schedule
    A(m,n) of 3.3.21, p. 309, behind independent original laws. *)
Parameter value:forall (R:realType) (m:R),0<m ->m<1 ->
  forall n:nat->nat,(forall j,(2<=n j)%N) ->set (real_line_metric R).
(** Source for [laws]: independent original factor laws of
    3.3.21, p. 309. Geometric conclusions are derived downstream. *)
Parameter laws:forall R m hm hm1 n hn,
  is_scheduled_power_cantor_set m n (@value R m hm hm1 n hn).
End ScheduledPowerCantorSignature.
Module ScheduledPowerCantor:ScheduledPowerCantorSignature.
(** Source for [value]: the private existence witness for
    original A(m,n), 3.3.21, p. 309. Its implementation is sealed. *)
Definition value (R:realType) (m:R) (hm:0<m) (hm1:m<1) n (hn:forall j,(2<=n j)%N):=
  projT1 (cid (@scheduled_power_cantor_set_exists R m n hm hm1 hn)).
(** Source for [laws]: the private witness satisfies the
    independently stated original laws, 3.3.21, p. 309. *)
Lemma laws R m hm hm1 n hn:is_scheduled_power_cantor_set m n (@value R m hm hm1 n hn).
Proof. exact:(projT2 (cid (@scheduled_power_cantor_set_exists R m n hm hm1 hn))). Qed.
End ScheduledPowerCantor.
