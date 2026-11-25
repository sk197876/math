(** Federer (1969), 3.3.21, p. 309: independent original arbitrary-schedule factor laws. *)
From mathcomp Require Import all_boot all_algebra classical_sets reals.
From Federer Require Import RealMetricBackground PowerCantorPairUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_scheduled_power_cantor_set]: the original
    factor A(m,n) from 2.10.28, p. 193, used in 3.3.21,
    p. 309. The arbitrary original schedule is explicit. Only
    the original pair laws are specified; compactness, masses,
    gaps and density are separately proved conclusions. *)
Definition is_scheduled_power_cantor_set (R:realType) (m:R) (n:nat->nat)
    (A:set (real_line_metric R)):Prop:=exists f,is_power_cantor_pair 1 m n A f.
