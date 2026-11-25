(** Federer (1969), 3.3.21, p. 309: actual original factor exists for every admitted schedule. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import RealMetricBackground PowerCantorPair ScheduledPowerCantorSetUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scheduled_power_cantor_set_exists]: existence
    of the actual original A(m,n) used in 3.3.21, p. 309,
    follows from the proved original pair existence, with the
    original schedule unchanged. No density or mass conclusion
    is an existence assumption. *)
Theorem scheduled_power_cantor_set_exists (R:realType) (m:R) (n:nat->nat):
  0<m ->m<1 ->(forall j,(2<=n j)%N) ->exists A,is_scheduled_power_cantor_set m n A.
Proof.
move=>hm hm1 hn.
have [A [f hPair]]:=@power_cantor_pair_exists R 1 m n ltr01 hm hm1 hn.
by exists A,f.
Qed.
