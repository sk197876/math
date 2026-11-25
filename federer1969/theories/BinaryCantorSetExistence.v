(** Federer (1969), 3.3.20, p. 306:
    existence of the independently specified original factor. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import RealMetricBackground PowerCantorPairUP PowerCantorPair BinaryCantorSetUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [binary_power_cantor_set_exists]: the
    actual application of 2.10.28 in 3.3.20,
    p. 306, with n_j=2. It works for
    every 0<m<1; no mass, projection or
    geometric conclusion is assumed as existence data. *)
Theorem binary_power_cantor_set_exists (R:realType) (m:R):
  0<m ->m<1 ->exists A,is_binary_power_cantor_set m A.
Proof.
move=>hm hm1.
have [A [f hPair]]:=@power_cantor_pair_exists R 1 m (fun _:nat=>2%N)
  ltr01 hm hm1 (fun _=>leqnn 2).
exists A,f;exact:hPair.
Qed.
