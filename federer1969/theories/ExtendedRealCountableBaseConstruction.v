(** Federer (1969), 2.4.17, p. 90: countable order neighborhoods justify the
    sequential continuity argument. This private background construction
    enumerates rational-endpoint intervals, including unbounded intervals at
    infinity. Public arguments use only the countable-base laws through a
    seal. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import CountableOpenBaseUP CountableBaseNormalizationSealed
  CountableOrderIntervals OrderFamilyIntervalOpen ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [extended_real_countable_base_exists]: supporting existence
    of a countable open base for the extended exponent line in Federer
    2.4.17, p. 90 The resulting base is specified by its abstract laws. *)
Theorem extended_real_countable_base_exists (R : realType) :
  exists U : nat -> set (extended_real_line R), is_countable_open_base U.
Proof.
pose J := [the countType of ((option rat * option rat)%type : Type)].
pose d (q : rat) := (ratr q : R)%:E.
pose V n : set (extended_real_line R) := order_family_interval d (odflt (None,None) (@unpickle J n)).
have hVo n : open (V n) := @order_family_interval_open _ [the orderTopologicalType _ of order_topology (\bar R)] rat d _.
have hVr B : open B -> forall x, B x -> exists n, V n x /\ V n `<=` B.
  move=> hB x hx.
  have [c [hcx hcB]] := @order_family_intervals_refine _ [the orderTopologicalType _ of order_topology (\bar R)]
    rat d (@extended_rationals_order_dense R) B hB x hx.
  exists (pickle c); by rewrite /V pickleK /=.
exists (@CountableBaseNormalization.value (extended_real_line R) V hVo hVr).
exact: CountableBaseNormalization.laws.
Qed.
