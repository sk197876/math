(** Federer (1969), 3.3.2, p. 288: conclude Borel
    measurability from the published corrected two-index formula. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import TopologicalBorel BorelFunctionUP
  ExtendedRealOrderTopology StructureLimsupLevels StructureBorelOrderCriterion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_tail_upper_limit_borel]: the
    Borel conclusion of the corrected proof in Federer
    3.3.2, p. 288; erratum pp. 5–6, book p. 288
    lines 1–6. Both the threshold-margin union and
    the aperture-cutoff intersection remain explicit. *)
Theorem structure_tail_upper_limit_borel (R:realType)
    (P:topologicalType) (f:P->R->R->\bar R) (delta:R):
  (forall r s,0<r ->0<s ->forall b:R,
    open [set x|(b%:E<f x r s)%E]) ->
  is_borel_function (fun x:P=>
    (structure_tail_upper_limit f delta x:extended_real_line R)).
Proof.
move=>hOpen; apply:structure_borel_from_strict_superlevels=>b.
rewrite structure_corrected_strict_superlevel.
apply:borel_set_countable_union (countableP setT) _=>j _.
apply:borel_set_countable_intersection (countableP setT) _ _.
- by exists 0%N.
- move=>i _; apply:open_borel_set.
  exact:(structure_tail_supremum_superlevel_open delta
    (b+((j.+1)%:R:R)^-1) i hOpen).
Qed.
