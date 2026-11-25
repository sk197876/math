(** Opaque compact-exhaustion witness supporting Federer (1969), 2.10.32,
    pp. 196–197. Expose only the sequence of nonempty compact sets and its
    independent exhaustion laws. The centre and closed-ball implementation
    remain private. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import InnerProductUP InnerMetric InnerConvex CompactSetDistanceProfile
  LipschitzFunctionCompact CompactConvexExhaustionUP CompactConvexExhaustionConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Module Type COMPACT_CONVEX_EXHAUSTION.
(** Source for [value]: supporting abstract compact
    sequence for the reduction of 2.10.32,
    pp. 196–197, with explicit hypotheses
    guaranteeing existence. *)
Parameter value : forall (R : realType) (V : lmodType R)
  (B : V -> V -> R) (hB : is_inner_product B),
  metric_boundedly_compact (inner_metric_space hB) ->
  forall C : set (inner_metric_space hB), C !=set0 -> closed C -> is_inner_convex C ->
  nat -> compact_metric_set (inner_metric_space hB).
(** Source for [laws]: supporting specification of the
    abstract sequence in 2.10.32, pp. 196–197.
    Its containment, convexity, increase and cover
    are supplied by a proved existence witness. *)
Parameter laws : forall (R : realType) (V : lmodType R)
  (B : V -> V -> R) (hB : is_inner_product B)
  (hX : metric_boundedly_compact (inner_metric_space hB))
  (C : set (inner_metric_space hB)) (hne : C !=set0) (hc : closed C) (hv : is_inner_convex C),
  is_compact_convex_exhaustion hB C (@value R V B hB hX C hne hc hv).
End COMPACT_CONVEX_EXHAUSTION.

Module CompactConvexExhaustion : COMPACT_CONVEX_EXHAUSTION.
(** Source for [value]: private existence witness for
    the compact reduction of 2.10.32,
    pp. 196–197, hidden by opaque ascription. *)
Definition value (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (hX : metric_boundedly_compact (inner_metric_space hB))
    (C : set (inner_metric_space hB)) (hne : C !=set0) (hc : closed C) (hv : is_inner_convex C) :=
  projT1 (cid (@compact_convex_exhaustion_exists R V B hB C hX hne hc hv)).
(** Source for [laws]: proved supporting exhaustion
    laws for 2.10.32, pp. 196–197.
    No project axiom is added by the interface. *)
Lemma laws (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (hX : metric_boundedly_compact (inner_metric_space hB))
    (C : set (inner_metric_space hB)) (hne : C !=set0) (hc : closed C) (hv : is_inner_convex C) :
  is_compact_convex_exhaustion hB C (@value R V B hB hX C hne hc hv).
Proof. exact: (projT2 (cid (@compact_convex_exhaustion_exists R V B hB C hX hne hc hv))). Qed.
End CompactConvexExhaustion.
