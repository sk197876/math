(** Public compact-exhaustion interface supporting Federer (1969), 2.10.32,
    pp. 196–197. The sequence is accessed only through its proved abstract
    laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import InnerProductUP InnerMetric InnerConvex CompactSetDistanceProfile
  LipschitzFunctionCompact CompactConvexExhaustionUP CompactConvexExhaustionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [compact_convex_exhaustion]: supporting
    abstract sequence for the compact reduction
    of 2.10.32, pp. 196–197. Existence
    follows from the supplied bounded compactness
    and closed convex target hypotheses. *)
Definition compact_convex_exhaustion (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (hX : metric_boundedly_compact (inner_metric_space hB))
    (C : set (inner_metric_space hB)) (hne : C !=set0) (hc : closed C) (hv : is_inner_convex C) :=
  @CompactConvexExhaustion.value R V B hB hX C hne hc hv.
Arguments compact_convex_exhaustion {R V B} hB hX {C} hne hc hv.

(** Source for [compact_convex_exhaustion_specification]: supporting
    exposed laws of the sequence in the
    reduction of 2.10.32, pp. 196–197.
    Downstream measure arguments use only these laws. *)
Lemma compact_convex_exhaustion_specification (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (hX : metric_boundedly_compact (inner_metric_space hB))
    (C : set (inner_metric_space hB)) (hne : C !=set0) (hc : closed C) (hv : is_inner_convex C) :
  is_compact_convex_exhaustion hB C (compact_convex_exhaustion hB hX hne hc hv).
Proof. exact: CompactConvexExhaustion.laws. Qed.
Arguments compact_convex_exhaustion_specification {R V B} hB hX {C} hne hc hv.
