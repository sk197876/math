(** General-topology adapters for Federer (1969), 2.3.5, p. 77. Source
    context: PartialContinuityUP.v. These relate the abstract graph-based
    continuity to ordinary subspace continuity; no measurable-function
    theorem is imported. *)
From mathcomp Require Import all_boot classical_sets topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages PartialContinuityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [partial_continuity_empty]: empty-set boundary
    of the restriction conclusion in Federer 2.3.5, p. 77.
    Neither an inhabited target nor any defined value is required. *)
Lemma partial_continuity_empty (X Y : topologicalType) (f : partial_function X Y) :
  partial_function_continuous_on set0 f.
Proof.
constructor; first by move=> x [].
move=> U _; exists set0; split; first exact: open0.
by rewrite !set0I.
Qed.

(** Source for [partial_continuity_total_iff]: supporting equivalence
    of the relative-open specification with ordinary continuity of
    f|C in Federer 2.3.5, p. 77. The values of the total
    representative outside C play no role. *)
Lemma partial_continuity_total_iff (X Y : topologicalType) (C : set X) (g : X -> Y) :
  partial_function_continuous_on C (partial_function_total g) <->
  {within C, continuous g}.
Proof.
rewrite continuousP; split.
- move=> hf U hU; have [V [hV he]] := partial_continuity_open hf hU.
  rewrite partial_function_total_preimage in he.
  apply/open_subspaceP; exists V=> //.
  by rewrite setIC -he setIC.
- move=> hg; constructor.
  + by rewrite partial_function_total_domain; move=> x _.
  + move=> U hU; have [V hV he] := (proj1 (open_subspaceP C _)) (hg U hU).
    exists V; split=> //; rewrite partial_function_total_preimage.
    by rewrite setIC -he setIC.
Qed.
