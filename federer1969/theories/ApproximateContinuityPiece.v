(** Federer (1969), 2.9.13, p. 159: measurability and almost-everywhere
    approximate continuity. The erratum p. 3, book p. 159 line 19, corrects
    the order of the pair to (phi,V). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialContinuityUP MeasureDerivationContext
  MeasureSetDensity MeasureApproximateLimitUP LocalZeroDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [continuous_piece_approximate_continuity]: direct pointwise
    step in Federer 2.9.13, p. 159, first proof paragraph Continuity on a
    piece C at one of its density points implies approximate continuity. The
    piece need not be closed for this implication; the subsequent Lusin
    argument supplies closed pieces. *)
Lemma continuous_piece_approximate_continuity (R : realType) (X : metricType R)
    (Y : topologicalType) (phi : set X -> \bar R) (V : X -> set X -> Prop)
    (C : set X) (f : partial_function X Y) x :
  is_measure_derivation_context phi V -> partial_function_continuous_on C f -> C x ->
  partial_function_graph (measure_set_density phi V (~` C)) x 0 ->
  is_measure_approximately_continuous_at phi V f x.
Proof.
move=> hc hcont hxC hzero.
have [y hy] := @partial_continuity_domain X Y C f hcont x hxC.
exists y; split=> // W hW.
move: hW; rewrite nbhsE=> -[O [hO hyO] hOW].
have [U [hU he]] := partial_continuity_open hcont hO.
have hxpre : (C `&` partial_function_preimage f O) x.
  split=> //; exists y; by split.
have hxU : U x by rewrite he in hxpre; exact: hxpre.2.
apply: (@local_zero_density_mono R X phi V
  (~` partial_function_preimage f W) (~` C) U x hc hU hxU _ hzero).
move=> z hzU hn hzC; apply: hn.
have hzpre : (C `&` partial_function_preimage f O) z by rewrite he; split.
have [v [hv hvO]] := hzpre.2; exists v; split=> //; exact: hOW v hvO.
Qed.
