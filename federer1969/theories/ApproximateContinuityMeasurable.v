(** Federer (1969), 2.9.13, p. 159: measurability and almost-everywhere
    approximate continuity. The erratum p. 3, book p. 159 line 19, corrects
    the order of the pair to (phi,V). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP MeasureUP MeasureBasic MeasureAlmostUP
  MeasureAlmostBasic MeasureDerivationContext MeasureDensityPoints DensityMeasurableSets
  MeasureApproximateLimitUP MeasurableFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [almost_approximate_continuity_measurable]: direct converse
    of Federer 2.9.13, p. 159, last proof paragraph On each open inverse
    image A, approximate continuity gives the Q density condition. The
    second measurability equivalence of 2.9.11 then proves A measurable.
    This direction needs no separability or metric structure on the target. *)
Theorem almost_approximate_continuity_measurable (R : realType) (X : metricType R)
    (Y : topologicalType) (phi : set X -> \bar R) (V : X -> set X -> Prop)
    (f : partial_function X Y) :
  is_measure_derivation_context phi V ->
  measure_almost_everywhere phi [set x | is_measure_approximately_continuous_at phi V f x] ->
  is_measure_measurable_function phi f.
Proof.
move=> hc ha; have hm := derivation_measure_law (derivation_context_measure hc).
constructor.
- apply: (@measure_almost_everywhere_mono R X phi hm _ _ _ ha)=> x [y [hy _]].
  by exists y.
- move=> W hW; pose A := partial_function_preimage f W.
  have hnull : phi (A `\` measure_density_complement_zero_points phi V A)=0.
    apply: (@measure_null_subset R X phi hm _
      (~` [set x | is_measure_approximately_continuous_at phi V f x])) ha.
    move=> x [hxA hnQ] [y [hy hl]]; apply: hnQ.
    have [z [hz hzW]] := hxA.
    have he := partial_function_single_valued hy hz.
    have hyW : W y by rewrite he.
    have hN : nbhs y W by rewrite openE in hW; exact: hW y hyW.
    exact: hl W hN.
  exact: (density_complement_zero_points_conclusions A hc).2.2.2.2 hnull.
Qed.
