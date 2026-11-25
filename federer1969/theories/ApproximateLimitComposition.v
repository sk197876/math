(** Federer (1969), 3.1.3(2),(4), p. 213: continuous changes of
    values preserve approximate limits. This supporting step permits
    viewing a real-valued function in the extended real line. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionPostcomposition
  MeasureApproximateLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [approximate_limit_continuous_postcompose]: supporting
    topological consequence of the definition in Federer 2.9.12, p. 158,
    used for the real-valued limit in 3.1.3(4), p. 213. Composition
    preserves the actual domain of the partial function. *)
Lemma approximate_limit_continuous_postcompose (R : realType) (X : metricType R)
    (Y Z : topologicalType) (phi : set X -> \bar R) (V : X -> set X -> Prop)
    (f : partial_function X Y) (g : Y -> Z) x y :
  {for y, continuous g} -> is_measure_approximate_limit phi V f x y ->
  is_measure_approximate_limit phi V (partial_function_postcompose f g) x (g y).
Proof.
move=> hg hf W hW; rewrite partial_function_postcompose_preimage.
apply: hf; exact: hg _ hW.
Qed.
