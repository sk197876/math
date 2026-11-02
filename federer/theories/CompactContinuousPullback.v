(** General-topology support for Federer (1969), 2.6.6, pp. 120–121:
    continuous pullback into a compact space preserves K. Source context:
    CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot classical_sets reals topology.
From Federer Require Import RealMetricBackground CompactSupportFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [compact_continuous_pullback_membership]: supporting
    membership in the pullback lattices of Federer 2.6.6,
    pp. 120–121. Compactness is needed only for the domain. *)
Lemma compact_continuous_pullback_membership (R : realType) (X Y : topologicalType)
    (p : X -> Y) (f : Y -> R) : compact (@setT X) -> continuous p ->
  compactly_supported_continuous_functions f -> compactly_supported_continuous_functions (f \o p).
Proof.
move=> hc hp hf; split.
- move=> x; exact (@continuous_comp X Y (real_line_metric R) p f x (hp x) (hf.1 (p x))).
- exact: subclosed_compact (@real_function_support_closed R X _) hc (@subsetT _ _).
Qed.
