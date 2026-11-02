(** Federer (1969), 3.1.4, p. 214: empty-target boundary of
    the scalar reduction, interpreted using the exact partial-domain
    definition of approximate limit in 2.9.12, p. 158. *)
From mathcomp Require Import all_boot boolp classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP MeasureSetDensity MeasureApproximateLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [constant_partial_approximate_limit_iff]: supporting
    boundary case of Federer 3.1.4, p. 214. A constant partial
    function has its constant as an approximate limit exactly when
    the missing domain has density zero. No totalization is used. *)
Theorem constant_partial_approximate_limit_iff (R : realType) (X : metricType R)
    (Y : topologicalType) (mu : set X -> \bar R) (V : X -> set X -> Prop)
    (f : partial_function X Y) a y :
  (forall x z, partial_function_graph f x z -> z=y) ->
  (is_measure_approximate_limit mu V f a y <->
    partial_function_graph (measure_set_density mu V (~` partial_function_domain f)) a 0%E).
Proof.
move=> hc; split; first exact: approximate_limit_domain_density.
move=> hd W hW.
have he : partial_function_preimage f W=partial_function_domain f.
  apply/seteqP; split=> x; first by move=> [z [hz _]]; exists z.
  move=> [z hz]; exists z; split=> //.
  rewrite (hc x z hz); exact: nbhs_singleton hW.
by rewrite he.
Qed.
