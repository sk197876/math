(** Federer (1969), 2.5.14, p. 107, first paragraph: the level families for
    K(X) supply open outer and compact inner approximations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealMetricBackground CompactSupportFunctionUP FunctionLatticeUP
  FunctionLatticeLevelFamilies CountableOrderIntervals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_support_strict_level_open]: the F0 sets are open in
    Federer 2.5.14, p. 107 *)
Lemma compact_support_strict_level_open (R : realType) (X : topologicalType) S :
  function_lattice_strict_levels (@compactly_supported_continuous_functions R X) S -> open S.
Proof.
move=> [f [t [[[hf _] _] [_ ->]]]].
exact ((@continuousP X (real_line_metric R) f).1 hf _ (@order_strict_upper_ray_open _ [the orderTopologicalType _ of R^o] t)).
Qed.

(** Source for [compact_support_increasing_level_open]: the F1 sets are
    open, used in both approximation formulas in Federer 2.5.14, p. 107 *)
Lemma compact_support_increasing_level_open (R : realType) (X : topologicalType) S :
  function_lattice_increasing_levels (@compactly_supported_continuous_functions R X) S -> open S.
Proof.
move=> [V [hV [_ ->]]]; apply: bigcup_open=> n _.
exact: compact_support_strict_level_open (hV n).
Qed.

(** Source for [compact_support_positive_closed_level_compact]: compactness
    of positive closed levels of h in K(X), supporting Federer 2.5.14, p.
    107 The threshold must be positive. *)
Lemma compact_support_positive_closed_level_compact (R : realType) (X : topologicalType)
    (f : X -> R) (t : R) :
  compactly_supported_continuous_functions f -> 0 < t -> compact [set x | t <= f x].
Proof.
move=> [hf hs] ht.
have hc : closed [set x | t <= f x].
  exact ((@continuous_closedP X (real_line_metric R) f).1 hf _ (@order_closed_upper_ray_closed _ [the orderTopologicalType _ of R^o] t)).
apply: (@subclosed_compact X _ (real_function_support f) hc hs)=> x hx.
apply: subset_closure=> hz; change (is_true (t <= f x)) in hx.
by move: hx; rewrite hz leNgt ht.
Qed.

(** Source for [compact_support_inner_difference_compact]: the compact
    approximants {h >= 1} minus E in Federer 2.5.14, p. 107 *)
Lemma compact_support_inner_difference_compact (R : realType) (X : topologicalType)
    (h : X -> R) (E : set X) :
  compactly_supported_continuous_functions h ->
  function_lattice_increasing_levels (@compactly_supported_continuous_functions R X) E ->
  compact ([set x | 1 <= h x] `\` E).
Proof.
move=> hh hE.
have hc := @compact_support_positive_closed_level_compact R X h 1 hh (@ltr01 R).
apply: (@subclosed_compact X _ [set x | 1 <= h x])=> //.
- apply: closedI.
  + exact ((@continuous_closedP X (real_line_metric R) h).1 hh.1 _ (@order_closed_upper_ray_closed _ [the orderTopologicalType _ of R^o] 1)).
  + rewrite closedC; exact: compact_support_increasing_level_open hE.
Qed.
