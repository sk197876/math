(** Federer (1969), 2.9.10, p. 157: continuous/singular derivates and
    independence of the Vitali relation. All scalar values retain partial
    domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From mathcomp.analysis.normedtype_theory Require Import num_normedtype.
From Federer Require Import RealMetricBackground FunctionLatticeUP FunctionLatticeLevelFamilies
  BoundedSupportContinuous TopologicalBorel BorelFamilyBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [bounded_continuous_strict_level_open]: supporting
    F0 topology for the first observation of Federer 2.9.10,
    p. 157. Strict positive levels of the given continuous
    functions are open; bounded support is not needed for openness. *)
Lemma bounded_continuous_strict_level_open (R : realType) (X : metricType R) S :
  function_lattice_strict_levels (@bounded_support_continuous_functions R X) S -> open S.
Proof.
move=> [f [t [[hf _] [_ ->]]]].
change (open (f @^-1` [set y : real_line_metric R | t<y])).
apply: (continuousP f).1 hf.1 _ _.
change (open [set y : R^o | t<y]); exact: open_gt.
Qed.

(** Source for [bounded_continuous_increasing_level_open]: supporting
    F1 topology for the first observation of Federer 2.9.10,
    p. 157. Countable increasing unions of F0 levels are open. *)
Lemma bounded_continuous_increasing_level_open (R : realType) (X : metricType R) S :
  function_lattice_increasing_levels (@bounded_support_continuous_functions R X) S -> open S.
Proof.
move=> [V [hV [_ ->]]]; apply: bigcup_open=> n _.
exact: bounded_continuous_strict_level_open (hV n).
Qed.

(** Source for [bounded_continuous_finite_hull_borel]: supporting
    Borel regularity in the first observation of Federer 2.9.10,
    p. 157. The F2 hull is a countable intersection of open
    F1 sets, hence Borel; its first-set finiteness is independent
    of this purely topological inference. *)
Lemma bounded_continuous_finite_hull_borel (R : realType) (X : metricType R)
    (phi : set X -> \bar R) S :
  function_lattice_finite_hulls (@bounded_support_continuous_functions R X) phi S -> borel_set S.
Proof.
move=> [V [hV [_ [_ ->]]]].
apply: (@borel_set_countable_intersection X nat setT V (countableP _) (ex_intro _ 0%N Logic.I))=> n _.
apply: open_borel_set; exact: bounded_continuous_increasing_level_open (hV n).
Qed.
