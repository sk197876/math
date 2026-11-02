(** Federer (1969), 2.2.1, p. 60: metric-space instances of the two
    topological generation criteria. Source context: BorelFamilyUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology pseudometric_structure.
From Federer Require Import CountablyClosedFamilyUP TopologicalBorel
  TopologicalBorelGeneration MetricOpenClosedCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [metric_has_closed_sequence_covers]: Federer
    2.2.1, p. 60, metric instance of the closed-cover hypothesis.
    It is obtained from the local existence proof, rather than an
    external descriptive-set-theory theorem. *)
Lemma metric_has_closed_sequence_covers (R : realType) (T : pseudoMetricType R) :
  has_closed_sequence_covers T.
Proof.
move=> U ho; have [C [hc he]] := metric_open_countable_closed_cover ho.
exists C; split=> // n; exact: (hc n).1.
Qed.

(** Source for [metric_borel_generated_by_open_closure]: Federer
    2.2.1, p. 60, open generators and either countable-union
    convention in a metric space; includes the printed weaker case. *)
Theorem metric_borel_generated_by_open_closure (d : bool) (R : realType)
    (T : pseudoMetricType R) (F : set (set T)) :
  is_generated_closed_family d setT (@open T) F -> F = @borel_set T.
Proof. exact: (@borel_generated_by_open_closure d T F (@metric_has_closed_sequence_covers R T)). Qed.

(** Source for [metric_borel_generated_by_closed_closure]: Federer
    2.2.1, p. 60, closed generators with unrestricted countable
    unions and nonempty countable intersections in a metric space. *)
Theorem metric_borel_generated_by_closed_closure (R : realType)
    (T : pseudoMetricType R) (F : set (set T)) :
  is_generated_closed_family false setT (@closed T) F -> F = @borel_set T.
Proof. exact: (@borel_generated_by_closed_closure T F (@metric_has_closed_sequence_covers R T)). Qed.
