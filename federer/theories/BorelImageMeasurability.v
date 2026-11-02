(** Federer (1969), 2.2.13, pp. 69–70: continuous images of Borel sets from
    a complete separable metric space into a Hausdorff space are measurable
    for any measure making all closed sets measurable. As in the book,
    combine 2.2.10 with 2.2.12. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality reals
  constructive_ereal topology.
From Federer Require Import CompleteMetricUP SuslinSetUP TopologicalBorel
  BorelClosedProjection SuslinContinuousImages MetricSubsetBackground
  MeasureUP SuslinMeasurability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [continuous_suslin_image]: supporting ambient-map
    form of Federer 2.2.10, p. 65, used in 2.2.13,
    pp. 69–70. The established theorem accepts a map on
    the actual subspace; here a globally continuous map is restricted
    to that subspace without requiring an extension argument. *)
Lemma continuous_suslin_image (R : realType) (X : metricType R)
    (Y : topologicalType) (f : X -> Y) (S : set X) :
  is_complete_metric_space X ->
  (exists D : set X, countable D /\ dense D) ->
  hausdorff_space Y -> continuous f -> is_suslin_set R S ->
  is_suslin_set R (f @` S).
Proof.
move=> hX hsep hY hf hS.
pose g (x : metric_subset S) := f (val x).
have hg : continuous g.
  move=> x; apply: continuous_comp _ (hf (val x)).
  exact: metric_subset_inclusion_continuous.
have he : g @` setT = f @` S.
  apply/seteqP; split.
  - move=> y [x _ <-]; exists (val x)=> //; exact: set_valP.
  - move=> y [x hx <-]; exists (Sub x (mem_set hx))=> //.
rewrite -he; exact: continuous_suslin_subspace_image hX hsep hS hY hg.
Qed.

(** Source for [continuous_borel_image_measurable]: direct
    proposition in Federer 2.2.13, pp. 69–70. Every
    Borel subset of the complete separable metric source has
    measurable image, with the printed Hausdorff-target and closed-
    measurability hypotheses retained. No injectivity is required. *)
Theorem continuous_borel_image_measurable (R : realType) (X : metricType R)
    (Y : topologicalType) (f : X -> Y) (mu : set Y -> \bar R)
    (hm : is_measure mu) (A : set X) :
  is_complete_metric_space X ->
  (exists D : set X, countable D /\ dense D) ->
  hausdorff_space Y -> continuous f ->
  (forall C : set Y, closed C -> measure_measurable mu C) ->
  borel_set A -> measure_measurable mu (f @` A).
Proof.
move=> hX hsep hY hf hc hA; apply: (@suslin_set_measurable R Y mu hm (f @` A) hc).
apply: (@continuous_suslin_image R X Y f A hX hsep hY hf); exact: metric_borel_suslin hA.
Qed.
