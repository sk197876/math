(** Federer (1969), 2.2.14, p. 70, final paragraph: Borel maps between
    complete separable metric spaces send Suslin sets to Suslin sets. We
    retain the graph and second-projection factorisation printed in the
    book. Source editions: BorelFunctionUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality reals topology.
From Federer Require Import BorelFunctionUP BorelGraphs BorelImageMeasurability
  SuslinSetUP SuslinPreimages SuslinSequenceClosure BorelClosedProjection
  MetricProductBackground MetricProductCompleteness MetricProductSeparability
  CompleteMetricUP TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [suslin_binary_intersection]: supporting two-set
    instance of Federer 2.2.10, p. 66, used in the
    displayed graph-image formula of 2.2.14, p. 70. *)
Lemma suslin_binary_intersection (R : realType) (T : topologicalType) (A B : set T) :
  is_suslin_set R A -> is_suslin_set R B -> is_suslin_set R (A `&` B).
Proof.
move=> ha hb.
have he : A `&` B = \bigcap_n (if n == 0%N then A else B).
  apply/seteqP; split.
  - move=> x [hx hy] n _; by case: ifP.
  - move=> x hx; split; [exact: (hx 0%N Logic.I)|exact: (hx 1%N Logic.I)].
rewrite he; apply: suslin_sequence_intersection=> n; by case: ifP.
Qed.

(** Source for [borel_function_suslin_image]: direct final
    assertion in Federer 2.2.14, p. 70. The set
    g(A) is the intersection of A times Y with the Borel
    graph, hence Suslin in the complete separable product. The
    continuous second projection has image f(A), which is Suslin. *)
Theorem borel_function_suslin_image (R : realType) (X Y : metricType R)
    (f : X -> Y) (A : set X) :
  is_complete_metric_space X -> is_complete_metric_space Y ->
  (exists D : set X, countable D /\ dense D) ->
  (exists D : set Y, countable D /\ dense D) ->
  is_borel_function f -> is_suslin_set R A -> is_suslin_set R (f @` A).
Proof.
move=> hX hY hsX hsY hf hA.
pose P := [the metricType R of metric_product X Y].
pose G : set P := [set p | A p.1 /\ f p.1 = p.2].
have hG : is_suslin_set R G.
  apply: (@suslin_binary_intersection R P (fst @^-1` A) [set p | f p.1 = p.2]).
  - exact: continuous_preimage_suslin (@first_projection_continuous X Y) hA.
  - apply: metric_borel_suslin; exact: borel_function_graph hsY hf.
have hp : is_complete_metric_space P := complete_metric_product hX hY.
have hsP : exists D : set P, countable D /\ dense D := separable_metric_product hsX hsY.
have he : (@snd X Y) @` G = f @` A.
  apply/seteqP; split.
  - move=> y [[x z] [hx heq] <-]; exists x=> //; exact heq.
  - move=> y [x hx <-]; exists (x,f x)=> //; by split.
rewrite -he; exact: continuous_suslin_image hp hsP (@metric_hausdorff R Y)
  (@second_projection_continuous X Y) hG.
Qed.
