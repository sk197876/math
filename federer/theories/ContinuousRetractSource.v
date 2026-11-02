(** Federer (1969), 2.2.13, pp. 69–70: continuous Borel images from a
    complete separable metric space are measurable. This supporting
    transport permits a continuous surjection with a specified right
    inverse, so a homeomorphic presentation can supply completeness without
    changing the chosen metric. Used for the Euclidean plane in 2.5.10, p.
    101. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import CompleteMetricUP MeasureUP TopologicalBorel
  ContinuousBorelPreimages BorelImageMeasurability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [continuous_retraction_separable]: supporting
    preservation of separability under a continuous surjection
    in the application of Federer 2.2.13, pp. 69–70,
    to 2.5.10, p. 101. The supplied right inverse
    only witnesses surjectivity in this lemma. *)
Lemma continuous_retraction_separable (X Y : topologicalType)
    (j : X -> Y) (q : Y -> X) :
  continuous j -> cancel q j ->
  (exists D : set X, countable D /\ dense D) ->
  exists E : set Y, countable E /\ dense E.
Proof.
move=> hj hq [D [hD hd]]; exists (j @` D); split.
- exact: sub_countable (card_image_le _ _) hD.
- move=> W [y hy] hW.
  have hn : j @^-1` W !=set0 by exists (q y); rewrite /preimage /= hq.
  have ho : open (j @^-1` W).
    apply: open_comp=> // x _; exact: hj.
  have [x [hx hDx]] := hd (j @^-1` W) hn ho.
  exists (j x); split=> //; by exists x.
Qed.

(** Source for [continuous_retract_borel_image_measurable]:
    supporting change of source in Federer 2.2.13,
    pp. 69–70. The complete separable domain is X;
    the target source Y has a right inverse q for
    the continuous surjection j. No completeness of its
    particular metric is asserted. *)
Lemma continuous_retract_borel_image_measurable (R : realType)
    (X : metricType R) (Y Z : topologicalType)
    (j : X -> Y) (q : Y -> X) (f : Y -> Z)
    (mu : set Z -> \bar R) (hm : is_measure mu) :
  is_complete_metric_space X ->
  (exists D : set X, countable D /\ dense D) ->
  continuous j -> cancel q j -> hausdorff_space Z -> continuous f ->
  (forall C, closed C -> measure_measurable mu C) ->
  forall A, borel_set A -> measure_measurable mu (f @` A).
Proof.
move=> hX hs hj hq hZ hf hc A hA.
have he : (fun x => f (j x)) @` (j @^-1` A)=f @` A.
  apply/seteqP; split.
  - move=> z [x hx <-]; by exists (j x).
  - move=> z [y hy <-]; exists (q y); by rewrite /= hq.
rewrite -he; apply: (@continuous_borel_image_measurable R X Z
  (fun x => f (j x)) mu hm (j @^-1` A) hX hs hZ _ hc).
- move=> x; exact: continuous_comp (hj x) (hf (j x)).
- exact (@continuous_borel_preimage X Y j hj A hA).
Qed.
