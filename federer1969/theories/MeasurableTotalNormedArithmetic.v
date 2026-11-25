(** Federer (1969), 2.3.8, pp. 78–79: pointwise vector operations on total
    representatives. Federer's erratum p. 1, book p. 78 line 7, instead
    corrects the full partial collection to a set. We distinguish the total
    subcollection explicitly. Source context: MeasurableNormedFunctionUP.v. *)
From mathcomp Require Import all_boot all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic
  PartialNormedArithmetic MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableNormedFunctionUP MeasurableNormedArithmetic MeasurableNormedBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [measurable_normed_total_add]: direct additive closure on
    total representatives for Federer 2.3.8, p. 78 *)
Lemma measurable_normed_total_add (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (f g : X -> real_norm_metric_space hN) :
  is_measurable_normed_function mu (partial_function_total f) ->
  is_measurable_normed_function mu (partial_function_total g) ->
  is_measurable_normed_function mu (partial_function_total (fun x => f x+g x)).
Proof.
move=> hf hg; have hsum := @measurable_normed_function_add R X V N hN mu hm _ _ hf hg.
apply: (@measurable_normed_almost_equal R X V N hN mu hm _ _ hsum).
apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm)).
move=> x _; exists (f x+g x); split=> //.
apply: (proj2 (partial_vector_add_graph _ _ x _)); exists (f x),(g x); by split=> //; split.
Qed.

(** Source for [measurable_normed_total_scale]: scalar closure on total
    representatives used in Federer 2.3.8, p. 79 *)
Lemma measurable_normed_total_scale (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (c : R)
    (f : X -> real_norm_metric_space hN) :
  is_measurable_normed_function mu (partial_function_total f) ->
  is_measurable_normed_function mu (partial_function_total (fun x => c *: f x)).
Proof.
move=> hf; have hscale := @measurable_normed_function_scale R X V N hN mu hm c _ hf.
apply: (@measurable_normed_almost_equal R X V N hN mu hm _ _ hscale).
apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm)).
move=> x _; exists (c *: f x); split=> //.
apply: (proj2 (partial_vector_scale_graph c _ x _)); exists (f x); by split.
Qed.
