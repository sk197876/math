(** Federer (1969), 2.3.8, p. 78, bracketed assertion: essential
    separability is automatic for a countably measurable source and a target
    with a dense set of Ulam cardinality. The proof uses the 2.2.16/2.3.6
    image-support reduction on each finite-measure source piece, then a
    common closed separable linear envelope. Source context and
    partial-domain convention: MeasurableNormedFunctionUP.v. Each image
    support controls its own source piece, not the entire source; see the
    qualification recorded for 2.3.6. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import ModuleQuotient RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic
  PartialFunctionPreimages MeasureUP MeasureRestriction MeasurePushforward MeasureSupport
  MeasureAlmostBasic MeasureNullModification MeasurableFunctionUP MeasurableTotalExtension
  MeasurableFiniteImageSupport UlamCardinalUP MetricSubsetBackground
  CountablyMeasurableUP CountablyMeasurableSequences ClosedLinearSpanUP SeparableLinearEnvelope
  MeasurableNormedFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_normed_ulam_essentially_separable]: direct
    bracketed assertion of Federer 2.3.8, p. 78. No
    finite-dimensionality or separability of the whole Banach target
    is assumed; completeness is not needed for this assertion. *)
Theorem measurable_normed_ulam_essentially_separable (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (D : set (real_norm_metric_space hN))
    (f : partial_function X (real_norm_metric_space hN)) :
  measure_countably_measurable mu setT -> dense D -> is_ulam_set R D ->
  is_measure_measurable_function mu f -> is_measurable_normed_function mu f.
Proof.
move=> hX hd hu hf; split=> //.
have [A [hcover hA]] := proj1 (@countably_measurable_sequence_iff R X mu hm setT) hX.
have [g [hgf [heq hg]]] := @measurable_function_total_extension R X
  [the topologicalType of real_norm_metric_space hN] mu hm f 0%R hf.
pose S n := measure_support (measure_pushforward g (measure_restrict mu (A n))).
have hS n := @measurable_finite_image_support R X
  [the metricType R of real_norm_metric_space hN] mu hm g (A n) D hg (hA n).2 hd hu.
have hs n : exists H : set (metric_subset (S n)), countable H /\ dense H := (hS n).2.1.
have [Z [hc [hi hsep]]] := @countable_separable_sets_linear_envelope R V N hN S hs.
exists Z; split=> //.
rewrite (@almost_equal_preimage_measure R X (real_norm_metric_space hN) mu hm f
  (partial_function_total g) [set y | ~ Z y] heq) partial_function_total_preimage.
apply: (@measure_null_subset R X mu hm _
  (\bigcup_n (A n `&` (g @^-1` (~` S n))))).
- move=> x hn.
  have hx : (\bigcup_n A n) x by rewrite -hcover.
  have [n _ hax] := hx; exists n=> //; split=> // hsx.
  apply: hn; apply: hi; by exists n.
- apply: (@measure_null_countable_union R X nat mu hm setT _ (countableP _)).
  by move=> n _; exact: (hS n).2.2.
Qed.
