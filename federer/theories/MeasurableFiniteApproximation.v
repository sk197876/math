(** Federer (1969), 2.4.12, p. 87: finite-image approximations on the
    separable essential range of a member of A. The finite Borel partitions
    used here give a pointwise norm majorant, making explicit the
    finite-image reduction left as an exercise. This preparatory statement
    uses total representatives; norm invariance transfers the eventual Lp
    density claim to the book's partial-domain functions. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ModuleQuotient MetricSubsetBackground
  PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages PartialFunctionLimitUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasurableNormedFunctionUP
  MeasurableTotalBasic MeasurableNormedCountableRange EssentialSeparableEnvelope
  SeparableFiniteApproximationUP SeparableFiniteApproximationSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_total_finite_approximation]: supporting
    finite-image approximation for Federer 2.4.12, p. 87 Each approximant
    belongs to A, has finite image, converges almost everywhere to f, and
    its pointwise error is bounded by the original norm almost everywhere. *)
Theorem measurable_total_finite_approximation (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : X -> real_norm_metric_space hN) :
  is_measurable_normed_function mu (partial_function_total f) ->
  exists g : nat -> X -> real_norm_metric_space hN,
    (forall n, is_measurable_normed_function mu (partial_function_total (g n))) /\
    (forall n, finite_set (g n @` setT)) /\
    measure_almost_everywhere mu (partial_function_limit_locus
      (fun n => partial_function_total (g n)) (partial_function_total f)) /\
    forall n, measure_almost_everywhere mu [set x | (N (f x-g n x) <= N (f x))%R].
Proof.
move=> hf.
have [Z [hZ [[D [hc hd]] hz]]] := @essential_separable_sequence_envelope R X V N hN mu hm
  (fun _ : nat => partial_function_total f) (fun _ => hf.2).
pose a := @SeparableFiniteApproximation.value R V N hN Z D hZ hc hd.
have ha := @SeparableFiniteApproximation.laws R V N hN Z D hZ hc hd.
pose g n x := a n (f x).
have hfinite n : finite_set (g n @` setT).
  apply: (sub_finite_set (B:= a n @` setT)); last exact: separable_finite_image ha n.
  move=> z [x _ <-]; by exists (f x).
have hconull : measure_almost_everywhere mu [set x | Z (f x)].
  have hh := hz 0%N; rewrite partial_function_total_preimage in hh; exact hh.
exists g; split.
- move=> n; apply: (@measurable_normed_countable_total_range R X V N hN mu hm (g n)).
  + exact (@measurable_total_borel_postcomposition R X [the topologicalType of real_norm_metric_space hN]
      [the topologicalType of real_norm_metric_space hN] mu hm f (a n) hf.1 (separable_finite_borel ha n)).
  + exact: finite_set_countable (hfinite n).
split=> //; split.
- apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hconull).
  move=> x hx; exists (fun n => g n x),(f x); split=> //; split=> //.
  exact (@separable_finite_converges R V N hN Z a ha (f x) hx).
- move=> n; apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hconull).
  move=> x hx; exact (@separable_finite_error R V N hN Z a ha n (f x) hx).
Qed.
