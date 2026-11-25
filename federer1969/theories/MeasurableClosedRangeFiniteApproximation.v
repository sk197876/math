(** Federer (1969), 2.4.19, p. 91: finite-image approximants take their
    values in C. This supporting assembly restricts to the closed separable
    essential range intersected with C, then uses only the sealed closed-set
    approximation laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ModuleQuotient MetricSubsetBackground
  PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages PartialFunctionLimitUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableNormedFunctionUP MeasurableNormedCountableRange
  MeasurableTotalBasic EssentialSeparableEnvelope MeasureLpRangeRepresentative SeparableClosedIntersection
  ClosedSetFiniteApproximationUP ClosedSetFiniteApproximationSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_closed_range_finite_approximation]: supporting
    C-valued finite approximation in Federer 2.4.19, p. 91 The target may
    have arbitrary dimension and need not itself be separable. The error is
    bounded by distance to one fixed point of C on the common conull range. *)
Theorem measurable_closed_range_finite_approximation (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (C : set (real_norm_metric_space hN)) (f : X -> real_norm_metric_space hN) :
  mu setT != 0 -> closed C -> is_measurable_normed_function mu (partial_function_total f) ->
  measure_almost_everywhere mu [set x | C (f x)] ->
  exists z : V, exists g : nat -> X -> real_norm_metric_space hN,
    C z /\ (forall n, is_measurable_normed_function mu (partial_function_total (g n))) /\
    (forall n, finite_set (g n @` setT)) /\ (forall n x, C (g n x)) /\
    measure_almost_everywhere mu (partial_function_limit_locus
      (fun n => partial_function_total (g n)) (partial_function_total f)) /\
    forall n, measure_almost_everywhere mu [set x | (N (f x-g n x) <= N (f x-z))%R].
Proof.
move=> hmass hC hf hCf.
have [Z [hZ [[D [hc hd]] hz]]] := @essential_separable_sequence_envelope R X V N hN mu hm
  (fun _ : nat => partial_function_total f) (fun _ => hf.2).
pose S : set (real_norm_metric_space hN) := fun x => Z x.
pose K := S `&` C.
have hK : closed K by apply: closedI.
have hZf : measure_almost_everywhere mu [set x | S (f x)].
  have hh := hz 0%N; rewrite partial_function_total_preimage in hh; exact hh.
have hKf : measure_almost_everywhere mu [set x | K (f x)].
  exact: (@measure_almost_everywhere_and R X mu hm _ _ hZf hCf).
have hpre : measure_almost_everywhere mu (partial_function_preimage (partial_function_total f) K).
  by rewrite partial_function_total_preimage.
have hnon := @positive_measure_conull_range_nonempty R X (real_norm_metric_space hN)
  mu (partial_function_total f) K hmass hpre.
have [H [hHc hHd]] := @separable_closed_intersection R
  [the metricType R of real_norm_metric_space hN] S C (ex_intro _ D (conj hc hd)) hC hnon.
have [z hzK] := hnon.
pose z0 : metric_subset K := @exist (real_norm_metric_space hN) (fun x => x \in K) z (mem_set hzK).
pose a := @ClosedSetFiniteApproximation.value R V N hN K z0 H hK hHc hHd.
have ha := @ClosedSetFiniteApproximation.laws R V N hN K z0 H hK hHc hHd.
pose g n x := a n (f x).
have hfinite n : finite_set (g n @` setT).
  apply: (sub_finite_set (B:= a n @` setT)); last exact: closed_set_finite_image ha n.
  move=> y [x _ <-]; by exists (f x).
exists z,g; split; first exact hzK.2.
split.
- move=> n; apply: (@measurable_normed_countable_total_range R X V N hN mu hm (g n)).
  + exact: (@measurable_total_borel_postcomposition R X [the topologicalType of real_norm_metric_space hN]
      [the topologicalType of real_norm_metric_space hN] mu hm f (a n) hf.1 (closed_set_finite_borel ha n)).
  + exact: finite_set_countable (hfinite n).
split=> //; split.
- move=> n x; exact (closed_set_finite_range ha n (f x)).2.
split.
- apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hKf)=> x hx.
  exists (fun n => g n x),(f x); split=> //; split=> //.
  exact: (@closed_set_finite_converges R V N hN K z a ha (f x) hx).
- move=> n; apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hKf)=> x hx.
  exact: (@closed_set_finite_error R V N hN K z a ha n (f x) hx).
Qed.
