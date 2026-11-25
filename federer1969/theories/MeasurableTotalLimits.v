(** Federer (1969), 2.3.2(6), pp. 73–74: almost everywhere limits of total
    measurable maps into arbitrary metric spaces. This supporting case uses
    exactly the printed open-inner- set formula and null modifications. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages
  MeasureUP MeasureSplit MeasureCountableClosure MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasurableAlmostModification PointwiseLimit PointwiseOpenPreimage
  MetricSetDistanceUP MetricSetDistanceSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [convergent_open_membership_formula]: supporting
    single-point version of the exact formula in Federer 2.3.2(6),
    p. 74. The existing pointwise formula is applied to a
    one-point source; no separability premise is introduced. *)
Lemma convergent_open_membership_formula (R : realType) (Y : metricType R)
    (u : nat -> Y) (z : Y) (U : set Y) (d : Y -> R)
    (hd : is_metric_set_distance (~` U) d) :
  open U -> u @ \oo --> z ->
  (U z <-> exists i N, forall n, (N <= n)%N -> metric_open_inner d i (u n)).
Proof.
move=> ho hl.
have hp : is_pointwise_limit (fun n (_ : unit) => u n) (fun _ => z) by move=> [].
have he := @pointwise_open_preimage_formula R unit Y
  (fun n (_ : unit) => u n) (fun _ => z) U d hd ho hp.
split.
- move=> hz; have h : ((fun _ : unit => z) @^-1` U) tt := hz.
  rewrite he in h; have [i _ [N _ hN]] := h; by exists i, N.
- move=> [i [N hN]].
  have h : (\bigcup_i \bigcup_N \bigcap_(n in [set n | (N <= n)%N])
      ((fun _ : unit => u n) @^-1` metric_open_inner d i)) tt.
    exists i; first exact Logic.I.
    exists N; first exact Logic.I.
    exact hN.
  by rewrite -he in h.
Qed.

(** Source for [measurable_total_functions_almost_limit]: total
    function case of Federer 2.3.2(6), pp. 73–74.
    The exceptional set is the complement of P; the proof uses
    measurable countable unions and intersections and completeness. *)
Theorem measurable_total_functions_almost_limit (R : realType)
    (X : choiceType) (Y : metricType R) (mu : set X -> \bar R)
    (hm : is_measure mu) (f : nat -> X -> Y) (g : X -> Y) (P : set X) :
  (forall n, is_measure_measurable_function mu (partial_function_total (f n))) ->
  measure_almost_everywhere mu P ->
  (forall x, P x -> (fun n => f n x) @ \oo --> g x) ->
  is_measure_measurable_function mu (partial_function_total g).
Proof.
move=> hf hP hl; constructor.
- rewrite partial_function_total_domain; exact: measure_almost_everywhere_true hm.
- move=> U ho; rewrite partial_function_total_preimage.
  case: (pselect ((~` U) !=set0))=> [hn|hn]; last first.
    have he : U = setT.
      apply/seteqP; split=> [y hy|y _]; first exact Logic.I.
      apply: contrapT=> hy; apply: hn; by exists y.
    rewrite he preimage_setT; exact: measure_measurable_whole hm.
  pose d := @MetricSetDistance.value R Y (~` U) hn.
  have hd := @MetricSetDistance.laws R Y (~` U) hn.
  pose A := \bigcup_i \bigcup_N \bigcap_(n in [set n | (N <= n)%N])
    (f n @^-1` metric_open_inner d i).
  have hA : measure_measurable mu A.
    apply: (@measure_measurable_countable_union R X nat mu hm setT _ (countableP _))=> i _.
    apply: (@measure_measurable_countable_union R X nat mu hm setT _ (countableP _))=> N _.
    apply: (@measure_measurable_countable_intersection R X nat mu hm _ _ (countableP _))=> n hN.
    have h := measurable_function_open_preimage (hf n) (metric_open_inner_open hd i).
    by rewrite partial_function_total_preimage in h.
  apply: (@measurable_set_null_modification R X mu hm A _ (~` P) hP _ hA).
  move=> x hnn; have hx : P x by apply: contrapT=> hx; exact: hnn.
  have he := @convergent_open_membership_formula R Y (fun n => f n x) (g x) U d hd ho (hl x hx).
  split.
  + move=> [i _ [N _ hN]]; apply: (proj2 he); by exists i, N.
  + move=> hg; have [i [N hN]] := proj1 he hg.
    exists i; first exact Logic.I.
    exists N; first exact Logic.I.
    exact hN.
Qed.
