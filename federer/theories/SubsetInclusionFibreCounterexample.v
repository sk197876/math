(** Federer (1969), 2.10.26, p. 189: the inclusion of a nonmeasurable subset
    of the real line gives a nonmeasurable fibre-mass function for k=0,m=1.
    Prove the exact counting-fibre identity for any metric subset first,
    then use its positive superlevel to recover the subset. The real-line
    statement uses the proved equality of degree-one Hausdorff and Lebesgue
    measure from 2.10.7, p. 175. The metric subtype is existing
    general-topology infrastructure, not a new replacement definition of a
    measure. no identical inclusion example was found. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import CountableOrderIntervals ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  LipschitzUP MetricSubsetBackground HausdorffMeasure HausdorffCountingMeasure HausdorffFibreCutoffs
  MeasureUP MeasureBasic MeasurableFunctionUP RealMetricBackground RealHausdorffLebesgue
  LebesgueScalarMeasure RealMetricCompleteness RealLineSeparability BernsteinNonmeasurableSubset.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [subset_inclusion_lipschitz_bound]: supporting
    Lipschitz property of the inclusion in the example
    of 2.10.26, p. 189. The inclusion preserves
    distances; the bound one works also on an
    empty or singleton source. *)
Lemma subset_inclusion_lipschitz_bound (R : realType) (Y : metricType R) (A : set Y) :
  is_metric_lipschitz_bound setT (fun x : metric_subset A=>(val x : Y)) 1%R.
Proof.
split; first exact: ler01.
by move=> x z _ _; rewrite metric_subset_distanceE mul1r.
Qed.

(** Source for [subset_inclusion_counting_fibre]: direct
    k=0 fibre computation in the inclusion example
    of 2.10.26, p. 189. A fibre consists of
    one subtype point if y belongs to A, and
    otherwise is empty. No measurability of A is used. *)
Theorem subset_inclusion_counting_fibre (R : realType) (Y : metricType R) (A : set Y) (y : Y) :
  hausdorff_fibre_mass (fun x : metric_subset A=>(val x : Y)) setT 0 y=
    (if y \in A then 1 else 0).
Proof.
rewrite /hausdorff_fibre_mass; case: (boolP (y \in A))=> hy.
- pose a : metric_subset A := Sub y hy.
  have he : setT `&` (fun x : metric_subset A=>(val x : Y)) @^-1` [set y]=[set a].
    apply/seteqP; split=> [x [_ hx]|x ->]; last by split.
    apply: val_inj; exact hx.
  rewrite he; exact: hausdorff_zero_singleton.
- have he : setT `&` (fun x : metric_subset A=>(val x : Y)) @^-1` [set y]=set0.
    apply/seteqP; split=> [x [_ hx]|x []].
    exfalso; apply: (negP hy); have hval : A (val x) := set_valP x.
    rewrite (hx : val x=y) in hval; exact: mem_set hval.
  rewrite he; exact: measure_empty (@hausdorff_measure_is_measure R _ 0).
Qed.

(** Source for [subset_inclusion_fibre_nonmeasurable]: direct
    mechanism of the nonmeasurable inclusion example in
    2.10.26, p. 189. A measurable fibre integrand
    would have measurable positive preimage, exactly A.
    The target measure is arbitrary here, which is
    supporting generality rather than an extra source claim. *)
Theorem subset_inclusion_fibre_nonmeasurable (R : realType) (Y : metricType R)
    (mu : set Y -> \bar R) (A : set Y) :
  ~ measure_measurable mu A ->
  ~ is_measure_measurable_function mu (partial_function_total
    (hausdorff_fibre_mass (fun x : metric_subset A=>(val x : Y)) setT 0)).
Proof.
move=> hA hmeas; apply: hA.
have ho : open [set z : extended_real_line R | 0<z].
  exact: order_strict_upper_ray_open.
have hh := measurable_function_open_preimage hmeas ho.
have he : partial_function_preimage (partial_function_total
    (hausdorff_fibre_mass (fun x : metric_subset A=>(val x : Y)) setT 0))
    [set z : extended_real_line R | 0<z]=A.
  apply/seteqP; split.
  - move=> y [z [hz hpos]].
    rewrite -(hz : hausdorff_fibre_mass (fun x : metric_subset A=>(val x : Y)) setT 0 y=z)
      subset_inclusion_counting_fibre in hpos.
    case: (boolP (y \in A))=> hy; first exact: set_mem hy.
    rewrite (negbTE hy) in hpos.
    have hbad : (0 : \bar R)<0 := hpos; by rewrite ltxx in hbad.
  - move=> y hy; exists 1; split; last first.
      change (is_true ((0 : \bar R)<1)); by rewrite lte_fin ltr01.
    change (hausdorff_fibre_mass (fun x : metric_subset A=>(val x : Y)) setT 0 y = 1).
    by rewrite subset_inclusion_counting_fibre (mem_set hy).
by rewrite he in hh.
Qed.

(** Source for [real_subset_inclusion_fibre_nonmeasurable]:
    direct conditional example of 2.10.26, p. 189:
    every non-Lebesgue-measurable real subset supplies
    the printed k=0,m=1 inclusion counterexample.
    This theorem does not claim construction of such
    a set; existence is a separate set-theoretic result. *)
Corollary real_subset_inclusion_fibre_nonmeasurable (R : realType) (A : set (real_line_metric R)) :
  ~ measure_measurable (@lebesgue_scalar_measure R) A ->
  ~ is_measure_measurable_function (@hausdorff_measure R [the metricType R of real_line_metric R] 1)
    (partial_function_total
      (hausdorff_fibre_mass (fun x : metric_subset A=>(val x : real_line_metric R)) setT 0)).
Proof.
move=> hA; apply: subset_inclusion_fibre_nonmeasurable.
have he : @hausdorff_measure R [the metricType R of real_line_metric R] 1=@lebesgue_scalar_measure R.
  apply: funext=> B; exact: real_hausdorff_measure_one_lebesgue.
by rewrite he.
Qed.

(** Source for [real_nonmeasurable_inclusion_exists]: direct
    existence of the example required in 2.10.26,
    p. 189. Apply the proved nonmeasurable-subset
    theorem 2.2.4, p. 62, inside the unit
    interval, then the inclusion fibre identity. This
    uses the book's own set-theoretic argument and
    does not postulate a nonmeasurable set. *)
Theorem real_nonmeasurable_inclusion_exists (R : realType) :
  exists A : set (real_line_metric R), A `<=` `[(0%R : R),1%R] /\
    is_metric_lipschitz_bound setT (fun x : metric_subset A=>(val x : real_line_metric R)) 1%R /\
    ~ is_measure_measurable_function (@hausdorff_measure R [the metricType R of real_line_metric R] 1)
      (partial_function_total
        (hausdorff_fibre_mass (fun x : metric_subset A=>(val x : real_line_metric R)) setT 0)).
Proof.
pose Y := [the metricType R of real_line_metric R].
pose mu := @lebesgue_scalar_measure R.
have hmass : mu `[(0%R : R),1%R] = 1 by rewrite /mu lebesgue_scalar_segment ?ler01 // subr0.
have hpos : 0<mu `[(0%R : R),1%R] by rewrite hmass lte_fin ltr01.
have hfin : mu `[(0%R : R),1%R]< +oo by rewrite hmass; exact: ltry.
have [A [hA hnon]] := @borel_regular_nonmeasurable_subset R Y mu
  (lebesgue_scalar_is_measure R) (lebesgue_scalar_borel_regular R) `[(0%R : R),1%R]
  (@real_line_metric_complete R) (@real_line_countable_dense R) hpos hfin
  (fun x _=>lebesgue_scalar_singleton x).
exists A; split=> //; split; first exact: subset_inclusion_lipschitz_bound.
exact: real_subset_inclusion_fibre_nonmeasurable hnon.
Qed.
