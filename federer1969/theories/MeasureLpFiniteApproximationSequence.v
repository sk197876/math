(** Federer (1969), 2.4.12, pp. 87–88: finite-image approximants used in
    constructing the vector integral. This supporting sequence form combines
    the proved density construction with almost-equality invariance and
    symmetry. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureStepFunctionUP MeasurableNormedBasic MeasureLpMembershipUP MeasureLpConvergence
  MeasureLpAlmostEquality MeasureLpTotalFiniteApproximation MeasureLpDistanceLaws ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_lp_finite_image_approximation_sequence]:
    supporting sequential density used to extend the vector integral
    in Federer 2.4.12, pp. 87–88. The input retains its
    original partial domain; every approximant is an actual Lp member. *)
Theorem measure_lp_finite_image_approximation_sequence (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f : partial_function X (real_norm_metric_space hN)) :
  is_measure_lp_function mu p f ->
  exists g : nat -> partial_function X (real_norm_metric_space hN),
    (forall n, is_measure_lp_function mu p (g n)) /\
    (forall n, finite_set (partial_function_range (g n))) /\ converges_in_lp_norm mu N p g f.
Proof.
move=> hf.
have [F [hext [heq hF]]] := @measurable_normed_total_representative R X V N hN mu hm f hf.2.1.
have hFlp := @measure_lp_function_almost_equal R X V N hN mu hm p f _ hf heq.
have [g [hg [hfinite hl]]] := @measure_lp_total_finite_image_approximation R X V N hN mu hm p F hFlp.
exists (fun n => partial_function_total (g n)); split=> //; split.
- move=> n; have hr : partial_function_range (partial_function_total (g n)) = g n @` setT.
    apply/seteqP; split=> y; first by move=> [x hx]; exists x.
    by move=> [x _ hx]; exists x.
  rewrite hr; exact: hfinite n.
- move=> epsilon he; have heE : (0 : \bar R) < epsilon%:E by rewrite lte_fin.
  have [K hK] := hl.2 epsilon%:E heE; exists K=> n hn.
  rewrite (@measure_lp_distance_symmetric R X V N hN mu hm p _ f hf.1 (hg n).2.1 hf.2.1).
  rewrite (@measure_lp_distance_almost_left R X V N hN mu hm p f _ _ hf.1 hf.2.1 hF (hg n).2.1 heq).
  exact: hK n hn.
Qed.
