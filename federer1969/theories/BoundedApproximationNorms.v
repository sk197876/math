(** Federer (1969), 2.4.16, p. 90: each bounded finite- measure approximant
    has finite Lp norm, and these norms become unbounded when
    phi_p(f)=infinity. The proof below uses the already proved Fatou
    lower-semicontinuity inequality, which suffices for unboundedness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic PartialFunctionLimitUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasureLpNorm MeasureLpNormLowerLimit
  ExtendedRealBoundsUP ExtendedLowerLimitUP ExtendedLowerLimit PointwiseEventuallyConstant
  BoundedMeasureApproximationUP BoundedSupportLp.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [bounded_approximation_finite_lp_norm]: the finite
    phi_p(gn) assertion in Federer 2.4.16, p. 90, last paragraph. *)
Lemma bounded_approximation_finite_lp_norm (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f : X -> real_norm_metric_space (scalar_absolute_value_norm R))
    (g : nat -> X -> real_norm_metric_space (scalar_absolute_value_norm R)) :
  (1 <= p)%R -> is_bounded_measure_approximation mu f g -> forall n,
  measure_lp_norm mu (fun y : R => `|y|%R) p (partial_function_total (g n)) < +oo.
Proof.
move=> hp hg n; have [A [hA [hAf [hgz hgM]]]] := bounded_approximation_support hg n.
apply: (@bounded_finite_support_lp_norm R X mu hm p n.+1%:R A (g n) hp _ hA hAf
  (bounded_approximation_measurable hg n) hgz hgM).
by rewrite ltr0n.
Qed.

(** Source for [bounded_approximation_norm_unbounded]: the norms
    approach infinity in Federer 2.4.16, p. 90. This supporting
    unboundedness consequence is all that is needed to establish
    the infinite value of the dual supremum. *)
Lemma bounded_approximation_norm_unbounded (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f : X -> real_norm_metric_space (scalar_absolute_value_norm R))
    (g : nat -> X -> real_norm_metric_space (scalar_absolute_value_norm R)) :
  (1 <= p)%R -> is_measure_measurable_function mu (partial_function_total f) ->
  is_bounded_measure_approximation mu f g ->
  measure_lp_norm mu (fun y : R => `|y|%R) p (partial_function_total f)=+oo ->
  forall r : R, exists n, r%:E < measure_lp_norm mu (fun y : R => `|y|%R) p (partial_function_total (g n)).
Proof.
move=> hp hf hg hinf r.
have hpoint := @pointwise_eventually_equal_limit X _ g f (bounded_approximation_eventually hg).
have hlim : measure_almost_everywhere mu (partial_function_limit_locus
    (fun n => partial_function_total (g n)) (partial_function_total f)).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm)).
  move=> x _; exists (fun n => g n x),(f x); by split=> //; split=> //; exact: hpoint x.
have hfatou := @measure_lp_norm_lower_semicontinuous R X R^o _ (scalar_absolute_value_norm R)
  mu hm p _ _ hp (bounded_approximation_measurable hg) hf hlim.
apply: contrapT=> hn.
have hb n : measure_lp_norm mu (fun y : R => `|y|%R) p (partial_function_total (g n)) <= r%:E.
  rewrite leNgt; apply/negP=> hh; apply: hn; by exists n.
have hl : extended_lower_limit (fun n => measure_lp_norm mu (fun y : R => `|y|%R) p
    (partial_function_total (g n))) <= r%:E.
  apply: (extended_real_supremum_least (extended_lower_limit_laws _))=> b [N hN].
  exact: le_trans (hN N (leqnn N)) (hb N).
have hh := le_trans hfatou hl; by move: hh; rewrite hinf leNgt ltry.
Qed.
