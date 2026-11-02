(** Federer (1969), 2.4.15, proof p. 89: summability of the powered norm of
    f+g, before the Holder estimate. These supporting estimates use abstract
    norm laws and the project's integral comparison and addition theorems. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ExtendedRealPartial PartialFunctionUP PartialNormedArithmetic
  PartialNormPower RealPower RealPowerSumBound MeasurableNormPower PartialExtendedArithmetic
  PartialExtendedOrderLoci MeasureUpperIntegralScale DominatedErrorGraphs
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasurableNormedFunctionUP MeasurableNormedArithmetic
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralAddition MeasureIntegralScaleLaw
  MeasureIntegralComparison MeasureNonnegativeIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_norm_sum_power_majorant]: supporting
    dominating function 2^p(|f|^p+|g|^p) in Federer
    2.4.15, first proof display p. 89. It
    retains the common domain of the two functions. *)
Definition partial_norm_sum_power_majorant (R : realType) (X Y : Type)
    (N : Y -> R) (p : R) (f g : partial_function X Y) :=
  partial_extended_function_scale (real_power 2%R p)
    (partial_extended_function_add (partial_norm_power N p f) (partial_norm_power N p g)).

(** Source for [measure_norm_sum_power_finite_integral]: the summability
    inference in the opening proof of Federer 2.4.15, p. 89 The conclusion
    provides a finite powered integral and the explicit preliminary bound;
    completeness of the normed target is unnecessary for this estimate. *)
Lemma measure_norm_sum_power_finite_integral (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p a b : R)
    (f g : partial_function X (real_norm_metric_space hN)) :
  (0 < p)%R -> is_measurable_normed_function mu f -> is_measurable_normed_function mu g ->
  is_measure_integral mu (partial_norm_power N p f) a%:E ->
  is_measure_integral mu (partial_norm_power N p g) b%:E ->
  exists c : R, (0 <= c)%R /\
    is_measure_integral mu (partial_norm_power N p (partial_vector_add f g)) c%:E /\
    (c <= real_power 2%R p * (a+b))%R.
Proof.
move=> hp hf hg hfi hgi.
have hadd : extended_add a%:E b%:E = Some (a+b)%:E by rewrite /extended_add /=.
have hsum := @measure_integral_add R X mu hm _ _ _ _ _ hfi hgi hadd.
have htwo : (0 < (2 : R))%R by rewrite ltr0n.
have hcoef := @real_power_strictly_positive R 2%R p htwo.
have hmajor := @measure_integral_positive_scale R X mu hm (real_power 2%R p) _ (a+b)%:E hcoef hsum.
rewrite -EFinM in hmajor.
have hfg := @measurable_normed_function_add R X V N hN mu hm f g hf hg.
have hmeas := @measurable_norm_positive_power R X V N hN mu hm p _ hp hfg.1.
have hnonneg := @partial_norm_power_almost_nonnegative R X (real_norm_metric_space hN)
  mu hm N p (partial_vector_add f g) (measurable_function_domain hfg.1).
have [hi hpos] := @nonnegative_measurable_function_integral R X mu hm _ hmeas hnonneg.
have horder : measure_almost_everywhere mu (partial_extended_le_locus
    (partial_norm_power N p (partial_vector_add f g)) (partial_norm_sum_power_majorant N p f g)).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
    (@measure_almost_everywhere_and R X mu hm _ _ (measurable_function_domain hf.1) (measurable_function_domain hg.1))).
  move=> x [[u hu] [v hv]].
  exists (real_power (N (u+v)%R) p)%:E,
    (real_power 2%R p*(real_power (N u) p+real_power (N v) p))%:E; split.
  - exists (u+v)%R; split=> //; apply/partial_vector_add_graph; exists u,v; by split=> //; split.
  - split.
    + exists (real_power (N u) p+real_power (N v) p)%:E; split; last by rewrite EFinM.
      apply: partial_finite_sum_graph; [exists u|exists v]; by split.
    + rewrite lee_fin; exact (@norm_sum_power_bound R V N hN p u v hp).
have hbnd := @measure_integral_monotone R X mu hm _ _ _ _ hi hmajor horder.
pose c := measure_lower_integral mu (partial_norm_power N p (partial_vector_add f g)).
change (is_true (0 <= c)) in hpos.
change (is_true (c <= (real_power 2%R p*(a+b))%:E)) in hbnd.
have hfin : c \is a fin_num.
  rewrite (ge0_fin_numE hpos); exact: le_lt_trans hbnd (ltry _).
exists (fine c); split; first by move: hpos; rewrite -(fineK hfin) lee_fin.
split; first by rewrite fineK.
by move: hbnd; rewrite -(fineK hfin) lee_fin.
Qed.
