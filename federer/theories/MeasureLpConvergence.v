(** Federer (1969), 2.4.12, p. 87: finite-p norm convergence and its
    implication for convergence in measure. We retain partial functions and
    allow infinite individual norms; Lp membership is a separate predicate. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormedArithmetic
  MeasureUP MeasurableFunctionUP MeasurableNormedFunctionUP MeasurableNormedDifference
  MeasureConvergenceUP MeasureGauge MeasureLpNorm MeasureLpGaugeBound RealPower
  ExtendedPositivePower ExtendedPositivePowerOrder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_lp_distance]: difference seminorm for the
    finite-p convergence assertions of Federer 2.4.12, p. 87. *)
Definition measure_lp_distance (R : realType) (X : choiceType) (V : lmodType R)
    (mu : set X -> \bar R) (N : V -> R) (p : R) (f g : partial_function X V) :=
  measure_lp_norm mu N p (partial_vector_subtract f g).

(** Source for [converges_in_lp_norm]: direct epsilon formulation
    of finite-p convergence in Federer 2.4.12, p. 87. *)
Definition converges_in_lp_norm (R : realType) (X : choiceType) (V : lmodType R)
    (mu : set X -> \bar R) (N : V -> R) (p : R)
    (f : nat -> partial_function X V) (g : partial_function X V) :=
  forall e : R, (0 < e)%R -> exists K, forall n, (K <= n)%N ->
    measure_lp_distance mu N p (f n) g < e%:E.

(** Source for [cauchy_in_lp_norm]: direct finite-p Cauchy
    condition used in Federer 2.4.12, p. 87. *)
Definition cauchy_in_lp_norm (R : realType) (X : choiceType) (V : lmodType R)
    (mu : set X -> \bar R) (N : V -> R) (p : R) (f : nat -> partial_function X V) :=
  forall e : R, (0 < e)%R -> exists K, forall n m,
    (K <= n)%N -> (K <= m)%N -> measure_lp_distance mu N p (f n) (f m) < e%:E.

(** Source for [lp_norm_small_gauge]: supporting quantitative
    epsilon choice for Federer 2.4.12, p. 87. Applying the
    already proved gauge bound and the inverse positive power turns
    a sufficiently small Lp norm into a small measure gauge. *)
Lemma lp_norm_small_gauge (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p e : R)
    (f : partial_function X (real_norm_metric_space hN)) :
  (1 <= p)%R -> (0 < e)%R -> is_measure_measurable_function mu f ->
  measure_lp_norm mu N p f < (real_power e (p/(p+1))^-1)%:E -> measure_gauge mu N f < e%:E.
Proof.
move=> hp he hf hn.
have hp0 : (0 < p)%R := lt_le_trans ltr01 hp.
have hr : (0 < p/(p+1))%R := divr_gt0 hp0 (addr_gt0 hp0 ltr01).
have he0 : 0 <= e%:E by rewrite lee_fin; exact: ltW he.
have hd0 : 0 <= (real_power e (p/(p+1))^-1)%:E by rewrite lee_fin real_power_nonnegative.
have hnn := @measure_lp_norm_nonnegative R X V N hN mu p f hm hp hf.
have hb := @measure_gauge_le_lp_norm_power R X V N hN mu hm p f hp hf.
apply: le_lt_trans hb _.
have hpow := @extended_positive_power_strict_order R (measure_lp_norm mu N p f)
  (real_power e (p/(p+1))^-1)%:E (p/(p+1))%R hnn hd0 hr.
have ht : extended_positive_power (measure_lp_norm mu N p f) (p/(p+1))%R <
    extended_positive_power (extended_positive_power e%:E (p/(p+1))^-1) (p/(p+1))%R.
  by rewrite hpow.
by rewrite extended_positive_power_inverse_cancel in ht.
Qed.

(** Source for [lp_norm_cauchy_in_measure]: direct first step of the
    finite-p completeness argument in Federer 2.4.12, p. 87 *)
Lemma lp_norm_cauchy_in_measure (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f : nat -> partial_function X (real_norm_metric_space hN)) :
  (1 <= p)%R -> (forall n, is_measurable_normed_function mu (f n)) ->
  cauchy_in_lp_norm mu N p f -> cauchy_in_measure mu N f.
Proof.
move=> hp hf hc e he.
have hd : (0 < real_power e (p/(p+1))^-1)%R := real_power_strictly_positive _ he.
have [K hK] := hc _ hd; exists K=> n m hn hm'.
exact (@lp_norm_small_gauge R X V N hN mu hm p e _ hp he
  (@measurable_normed_function_subtract R X V N hN mu hm (f n) (f m) (hf n) (hf m)).1
  (hK n m hn hm')).
Qed.
