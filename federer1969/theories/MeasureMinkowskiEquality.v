(** Federer (1969), 2.4.15, p. 89: the complete general normed-space
    equality criterion for Minkowski. The inner-product specialisation is a
    separate assertion. All zero-norm cases and partial conull domains are
    retained in the general criterion below. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormedArithmetic
  MinkowskiEqualityUP MeasureMinkowskiPositiveEquality MeasureMinkowskiZeroEquality MeasureMinkowskiEqualitySufficient
  MeasureLpNorm MeasureLpMembershipUP MeasureUP MeasurableFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [minkowski_equality_condition_necessary]: the necessity
    direction of the general equality criterion in Federer 2.4.15, p. 89 The
    positive-norm case uses the two Holder equalities; either zero norm
    gives coefficients zero and one without division. *)
Theorem minkowski_equality_condition_necessary (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f g : partial_function X (real_norm_metric_space hN)) :
  (1 < p)%R -> is_measure_lp_function mu p f -> is_measure_lp_function mu p g ->
  measure_lp_norm mu N p (partial_vector_add f g) = measure_lp_norm mu N p f + measure_lp_norm mu N p g ->
  is_minkowski_equality_condition N mu f g.
Proof.
move=> hp hf hg he.
have hfnn := @measure_lp_norm_nonnegative R X V N hN mu p f hm hf.1 hf.2.1.1.
have hgnn := @measure_lp_norm_nonnegative R X V N hN mu p g hm hg.1 hg.2.1.1.
have hffin : measure_lp_norm mu N p f \is a fin_num.
  rewrite (ge0_fin_numE hfnn); exact hf.2.2.1.
have hgfin : measure_lp_norm mu N p g \is a fin_num.
  rewrite (ge0_fin_numE hgnn); exact hg.2.2.1.
pose a := fine (measure_lp_norm mu N p f).
pose b := fine (measure_lp_norm mu N p g).
have hfa : measure_lp_norm mu N p f = a%:E by rewrite fineK.
have hgb : measure_lp_norm mu N p g = b%:E by rewrite fineK.
have ha0 : (0 <= a)%R by move: hfnn; rewrite hfa lee_fin.
have hb0 : (0 <= b)%R by move: hgnn; rewrite hgb lee_fin.
have [ha|ha] := eqVneq a 0%R.
- have hz : measure_lp_norm mu N p f = 0 by rewrite hfa ha.
  exact (@minkowski_zero_left_equality_condition R X V N hN mu hm p f g hf.1 hf.2.1.1 hz
    (measurable_function_domain hg.2.1.1)).
have [hb|hb] := eqVneq b 0%R.
- have hz : measure_lp_norm mu N p g = 0 by rewrite hgb hb.
  exact (@minkowski_zero_right_equality_condition R X V N hN mu hm p f g hg.1
    (measurable_function_domain hf.2.1.1) hg.2.1.1 hz).
have hapos : (0 < a)%R by rewrite lt_neqAle eq_sym ha ha0.
have hbpos : (0 < b)%R by rewrite lt_neqAle eq_sym hb hb0.
have hsum : measure_lp_norm mu N p (partial_vector_add f g) = (a+b)%:E.
  by rewrite he hfa hgb -EFinD.
exact (@minkowski_positive_norm_equality_necessary R X V N hN mu hm p a b f g hp hapos hbpos hf.2.1 hg.2.1 hfa hgb hsum).
Qed.

(** Source for [minkowski_equality_iff]: the complete general equality
    condition in Federer 2.4.15, p. 89 A single nonnegative pair of
    coefficients summing to one gives the two printed norm identities almost
    everywhere. *)
Theorem minkowski_equality_iff (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f g : partial_function X (real_norm_metric_space hN)) :
  (1 < p)%R -> is_measure_lp_function mu p f -> is_measure_lp_function mu p g ->
  (measure_lp_norm mu N p (partial_vector_add f g) = measure_lp_norm mu N p f + measure_lp_norm mu N p g <->
   is_minkowski_equality_condition N mu f g).
Proof.
move=> hp hf hg; split.
- exact (@minkowski_equality_condition_necessary R X V N hN mu hm p f g hp hf hg).
- exact (@minkowski_equality_condition_sufficient R X V N hN mu hm p f g hf hg).
Qed.
