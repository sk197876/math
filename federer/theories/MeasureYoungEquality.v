(** Federer (1969), 2.4.14, p. 88: equality in the normalised
    arithmetic-geometric integral estimate. This is an intermediate equality
    criterion; the sign condition for the original signed integral is
    separate. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormPower RealPower
  PartialNormProduct MeasureYoungNormProduct YoungNormSumGraph YoungPowerInequality
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasureIntegralUP
  MeasureIntegralOrderEquality MeasureIntegralAlmostEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_young_unit_equality_forces_powers]: the necessity of
    equal normalised powers in Federer 2.4.14, proof p. 88 Integrating the
    nonnegative Young deficit proves the almost-everywhere conclusion,
    without assuming it. *)
Lemma measure_young_unit_equality_forces_powers (R : realType) (X : choiceType)
    (V W : lmodType R) (N : V -> R) (M : W -> R)
    (hN : is_real_norm N) (hM : is_real_norm M)
    (mu : set X -> \bar R) (hm : is_measure mu) (p q : R)
    (f : partial_function X (real_norm_metric_space hN))
    (g : partial_function X (real_norm_metric_space hM)) :
  (0 < p)%R -> (0 < q)%R -> (p^-1 + q^-1 = 1)%R ->
  is_measure_measurable_function mu f -> is_measure_measurable_function mu g ->
  is_measure_integral mu (partial_norm_power N p f) 1 ->
  is_measure_integral mu (partial_norm_power M q g) 1 ->
  is_measure_integral mu (partial_norm_product N M f g) 1 ->
  measure_almost_equal mu (partial_norm_power N p f) (partial_norm_power M q g).
Proof.
move=> hp hq hpq hf hg hfi hgi hprod.
have hsum := @measure_young_norm_sum_unit_integral R X _ _ N M p q mu hm f g hp hq hpq hfi hgi.
have hdom := @measure_almost_everywhere_and R X mu hm _ _
  (measurable_function_domain hf) (measurable_function_domain hg).
have horder : measure_almost_everywhere mu [set x | exists a b : R,
    partial_function_graph (partial_norm_product N M f g) x a%:E /\
    partial_function_graph (partial_young_norm_sum N M p q f g) x b%:E /\ (a <= b)%R].
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hdom).
  move=> x [[a ha] [b hb]].
  exists (N a*M b)%R,(p^-1*real_power (N a) p+q^-1*real_power (M b) q)%R; split.
  - apply/(@partial_norm_product_graph R X V W N M hN hM); exists a,b; by split=> //; split.
  - split; first exact (@partial_young_norm_sum_graph R X _ _ N M p q f g x a b ha hb).
    exact (@young_power_inequality R p q (N a) (M b) hp hq hpq
      (real_seminorm_nonnegative hN.1 a) (real_seminorm_nonnegative hM.1 b)).
have he := @measure_integral_order_equality R X mu hm _ _ 1%R hprod hsum horder.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
  (@measure_almost_everywhere_and R X mu hm _ _ hdom he)).
move=> x [[[a ha] [b hb]] [z [hzprod hzsum]]].
have hpgraph : partial_function_graph (partial_norm_product N M f g) x (N a*M b)%:E.
  apply/(@partial_norm_product_graph R X V W N M hN hM); exists a,b; by split=> //; split.
have hsgraph := @partial_young_norm_sum_graph R X _ _ N M p q f g x a b ha hb.
have heE : (N a*M b)%:E = (p^-1*real_power (N a) p+q^-1*real_power (M b) q)%:E.
  rewrite (partial_function_single_valued hpgraph hzprod).
  exact: esym (partial_function_single_valued hsgraph hzsum).
have heR := EFin_inj heE.
have hpow := (@young_power_equality R p q (N a) (M b) hp hq hpq
  (real_seminorm_nonnegative hN.1 a) (real_seminorm_nonnegative hM.1 b)).1 heR.
exists (real_power (N a) p)%:E; split; first by exists a; split.
exists b; split=> //; by rewrite hpow.
Qed.

(** Source for [measure_young_equal_powers_unit_integral]: the sufficiency
    of equal normalised powers in Federer 2.4.14, p. 88 Pointwise equality
    in Young's inequality identifies the product with the weighted sum on a
    conull set. *)
Lemma measure_young_equal_powers_unit_integral (R : realType) (X : choiceType)
    (V W : lmodType R) (N : V -> R) (M : W -> R)
    (hN : is_real_norm N) (hM : is_real_norm M)
    (mu : set X -> \bar R) (hm : is_measure mu) (p q : R)
    (f : partial_function X (real_norm_metric_space hN))
    (g : partial_function X (real_norm_metric_space hM)) :
  (0 < p)%R -> (0 < q)%R -> (p^-1 + q^-1 = 1)%R ->
  is_measure_integral mu (partial_norm_power N p f) 1 ->
  is_measure_integral mu (partial_norm_power M q g) 1 ->
  measure_almost_equal mu (partial_norm_power N p f) (partial_norm_power M q g) ->
  is_measure_integral mu (partial_norm_product N M f g) 1.
Proof.
move=> hp hq hpq hfi hgi he.
have hsum := @measure_young_norm_sum_unit_integral R X _ _ N M p q mu hm f g hp hq hpq hfi hgi.
apply: (@measure_integral_almost_equal R X mu hm _ _ 1 hsum).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ he).
move=> x [z [[a [ha haz]] [b [hb hbz]]]].
have heE : (real_power (N a) p)%:E = (real_power (M b) q)%:E by rewrite haz hbz.
have hpow := EFin_inj heE.
have hnum := (@young_power_equality R p q (N a) (M b) hp hq hpq
  (real_seminorm_nonnegative hN.1 a) (real_seminorm_nonnegative hM.1 b)).2 hpow.
exists (N a*M b)%:E; split.
- rewrite hnum; exact (@partial_young_norm_sum_graph R X _ _ N M p q f g x a b ha hb).
- apply/(@partial_norm_product_graph R X V W N M hN hM); exists a,b; by split=> //; split.
Qed.
