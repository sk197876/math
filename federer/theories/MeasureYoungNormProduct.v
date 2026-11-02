(** Federer (1969), 2.4.14, p. 88: integrate the arithmetic-geometric
    comparison before normalisation. The supporting norm-product formulation
    also supplies the integrability needed for Minkowski's proof in 2.4.15,
    p. 89. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ExtendedRealOrderTopology ExtendedRealPartial
  PartialFunctionUP PartialNormPower RealPower PartialNormProduct PartialExtendedArithmetic YoungPowerInequality
  MeasureUpperIntegralScale DominatedErrorGraphs PartialExtendedOrderLoci
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasureIntegralUP MeasureIntegralBounds MeasureNonnegativeIntegral
  MeasureIntegralScaleLaw MeasureIntegralAddition MeasureIntegralComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_young_norm_sum]: supporting pointwise
    weighted sum in the proof of Federer 2.4.14, p. 88,
    before normalising the two functions. The domain is their
    common domain; the two finite powered norms have a defined sum. *)
Definition partial_young_norm_sum (R : realType) (X Y Z : Type)
    (N : Y -> R) (M : Z -> R) (p q : R)
    (f : partial_function X Y) (g : partial_function X Z) :=
  partial_extended_function_add
    (partial_extended_function_scale p^-1 (partial_norm_power N p f))
    (partial_extended_function_scale q^-1 (partial_norm_power M q g)).

(** Source for [norm_product_young_order]: supporting pointwise
    arithmetic-geometric comparison in Federer 2.4.14, p. 88 All graph
    values are explicit, so no values are assigned on exceptional domains. *)
Lemma norm_product_young_order (R : realType) (X : Type)
    (V W : lmodType R) (N : V -> R) (M : W -> R)
    (hN : is_real_norm N) (hM : is_real_norm M) (p q : R)
    (f : partial_function X V) (g : partial_function X W) :
  (0 < p)%R -> (0 < q)%R -> (p^-1 + q^-1 = 1)%R ->
  partial_function_domain f `&` partial_function_domain g `<=`
    partial_extended_le_locus (partial_norm_product N M f g) (partial_young_norm_sum N M p q f g).
Proof.
move=> hp hq hpq x [[a ha] [b hb]].
have hleft : partial_function_graph (partial_extended_function_scale p^-1 (partial_norm_power N p f))
    x (p^-1*real_power (N a) p)%:E.
  exists (real_power (N a) p)%:E; split; first by exists a; split.
  by rewrite EFinM.
have hright : partial_function_graph (partial_extended_function_scale q^-1 (partial_norm_power M q g))
    x (q^-1*real_power (M b) q)%:E.
  exists (real_power (M b) q)%:E; split; first by exists b; split.
  by rewrite EFinM.
exists (N a*M b)%:E,(p^-1*real_power (N a) p+q^-1*real_power (M b) q)%:E; split.
- apply/(@partial_norm_product_graph R X V W N M hN hM f g x _).
  exists a,b; by split=> //; split.
- split.
  + exact (@partial_finite_sum_graph R X _ _ x _ _ hleft hright).
  + rewrite lee_fin.
    exact (@young_power_inequality R p q (N a) (M b) hp hq hpq
      (real_seminorm_nonnegative hN.1 a) (real_seminorm_nonnegative hM.1 b)).
Qed.

(** Source for [measure_norm_product_young_bound]: supporting integral
    arithmetic-geometric estimate in Federer 2.4.14, p. 88 Finite
    powered-norm integrals imply summability of the norm product, before any
    division by a norm is performed. *)
Lemma measure_norm_product_young_bound (R : realType) (X : choiceType)
    (V W : lmodType R) (N : V -> R) (M : W -> R)
    (hN : is_real_norm N) (hM : is_real_norm M)
    (mu : set X -> \bar R) (hm : is_measure mu) (p q a b : R)
    (f : partial_function X (real_norm_metric_space hN))
    (g : partial_function X (real_norm_metric_space hM)) :
  (0 < p)%R -> (0 < q)%R -> (p^-1 + q^-1 = 1)%R ->
  is_measure_measurable_function mu f -> is_measure_measurable_function mu g ->
  is_measure_integral mu (partial_norm_power N p f) a%:E ->
  is_measure_integral mu (partial_norm_power M q g) b%:E ->
  exists c : R, (0 <= c)%R /\ is_measure_integral mu (partial_norm_product N M f g) c%:E /\
    (c <= p^-1*a+q^-1*b)%R.
Proof.
move=> hp hq hpq hf hg hfi hgi.
have hpi : (0 < p^-1)%R by rewrite invr_gt0.
have hqi : (0 < q^-1)%R by rewrite invr_gt0.
have hleft := @measure_integral_positive_scale R X mu hm p^-1 _ a%:E hpi hfi.
have hright := @measure_integral_positive_scale R X mu hm q^-1 _ b%:E hqi hgi.
rewrite -EFinM in hleft hright.
have hadd : extended_add (p^-1*a)%:E (q^-1*b)%:E = Some (p^-1*a+q^-1*b)%:E.
  by rewrite /extended_add /=.
have hsum := @measure_integral_add R X mu hm _ _ _ _ _ hleft hright hadd.
have hmeas := @measurable_norm_product R X V W N M hN hM mu hm f g hf hg.
have hnonneg := @norm_product_nonnegative_almost R X V W N M hN hM mu hm f g
  (measurable_function_domain hf) (measurable_function_domain hg).
have [hi hpos] := @nonnegative_measurable_function_integral R X mu hm _ hmeas hnonneg.
have horder : measure_almost_everywhere mu (partial_extended_le_locus
    (partial_norm_product N M f g) (partial_young_norm_sum N M p q f g)).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
    (@measure_almost_everywhere_and R X mu hm _ _
      (measurable_function_domain hf) (measurable_function_domain hg))).
  exact (@norm_product_young_order R X V W N M hN hM p q f g hp hq hpq).
have hbound := @measure_integral_monotone R X mu hm _ _ _ _ hi hsum horder.
pose c := measure_lower_integral mu (partial_norm_product N M f g).
change (is_true (0 <= c)) in hpos.
change (is_true (c <= (p^-1*a+q^-1*b)%:E)) in hbound.
have hfin : c \is a fin_num.
  rewrite (ge0_fin_numE hpos); exact: le_lt_trans hbound (ltry _).
exists (fine c); split.
- move: hpos; by rewrite -(fineK hfin) lee_fin.
- split; first by rewrite fineK.
  move: hbound; by rewrite -(fineK hfin) lee_fin.
Qed.
