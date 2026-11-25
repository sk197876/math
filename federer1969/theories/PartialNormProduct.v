(** Federer (1969), 2.4.14, p. 88: the absolute product in the proof of
    Holder's inequality. This supporting norm-product formulation also
    applies to the normed-vector functions in Minkowski's inequality,
    Federer 2.4.15, p. 89. Common partial domains are retained. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ExtendedRealOrderTopology PartialFunctionUP
  PartialDensityProduct PartialNormPower RealPower MeasurableNormPower MeasurableDensityProduct
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP PartialExtendedOrderLoci.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_norm_product]: supporting product of
    norms in the Holder bound of Federer 2.4.14,
    p. 88. In the scalar case it is |fg|.
    It uses the existing product operation and first norm powers. *)
Definition partial_norm_product (R : realType) (X Y Z : Type)
    (N : Y -> R) (M : Z -> R) (f : partial_function X Y) (g : partial_function X Z) :=
  partial_density_product (partial_norm_power N 1%R f) (partial_norm_power M 1%R g).

(** Source for [partial_norm_product_graph]: supporting graph
    formula for the absolute-product integrand of Federer
    2.4.14, p. 88. Both original values must exist. *)
Lemma partial_norm_product_graph (R : realType) (X : Type)
    (V W : lmodType R) (N : V -> R) (M : W -> R)
    (hN : is_real_norm N) (hM : is_real_norm M)
    (f : partial_function X V) (g : partial_function X W) x z :
  partial_function_graph (partial_norm_product N M f g) x z <->
  exists a b, partial_function_graph f x a /\ partial_function_graph g x b /\ (N a*M b)%:E=z.
Proof.
rewrite /partial_norm_product partial_density_product_graph; split.
- move=> [u [v [[a [ha hau]] [[b [hb hbv]] huv]]]].
  exists a,b; split=> //; split=> //.
  rewrite (@real_power_one_exponent R (N a) (real_seminorm_nonnegative hN.1 a)) in hau.
  rewrite (@real_power_one_exponent R (M b) (real_seminorm_nonnegative hM.1 b)) in hbv.
  by rewrite EFinM hau hbv.
- move=> [a [b [ha [hb he]]]]; exists (N a)%:E,(M b)%:E; split.
  + exists a; split=> //; by rewrite (@real_power_one_exponent R (N a) (real_seminorm_nonnegative hN.1 a)).
  + split.
    * exists b; split=> //; by rewrite (@real_power_one_exponent R (M b) (real_seminorm_nonnegative hM.1 b)).
    * by rewrite -EFinM.
Qed.

(** Source for [measurable_norm_product]: supporting measurability
    of the absolute product in Federer 2.4.14, p. 88,
    before its integral is bounded. No finiteness of either
    norm integral is needed for this step. *)
Lemma measurable_norm_product (R : realType) (X : choiceType)
    (V W : lmodType R) (N : V -> R) (M : W -> R)
    (hN : is_real_norm N) (hM : is_real_norm M)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space hN))
    (g : partial_function X (real_norm_metric_space hM)) :
  is_measure_measurable_function mu f -> is_measure_measurable_function mu g ->
  is_measure_measurable_function mu (partial_norm_product N M f g).
Proof.
move=> hf hg; apply: (@measurable_density_product R X mu hm).
- exact (@measurable_norm_positive_power R X V N hN mu hm 1%R f ltr01 hf).
- exact (@measurable_norm_positive_power R X W M hM mu hm 1%R g ltr01 hg).
Qed.

(** Source for [norm_product_nonnegative_almost]: supporting
    nonnegative integrability premise for the Holder proof in
    Federer 2.4.14, p. 88. Only conull domains
    are required, since the two factors are norms. *)
Lemma norm_product_nonnegative_almost (R : realType) (X : choiceType)
    (V W : lmodType R) (N : V -> R) (M : W -> R)
    (hN : is_real_norm N) (hM : is_real_norm M)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X V) (g : partial_function X W) :
  measure_almost_everywhere mu (partial_function_domain f) ->
  measure_almost_everywhere mu (partial_function_domain g) ->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus (partial_norm_product N M f g)).
Proof.
move=> hf hg; apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
  (@measure_almost_everywhere_and R X mu hm _ _ hf hg)).
move=> x [[a ha] [b hb]]; exists (N a*M b)%:E; split.
- apply/(@partial_norm_product_graph R X V W N M hN hM f g x _).
  exists a,b; by split=> //; split.
- rewrite lee_fin; exact: mulr_ge0 (real_seminorm_nonnegative hN.1 a) (real_seminorm_nonnegative hM.1 b).
Qed.
