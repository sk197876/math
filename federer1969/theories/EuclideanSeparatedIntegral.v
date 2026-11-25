(** Federer (1969), 3.2.13, p. 250: Cartesian Fubini for
    the product Gaussian integral, through the Lebesgue block law
    2.6.5, p. 120, and the separated integral 2.6.4, p. 119. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates
  EuclideanBlockMeasure EuclideanLebesgueDimensions PartialFunctionUP PartialFunctionPrecomposition
  MeasureUP MeasureIntegralUP MeasureIntegralGraphEquivalence SummableRealFunctionUP
  SeparatedProductIntegral InjectivePushforwardIntegral ProductMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_separated_integral]: the actual finite
    integral of a product of functions of separate Euclidean
    coordinate blocks is the product of their integrals,
    Federer 2.6.4, p. 119, used in 3.2.13, p. 250. *)
Lemma euclidean_separated_integral (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->R)
    (g:inner_metric_space (@euclidean_inner_productP R n)->R) (a b:R):
  is_measure_integral (@euclidean_lebesgue_measure R m) (real_total_integrand f) a%:E ->
  is_measure_integral (@euclidean_lebesgue_measure R n) (real_total_integrand g) b%:E ->
  is_measure_integral (@euclidean_lebesgue_measure R (m+n))
    (real_total_integrand (fun x=>f (euclidean_block_split x).1*g (euclidean_block_split x).2)) (a*b)%:E.
Proof.
move=>hf hg.
have hProduct:=separated_product_integral (euclidean_lebesgue_is_measure R m)
  (euclidean_lebesgue_is_measure R n) hf hg.
have hInj:injective (@euclidean_block_split R m n):=can_inj (@euclidean_block_splitK R m n).
have hPush:=@injective_pushforward_integral_iff R
  [the choiceType of inner_metric_space (@euclidean_inner_productP R (m+n))]
  [the choiceType of (inner_metric_space (@euclidean_inner_productP R m)*
    inner_metric_space (@euclidean_inner_productP R n))%type]
  (@euclidean_lebesgue_measure R (m+n)) (euclidean_lebesgue_is_measure R (m+n))
  (@euclidean_block_split R m n) (real_total_integrand (fun p=>f p.1*g p.2)) hInj (a*b)%:E.
rewrite euclidean_block_measure in hPush.
apply:(measure_integral_graph_equivalent _ (hPush.2 hProduct))=>x z.
by [].
Qed.
