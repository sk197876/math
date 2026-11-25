(** Federer (1969), 2.6.2(4), pp. 115, 117: exchange the factors to obtain
    the other order of integration. These supporting laws retain the exact
    partial domains and the countably measurable nonzero locus. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionPrecomposition
  MeasureUP MeasureAlmostUP MeasurableFunctionUP CountablyMeasurableUP MeasureIntegralUP
  MeasurePushforward PushforwardIntegral ProductMeasure ProductMeasureTranspose ProductTransposeMeasurability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_product_transpose]: supporting exchange
    of the arguments of the partial integrand in Federer
    2.6.2(4), p. 115. Undefined values remain undefined. *)
Definition partial_product_transpose (X Y Z : Type) (f : partial_function (X * Y) Z) :=
  partial_function_precompose (fun p : Y * X => (p.2,p.1)) f.

(** Source for [product_measurable_function_transpose]: supporting
    measurability under the symmetry of Federer 2.6.2(4),
    pp. 115, 117. Transpose the domain and every open preimage. *)
Lemma product_measurable_function_transpose (R : realType) (X Y : choiceType)
    (Z : topologicalType) (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (f : partial_function (X * Y) Z) :
  is_measure_measurable_function (product_measure ha hb) f ->
  is_measure_measurable_function (product_measure hb ha) (partial_product_transpose f).
Proof.
move=> hf; constructor.
- change (product_measure hb ha (product_transpose (~` partial_function_domain f)) = 0).
  rewrite product_measure_transpose; exact: measurable_function_domain hf.
- move=> U hU; change (measure_measurable (product_measure hb ha)
    (product_transpose (partial_function_preimage f U))).
  exact (@product_measurable_transpose R X Y alpha beta ha hb _ (measurable_function_open_preimage hf hU)).
Qed.

(** Source for [product_countably_measurable_function_transpose]:
    supporting preservation of the nonzero-locus hypothesis in
    Federer 2.6.2(4), p. 115, under exchange of factors. *)
Lemma product_countably_measurable_function_transpose (R : realType) (X Y : choiceType)
    (Z : topologicalType) (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (zero : Z) (f : partial_function (X * Y) Z) :
  is_countably_measure_measurable_function (product_measure ha hb) zero f ->
  is_countably_measure_measurable_function (product_measure hb ha) zero (partial_product_transpose f).
Proof.
move=> hf; constructor.
- exact (@product_measurable_function_transpose R X Y Z alpha beta ha hb f (countably_measurable_function_measurable hf)).
- change (measure_countably_measurable (product_measure hb ha)
    (product_transpose (partial_function_nonzero_locus zero f))).
  exact (@product_countably_measurable_transpose R X Y alpha beta ha hb _ (countably_measurable_function_locus hf)).
Qed.

(** Source for [product_integral_transpose]: supporting integral
    invariance under the factor exchange in Federer 2.6.2(4),
    p. 115, using the already proved image-measure formula
    2.4.18(1), p. 90. Infinite integral values are permitted. *)
Lemma product_integral_transpose (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta)
    (f : partial_function (X * Y) (extended_real_line R)) a :
  is_measure_integral (product_measure ha hb) f a ->
  is_measure_integral (product_measure hb ha) (partial_product_transpose f) a.
Proof.
move=> hf.
have he : measure_pushforward (fun p : Y * X => (p.2,p.1)) (product_measure hb ha) = product_measure ha hb.
  apply: funext=> S; exact (@product_measure_transpose R X Y alpha beta ha hb S).
have hm := @product_measurable_function_transpose R X Y (extended_real_line R) alpha beta ha hb f hf.1.
apply: (@measure_pushforward_integral_iff R (Y * X)%type (X * Y)%type
  (product_measure hb ha) (product_measure_is_measure hb ha) (fun p => (p.2,p.1)) f hm a).2.
by rewrite he.
Qed.
