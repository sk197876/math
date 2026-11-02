(** Federer (1969), 2.6.4, pp. 118–119: the product of two summable
    functions is summable, and its integral is the product of their
    integrals. The proof first integrates |f(x)||g(y)|, uses absolute
    domination, then applies Fubini. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialExtendedOrderLoci PartialAbsolutePartsGraph
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralUniqueness MeasureAbsoluteSummability
  SummableRealFunctionUP SummableRealArithmetic SummableRealNormed
  ProductMeasure ProductFunctionMeasurability ScalarCountableEmbedding NonnegativeSeparatedIntegral
  SeparatedRepeatedIntegral ProductSummableFubini.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [separated_product_summable]: well-definedness
    of the first map in Federer 2.6.4, p. 118,
    including arbitrary ambient measures and vanishing factors. *)
Theorem separated_product_summable (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (f : X -> R) (g : Y -> R) :
  summable_real_functions alpha f -> summable_real_functions beta g ->
  summable_real_functions (product_measure ha hb) (fun p : X*Y => f p.1*g p.2).
Proof.
move=> hf hg.
have [a hi] := summable_real_absolute ha hf.
have [b hj] := summable_real_absolute hb hg.
have hH := @nonnegative_separated_integral R X Y alpha beta ha hb
  (fun x => `|f x|) (fun y => `|g y|) a b (fun x => normr_ge0 _) (fun y => normr_ge0 _) hi hj.
have hm := product_measure_is_measure ha hb.
have hmeas := scalar_real_integrand_measurable hm
  (@product_measurable_scalar_function R X Y alpha beta ha hb f g
    (summable_real_function_in_normed_collection ha hf).1
    (summable_real_function_in_normed_collection hb hg).1).
refine (proj1 (@measure_dominated_summable R (Choice.clone (X*Y)%type _)
  (product_measure ha hb) hm
  (real_total_integrand (fun p : X*Y => f p.1*g p.2))
  (real_total_integrand (fun p : X*Y => `|f p.1|*`|g p.2|))
  hmeas (ex_intro _ (a*b) hH) _)).
apply: (@measure_almost_everywhere_mono R (Choice.clone (X*Y)%type _) _ hm setT _ _
  (measure_almost_everywhere_true hm)).
move=> [x y] _.
exists (`|f x*g y|)%:E,(`|f x|*`|g y|)%:E; split.
- exists (f x*g y)%:E; split; first by apply/real_total_integrand_graph.
  by rewrite abse_EFin.
- split; first by apply/real_total_integrand_graph.
  by rewrite normrM.
Qed.

(** Source for [separated_product_integral]: the pure-tensor
    integral identity in the commutative diagram of Federer
    2.6.4, p. 119. This is an actual product integral,
    not merely a formal repeated-integral computation. *)
Theorem separated_product_integral (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta)
    (f : X -> R) (g : Y -> R) (a b : R) :
  is_measure_integral alpha (real_total_integrand f) a%:E ->
  is_measure_integral beta (real_total_integrand g) b%:E ->
  is_measure_integral (product_measure ha hb)
    (real_total_integrand (fun p : X*Y => f p.1*g p.2)) (a*b)%:E.
Proof.
move=> hf hg.
have [c hc] := separated_product_summable ha hb (ex_intro _ a hf) (ex_intro _ b hg).
have hi := (@product_summable_fubini R X Y alpha beta ha hb _ c hc).1.
have hj := @separated_repeated_integral R X Y alpha beta ha hb f g a b hf hg.
have he := measure_integral_unique hi hj; by rewrite -he.
Qed.
