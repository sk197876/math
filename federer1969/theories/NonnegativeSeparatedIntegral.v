(** Federer (1969), 2.6.4, pp. 118–119: nonnegative factor case of the
    product-integral identity. The proof uses the actual nonnegative
    integral and Fubini, retaining countable measurability only for the
    nonzero loci of the factors. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialExtendedOrderLoci
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralUniqueness MeasureNonnegativeIntegral
  SummableRealFunctionUP TotalLoneSummability TotalScalarLpUP
  CountablyMeasurableUP ProductMeasure ProductFunctionFubini ProductFunctionCountability
  ScalarCountableEmbedding SeparatedRepeatedIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [nonnegative_separated_integral]: supporting
    nonnegative product case of Federer 2.6.4, pp. 118–119.
    Finite factor integrals force the actual product integral to
    be their finite product, without ambient sigma-finiteness. *)
Theorem nonnegative_separated_integral (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta)
    (f : X -> R) (g : Y -> R) (a b : R) :
  (forall x, 0 <= f x) -> (forall y, 0 <= g y) ->
  is_measure_integral alpha (real_total_integrand f) a%:E ->
  is_measure_integral beta (real_total_integrand g) b%:E ->
  is_measure_integral (product_measure ha hb)
    (real_total_integrand (fun p : X*Y => f p.1*g p.2)) (a*b)%:E.
Proof.
move=> hfn hgn hf hg.
have hfl := summable_real_total_lone ha (ex_intro _ a hf).
have hgl := summable_real_total_lone hb (ex_intro _ b hg).
have hc := scalar_real_integrand_countably_measurable (product_measure_is_measure ha hb)
  (@product_countably_measurable_scalar_function R X Y alpha beta ha hb f g hfl.2.2.2 hgl.2.2.2).
have hp : measure_almost_everywhere (product_measure ha hb)
    (partial_extended_nonnegative_locus (real_total_integrand (fun p : X*Y => f p.1*g p.2))).
  apply: (@measure_almost_everywhere_mono R (Choice.clone (X*Y)%type _) _
    (product_measure_is_measure ha hb) setT _ _ (measure_almost_everywhere_true (product_measure_is_measure ha hb))).
  move=> [x y] _.
  exists (f x*g y)%:E; split; first by apply/real_total_integrand_graph.
  by rewrite lee_fin; exact: mulr_ge0 (hfn x) (hgn y).
have [z hz] := nonnegative_measurable_function_integrable (product_measure_is_measure ha hb)
  (countably_measurable_function_measurable hc) hp.
have hi := (@product_function_fubini R X Y alpha beta ha hb _ z hz hc).1.
have hj := @separated_repeated_integral R X Y alpha beta ha hb f g a b hf hg.
have he := measure_integral_unique hi hj.
by rewrite -he.
Qed.
