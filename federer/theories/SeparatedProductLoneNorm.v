(** Federer (1969), 2.6.4, pp. 118–119: supporting L1 seminorm identity for
    the separated-variable product, from 2.4.12, p. 86, and the
    product-integral identity. This is a supporting norm formula, not a
    separate assertion printed in 2.6.4. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP ProductMeasure SummableRealFunctionUP SummableRealArithmetic
  SummableRealNormed TotalScalarLpUP TotalLoneSummability SeparatedProductIntegral NonnegativeSeparatedIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [separated_product_lone_norm]: supporting
    seminorm calculation for the dense tensor embedding in Federer
    2.6.4, pp. 118–119. Zero norms and null-supported
    functions are included, without a quotient by null functions. *)
Theorem separated_product_lone_norm (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (f : X -> R) (g : Y -> R) :
  summable_real_functions alpha f -> summable_real_functions beta g ->
  total_scalar_lp_norm (product_measure ha hb) 1 (fun p : X*Y => f p.1*g p.2) =
  (total_scalar_lp_norm alpha 1 f * total_scalar_lp_norm beta 1 g)%E.
Proof.
move=> hf hg.
have [a hi] := summable_real_absolute ha hf.
have [b hj] := summable_real_absolute hb hg.
have hni := total_lone_norm_from_absolute_integral ha
  (summable_real_function_in_normed_collection ha hf).1 hi.
have hnj := total_lone_norm_from_absolute_integral hb
  (summable_real_function_in_normed_collection hb hg).1 hj.
have hh := @nonnegative_separated_integral R X Y alpha beta ha hb
  (fun x => `|f x|) (fun y => `|g y|) a b (fun _ => normr_ge0 _) (fun _ => normr_ge0 _) hi hj.
have he : (fun p : X*Y => `|f p.1|*`|g p.2|) = (fun p : X*Y => `|f p.1*g p.2|).
  by apply: funext=> p; rewrite normrM.
rewrite he in hh.
have hnk := total_lone_norm_from_absolute_integral (product_measure_is_measure ha hb)
  (summable_real_function_in_normed_collection (product_measure_is_measure ha hb)
    (separated_product_summable ha hb hf hg)).1 hh.
by rewrite hni hnj hnk -EFinM.
Qed.
