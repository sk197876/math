(** Federer (1969), 2.6.4, pp. 118–119: density of the canonical
    monomorphism measured by (alpha times beta)(1). This connects the actual
    absolute-error integrals to the existing abstract Lebesgue seminorm; no
    new norm is constructed. The total-domain convention follows erratum p.
    2, book p. 119 lines 3, 4, 6. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP ProductMeasure SummableRealFunctionUP SummableRealArithmetic SummableRealNormed
  SummableRealSpace SummableTensorMap SummableTensorImage SummableTensorDensity FunctionProductBilinear
  TensorProduct TotalScalarLpUP TotalScalarLpFiniteSeminorm TotalLoneSummability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [summable_tensor_map_seminorm_dense]: exact
    seminorm-density assertion in Federer 2.6.4, pp. 118–119,
    for the actual abstract total-domain L1 carriers. *)
Theorem summable_tensor_map_seminorm_dense (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta)
    (f : summable_real_space (product_measure_is_measure ha hb)) (e : R) : 0<e ->
  exists t : tensor_space (summable_real_space ha) (summable_real_space hb),
    finite_total_scalar_lp_norm (product_measure ha hb) 1
      (fun p => summable_real_value (summable_tensor_map ha hb t) p-summable_real_value f p)<e.
Proof.
move=> he.
have [h [q [[t ht] [hi hq]]]] := @summable_tensor_image_dense R X Y alpha beta ha hb
  (summable_real_value f) e (summable_real_value_summable f) he.
exists t.
have hv : summable_real_value (summable_tensor_map ha hb t)=h.
  by rewrite summable_tensor_map_function.
have hs := @summable_real_subtract R (Choice.clone (X*Y)%type _) _ (product_measure_is_measure ha hb)
  h (summable_real_value f)
  (@separated_summable_image_summable R X Y alpha beta ha hb h (ex_intro _ t ht))
  (summable_real_value_summable f).
have hm := (@summable_real_function_in_normed_collection R (Choice.clone (X*Y)%type _) _
  (product_measure_is_measure ha hb) _ hs).1.
have hn := @total_lone_norm_from_absolute_integral R (Choice.clone (X*Y)%type _) _
  (product_measure_is_measure ha hb) (fun p => h p-summable_real_value f p) q hm hi.
by rewrite hv /finite_total_scalar_lp_norm hn.
Qed.
