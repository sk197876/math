(** Federer (1969), 2.5.20, p. 114: the variation lambda of T=mu o S is
    exactly the least upper bound on product tests |u(x,y)|<=f(x). This
    bridges the vector theorem and the final identification of the measure.
    Source context: CompactFunctionSpaceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import CompactFunctionSpaceUP CompactFunctionSpaceLaws CompactFunctionCurrying
  ContinuousVectorFamily CompactProductVectorFunctional ProductFibreVariationUP
  CompactSupportFunctionUP UniformFunctionNorm UniformFunctionNormUP
  FunctionLatticeUP VectorDaniellHypotheses VectorDaniellVariationIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_product_vector_variation_specification]:
    the displayed S and norm in Federer 2.5.20, p. 114,
    identify the bound in the definition of lambda from
    2.5.12(5), p. 103. Empty factors are allowed;
    the least-nonnegative-bound convention for the uniform
    norm handles an empty Y. *)
Theorem compact_product_vector_variation_specification (R : realType)
    (X Y : topologicalType) (E : lmodType R) (ev : E -> Y -> R)
    (hE : is_compact_function_space ev) (mu : ((X*Y) -> R) -> R)
    (f : X -> R) :
  hausdorff_space Y -> compact (@setT X) -> compact (@setT Y) ->
  is_vector_variation_functional (compact_function_norm ev)
    (@compactly_supported_continuous_functions R X)
    (@continuous_normed_functions R X E _ (compact_function_norm_laws hE))
    (compact_product_vector_functional ev mu) ->
  positive_function_lattice (@compactly_supported_continuous_functions R X) f ->
  is_product_fibre_variation mu f
    (variation_integral (compact_function_norm ev)
      (@continuous_normed_functions R X E _ (compact_function_norm_laws hE))
      (compact_product_vector_functional ev mu) f).
Proof.
move=> hh hX hY hT hf.
have hQ := @continuous_normed_functions_vector_space R X E _ (compact_function_norm_laws hE).
constructor.
- move=> u hu hb.
  have [w [hw he]] := compact_function_uncurry_surjective hE hh hY hu.
  have hnorm : function_le (fun x => compact_function_norm ev (w x)) f.
    move=> x; apply: (@uniform_function_norm_least R Y (ev (w x))
      (compact_function_norm ev (w x))
      (compact_support_uniform_norm_specification
        (@compact_function_evaluation_member R Y E ev hE (w x))) (f x) (hf.2 x)).
    move=> y; have h := hb x y; by rewrite -he /compact_function_uncurry in h.
  have h := @variation_integral_upper R X E _ (compact_function_norm_laws hE)
    (@compactly_supported_continuous_functions R X)
    (@continuous_normed_functions R X E _ (compact_function_norm_laws hE))
    (compact_product_vector_functional ev mu) hQ hT f w hf hw hnorm.
  by rewrite /compact_product_vector_functional he in h.
- move=> b hb.
  apply: (@variation_integral_least R X E _ (compact_function_norm_laws hE)
    (@compactly_supported_continuous_functions R X)
    (@continuous_normed_functions R X E _ (compact_function_norm_laws hE))
    (compact_product_vector_functional ev mu) hQ f b hf)=> w hw hnorm.
  rewrite /compact_product_vector_functional.
  apply: (hb (compact_function_uncurry ev w)
    (@compact_function_uncurry_member R X Y E ev hE hX hY w hw))=> x y.
  exact: le_trans (compact_function_evaluation_bound hE (w x) y) (hnorm x).
Qed.
