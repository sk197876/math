(** Federer (1969), 2.5.20, p. 114: T=mu o S is the linear functional on
    continuous K(Y)-valued families. Its finite variation bounds follow from
    the uniform bound for a Daniell functional on a compact space, 2.5.19,
    p. 113. These verify hypotheses, not assume a decomposition. Source
    context: CompactFunctionSpaceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric FunctionLatticeUP FunctionLatticeSeminormUP
  CompactSupportFunctionUP CompactSupportUniformBound DaniellIntegralUP DaniellSpaceCompactness
  DaniellSpaceCompactSpace CompactFunctionSpaceUP CompactFunctionSpaceLaws CompactFunctionCurrying
  OrderBoundedVectorFunctionalUP ContinuousVectorFamily.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_product_vector_functional]: the
    displayed definition T=mu o S in Federer 2.5.20,
    p. 114. Its laws are required only on continuous families. *)
Definition compact_product_vector_functional (R : realType) (X Y : topologicalType)
    (E : lmodType R) (ev : E -> Y -> R) (mu : ((X*Y) -> R) -> R)
    (w : X -> E) := mu (compact_function_uncurry ev w).

(** Source for [compact_product_vector_functional_order_bounded]:
    verified linearity and finite variation bounds of T in
    Federer 2.5.20, p. 114, required by 2.5.12(5),
    p. 103. Sequential continuity follows separately from compactness. *)
Theorem compact_product_vector_functional_order_bounded (R : realType) (X Y : topologicalType)
    (E : lmodType R) (ev : E -> Y -> R) (hE : is_compact_function_space ev)
    (mu : ((X*Y) -> R) -> R) :
  compact (@setT X) -> compact (@setT Y) ->
  is_daniell_integral (@compactly_supported_continuous_functions R (X*Y)%type) mu ->
  is_order_bounded_vector_functional (compact_function_norm ev)
    (@compactly_supported_continuous_functions R X)
    (@continuous_normed_functions R X E _ (compact_function_norm_laws hE))
    (compact_product_vector_functional ev mu).
Proof.
move=> hX hY hmu.
have hXY : compact (@setT (X*Y)%type).
  have he : (@setT X) `*` (@setT Y)=setT by apply/seteqP; split=> p _; split.
  rewrite -he; exact: compact_setX hX hY.
have hlin := @daniell_compact_support_linear R (X*Y)%type mu hmu.
have hS (w : X -> E) : continuous_normed_functions (compact_function_norm_laws hE) w ->
    compactly_supported_continuous_functions (compact_function_uncurry ev w).
  exact (@compact_function_uncurry_member R X Y E ev hE hX hY w).
constructor.
- move=> w v hw hv; rewrite /compact_product_vector_functional /compact_function_uncurry.
  have he : (fun p : X*Y => ev (w p.1+v p.1) p.2)=
      (fun p : X*Y => ev (w p.1) p.2+ev (v p.1) p.2).
    by apply: funext=> p; case: p=> x y; rewrite (compact_function_evaluation_add hE).
  rewrite he; exact: hlin.1 _ _ (hS w hw) (hS v hv).
- move=> c w hw; rewrite /compact_product_vector_functional /compact_function_uncurry.
  have he : (fun p : X*Y => ev (c*:w p.1) p.2)=
      (fun p : X*Y => c*ev (w p.1) p.2).
    by apply: funext=> p; case: p=> x y; rewrite (compact_function_evaluation_scale hE).
  rewrite he; exact: hlin.2 c _ (hS w hw).
- move=> f hf.
  have [C [hC hbound]] := @daniell_sup_norm_bounded R (X*Y)%type hXY mu hmu.
  have [M [hM hfM]] := compact_support_uniform_bound hf.1.
  exists (C*M)=> w hw hb.
  rewrite /compact_product_vector_functional.
  apply: le_trans (ler_norm _) _.
  apply: (hbound (compact_function_uncurry ev w) (hS w hw) M hM).
  move=> [x y]; apply: le_trans (compact_function_evaluation_bound hE (w x) y) _.
  apply: le_trans (hb x) _.
  apply: le_trans (ler_norm _) (hfM x).
Qed.
