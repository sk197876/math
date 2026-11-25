(** Federer (1969), 4.1.5, p. 350:
    the restriction of a scalar Daniell
    integral to a linear space of original
    compact tests exists and has finite
    original variation. Use the proved
    2.5.6 symmetric-interval bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP CompactSupportFunctionUP FunctionLatticeUP
  DaniellIntegralUP DaniellSpaceCompactness CompactUniformNorm VectorFunctionLattice
  DaniellVariation DaniellVariationFunctionals VectorVariationFiniteBounds
  ScalarDaniellRestrictionUP DistributionVariationUP DistributionVariationBoundedExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DaniellLinearTestRestriction.
Variable R:realType.
Variable X:topologicalType.
Variable E:lmodType R.
Variable values:Hom E (GRing.Lmodule.clone R (X->R^o) _).
Hypothesis hTest:forall phi:E,compactly_supported_continuous_functions (values phi).
Variable A:(X->R)->R.
Hypothesis hA:is_daniell_integral (@compactly_supported_continuous_functions R X) A.
Local Notation K := (@compactly_supported_continuous_functions R X).

(** Source for [daniell_linear_test_restriction_exists]: the
    original scalar restriction S=mu|D(U,R)
    is real linear, Federer 4.1.5, p. 350.
    This existence proof precedes continuity. *)
Theorem daniell_linear_test_restriction_exists:
  exists S:Hom E R^o,@is_scalar_daniell_test_restriction R X E values A S.
Proof.
pose L:=fun phi:E=>(A (values phi):R^o).
have hLinear:linear L.
  move=>c phi psi.
  have hValues:values (c*:phi+psi)=(fun x=>c*values phi x+values psi x).
    apply:funext=>x.
    exact:(congr1 (fun f:X->R^o=>f x) (hom_linear values c phi psi)).
  have hKLinear:=@daniell_compact_support_linear R X A hA.
  have hScaled:=@compactly_supported_scale R X c (values phi) (hTest phi).
  change (A (values (c*:phi+psi))=c*A (values phi)+A (values psi)).
  by rewrite hValues (hKLinear.1 _ _ hScaled (hTest psi)) (hKLinear.2 c _ (hTest phi)).
exists (@HomMap R E R^o L (introT (asboolP _) hLinear)).
by move=>phi.
Qed.

(** Source for [daniell_linear_test_restriction_finite]: the
    scalar restriction has the finite original
    gauge condition, Federer 4.1.5, p. 350,
    by the existing 2.5.6 variation formula. *)
Theorem daniell_linear_test_restriction_finite (S:Hom E R^o):
  @is_scalar_daniell_test_restriction R X E values A S ->
  forall f,positive_function_lattice K f ->exists b:R,
    is_distribution_variation_value (fun t:R^o=>`|t|) values S f b%:E.
Proof.
move=>hRestriction f hf.
have hK:=@compact_support_vector_lattice R X.
pose P:=@daniell_positive_variation R X K A hK.1 hA.
pose Q:=@daniell_negative_variation R X K A hK.1 hA.
have hP:=@daniell_positive_variation_specification R X K A hK.1 hA.
have hQ:=@daniell_negative_variation_specification R X K A hK.1 hA.
apply:(@distribution_variation_bounded_value_exists R X R^o (fun t:R^o=>`|t|)
  (@scalar_absolute_value_norm R) E values S f (P f+Q f) hf.2)=>phi hNorm.
have hBound:=@finite_variation_sum_upper R X K A hK (daniell_integral_add hA)
  f (P f) (Q f) hf (hP f hf) (hQ f hf) (values phi) (conj (hTest phi) hNorm).
rewrite (@hRestriction phi); exact:le_trans (ler_norm _) hBound.
Qed.
End DaniellLinearTestRestriction.
