(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(8), p. 329:
    preparation and division give the original
    finite simple quotient extension. Reuse the
    proved preparation, distinguished-polynomial regularity,
    bounded remainder generation and polynomial-image laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus HolomorphicLinear Hom RealNormUP NormDifferentialUP HolomorphicGermUP HolomorphicGermRing
  HolomorphicGermRepresentatives HolomorphicGermValueSealed ComplexWeierstrassTransverseUP ComplexWeierstrassTransversePullback
  ComplexWeierstrassRegularUP ComplexWeierstrassPreparationUP ComplexWeierstrassPreparationExistence
  HolomorphicPreparedPolynomialImage HolomorphicDistinguishedPolynomialLine
  CommutativeIdealUP CommutativeSubringUP CommutativePolynomialUP CommutativePolynomialEvaluationUP
  DistinguishedPolynomialUP CommutativeQuotientUP HolomorphicQuotientPolynomialImage
  RingScalarRestriction RingSubmoduleUP PolynomialBoundedImageGeneration
  PolynomialScalarComposition PolynomialPrimitiveGenerator.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FiniteQuotient.
Variable R:realType.
Variables X K:lmodType (ComplexScalars.C R).
Variables (NX:X->R) (NK:K->R).
Variables (hNX:is_complex_norm NX) (hNK:is_complex_norm NK).
Variable v:X.
Variable xi:Hom X (ComplexScalars.C R)^o.
Variables (inclusion:Hom K X) (projection:Hom X K).
Hypothesis hSplit:is_complex_weierstrass_transverse_space NX NK v xi inclusion projection.
Variable fXi:@holomorphic_representative_type R X NX (complex_norm_real hNX) 0.
Hypothesis hXi:@norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) (complex_hom_real xi).
Hypothesis hXiValues:forall x,holomorphic_representative_value fXi x = xi x.
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0)].
Local Notation A:=[the comNzRingType of (@holomorphic_germ_ring R K NK (complex_norm_real hNK) (projection 0))].
Local Notation pullback:=(@complex_weierstrass_transverse_ring_pullback R X K NX NK hNX hNK
  v xi inclusion projection hSplit).
Local Notation Gamma:=(holomorphic_germ fXi:G).
Variable B:comNzRingType.
Variable embed:{rmorphism A->B}.
Variable variable:B.
Variable coefficient:B->nat->A.
Hypothesis hP:is_commutative_polynomial_ring embed variable coefficient.
Variable J:{rmorphism B->G}.
Hypothesis hJ:is_commutative_polynomial_evaluation embed variable pullback Gamma J.
Variable C:comNzRingType.
Variable I:set G.
Variable pi:{rmorphism G->C}.
Hypothesis hIdeal:is_commutative_ideal I.
Hypothesis hQuotient:is_commutative_ideal_quotient I pi.
Local Notation scalar:=(GRing.RMorphism.clone A C (pi \o pullback) _).
Local Notation evaluate:=(GRing.RMorphism.clone B C (pi \o J) _).

(** Source for [regular_holomorphic_quotient_finite_extension]:
    the original quotient is finite over the
    preceding coefficient ring and generated as
    a ring by its coordinate class, 3.4.8(8),
    p. 329. Preparation supplies an actual
    distinguished polynomial in the original ideal;
    division supplies every quotient representative. *)
Theorem regular_holomorphic_quotient_finite_extension (Phi:G) k:
  I Phi ->is_complex_weierstrass_regular_germ hNX Phi k v ->
  is_finitely_generated_ring_submodule
    (setT:set [the lmodType A of ring_restricted_space scalar C^o]) /\
  is_generated_commutative_subring
    (fun y:C=>y = pi Gamma \/exists a:A,y = scalar a) setT /\
  exists H:B,is_distinguished_polynomial coefficient
    (@HolomorphicGermValue.map R K NK (complex_norm_real hNK) (projection 0)) H k /\I (J H).
Proof.
move=>hPhi hRegular.
have [Q [W [Wi hPreparation]]]:=@complex_weierstrass_preparation_with_transverse_exists R X K NX NK hNX hNK
  v xi inclusion projection k Phi hSplit hXi hRegular.
have [H [hDistinguished hH]]:=@holomorphic_prepared_polynomial_image R X K NX NK hNX hNK
  v xi inclusion projection hSplit fXi hXiValues B embed variable coefficient hP J hJ k W Wi
  (complex_weierstrass_preparation_polynomial hPreparation).
have hIn:I (J H).
  rewrite hH -(complex_weierstrass_preparation_identity hPreparation).
  exact:(@commutative_ideal_mul G I hIdeal Q Phi hPhi).
have hPreparedRegular:=@holomorphic_distinguished_polynomial_regular R X K NX NK hNX hNK
  v xi inclusion projection hSplit fXi hXiValues B embed variable coefficient hP J hJ H k hDistinguished hRegular.1.
have hRepresentative x:=@holomorphic_quotient_polynomial_representative R X K NX NK hNX hNK
  v xi inclusion projection hSplit fXi hXi hXiValues B embed variable coefficient hP J hJ C I pi hQuotient H k
  hPreparedRegular hIn x.
have hEvaluate:is_commutative_polynomial_evaluation embed variable scalar (pi Gamma) evaluate:=
  polynomial_evaluation_after_ring_map pi hJ.
pose bounded:set [the lmodType A of ring_restricted_space scalar C^o]:=fun x=>exists P:B,
  (forall i,(k<=i)%N ->coefficient P i = 0) /\x = evaluate P.
have hSets:bounded = setT.
  apply:funext=>x;apply:propext;split=>_;first exact:Logic.I.
  have [P [hBound hValue]]:=hRepresentative x.
  exists P;split;first exact:hBound.
  exact:esym hValue.
split.
- rewrite -hSets.
  exact:(@bounded_polynomial_image_finite A B C embed variable coefficient hP scalar (pi Gamma) evaluate hEvaluate k).
- split.
  + apply:(@polynomial_surjection_primitive_generator A B C embed variable coefficient hP scalar (pi Gamma) evaluate hEvaluate).1.
    move=>x;have [P [_ hValue]]:=hRepresentative x;by exists P.
  + exists H;by split.
Qed.
End FiniteQuotient.
