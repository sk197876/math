(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(10), p. 330:
    the original polynomial kernel has a
    distinguished monic generator. Connect its
    proved minimal generator to the original
    prepared prefix polynomial and the existing
    distinguished monic-divisor theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexOrderedBases HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup HolomorphicCoordinateNorm FieldCoordinateFunctional Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis FiniteCoordinates OrthonormalFamilies GrassmannAbbreviations EuclideanInnerProduct OrthogonalGroupTopology
  HolomorphicGermRing HolomorphicGermFactorization HolomorphicCoordinateGermsSealed HolomorphicPrefixGermMap
  HolomorphicRotatedGermIdeal HolomorphicReductionActual HolomorphicReductionFieldInputs HolomorphicReductionFaithfulPrefix
  CommutativeDomainUP CommutativeIdealUP CommutativeQuotientUP CommutativeFactorizationUP FractionFieldUP
  CoefficientFractionFieldUP CoefficientFaithfulFractionField IntegralRingElementUP
  CommutativePolynomialUP CommutativePolynomialMonicUP CommutativePolynomialSealed
  CommutativePolynomialEvaluationUP CommutativePolynomialEvaluationSealed PolynomialScalarComposition
  PolynomialCoefficientMapSealed IntegralMinimalPolynomialDescent FieldPolynomialMinimumUP HolomorphicReductionMinimalPolynomial HolomorphicPrefixPreparedPolynomial
  HolomorphicGermValueSealed DistinguishedPolynomialUP DistinguishedMonicDivisor.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OriginalDistinguished.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable Herm:X->X->ComplexScalars.C R.
Hypothesis hHerm:is_hermitian_product Herm.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation B:=(hermitian_real_part Herm).
Local Notation hB:=(hermitian_real_inner_product hHerm).
Variable n:nat.
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Hypothesis hON:orthonormal_family Herm e.
Variable omega:'I_n->Hom X (ComplexScalars.C R)^o.
Hypothesis hDual:forall i k,omega i (e k) = if i==k then 1 else 0.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(hermitian_complex_norm hHerm).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation eR:=(ordered_real_basis e).
Local Notation heR:=(ordered_real_basisP he).
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNXR 0)].
Variable I:set G.
Hypothesis hI:is_commutative_ideal I.
Hypothesis hProper:~I 1.
Variable g:@unitary_group R X Herm hHerm (n+n) eR heR.
Variable C:comNzRingType.
Variable pi:{rmorphism G->C}.
Hypothesis hPi:is_commutative_ideal_quotient (@holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR I g) pi.
Variable m:'I_n.
Hypothesis hMN:((m:nat)<=n)%N.
Hypothesis hAllB:forall j:'I_n,(m<=j)%N ->@holomorphic_reduction_actual_B R X Herm hHerm n e he omega I j g.
Local Notation A:=[the comNzRingType of (@holomorphic_germ_ring R (coordinate_space (ComplexScalars.C R) m)
  (@holomorphic_coordinate_norm R m)
  (complex_norm_real (@holomorphic_coordinate_norm_laws R m)) 0)].
Local Notation A1:=[the comNzRingType of (@holomorphic_germ_ring R (coordinate_space (ComplexScalars.C R) (m:nat).+1)
  (@holomorphic_coordinate_norm R (m:nat).+1)
  (complex_norm_real (@holomorphic_coordinate_norm_laws R (m:nat).+1)) 0)].
Local Notation E:=(@holomorphic_prefix_germ_map R X NX hNXR n e he omega m hMN).
Local Notation E1:=(@holomorphic_prefix_germ_map R X NX hNXR n e he omega (m:nat).+1 (ltn_ord m)).
Local Notation scalar:=(GRing.RMorphism.clone A C (pi \o E) _).
Local Notation gamma:=(fun j:'I_n=>@HolomorphicCoordinateGerms.value R X NX hNX n e he omega j).
Variables L M:fieldType.
Variable inclusion:{rmorphism C->L}.
Hypothesis hFraction:is_commutative_fraction_field inclusion.
Variable eta:{rmorphism A->M}.
Variable phi:{rmorphism M->L}.
Hypothesis hCoefficient:is_coefficient_fraction_field
  (GRing.RMorphism.clone A L (inclusion \o scalar) _) eta phi.


Variable P:comNzRingType.
Variable embed:{rmorphism A->P}.
Variable variable:P.
Variable coefficient:P->nat->A.
Hypothesis hP:is_commutative_polynomial_ring embed variable coefficient.
Variable J:{rmorphism P->G}.
Hypothesis hJ:is_commutative_polynomial_evaluation embed variable E (gamma m) J.


(** Source for [holomorphic_reduction_monic_kernel_distinguished]:
    every original monic polynomial kernel
    generator is distinguished, 3.4.8(10),
    p. 330. Apply the original prepared
    prefix annihilator and the already proved
    distinguished monic-divisor theorem. *)
Theorem holomorphic_reduction_monic_kernel_distinguished (W:P) k:
  is_monic_polynomial coefficient W k ->
  (forall T:P,@holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR I g (J T) <->
    commutative_divides W T) ->
  is_distinguished_polynomial coefficient
    (@HolomorphicGermValue.map R (coordinate_space (ComplexScalars.C R) m) (@holomorphic_coordinate_norm R m)
      (complex_norm_real (@holomorphic_coordinate_norm_laws R m)) 0) W k.
Proof.
move=>hMonic hKernel.
pose bound:=leq_trans (leqnSn (m:nat)) (ltn_ord m).
have hJBound:is_commutative_polynomial_evaluation embed variable
    (@holomorphic_prefix_germ_map R X NX hNXR n e he omega m bound) (gamma m) J.
  apply:(polynomial_evaluation_change_parameters hJ).
  - move=>a;by rewrite (bool_irrelevance hMN bound).
  - by [].
have [hInjection [V [r [hR [hDistinguished hIn]]]]]:=@holomorphic_prefix_distinguished_ideal_polynomial
  R X Herm hHerm n e he omega hDual I g m P embed variable coefficient hP J hJBound hI hProper
  (@hAllB m (leqnn m)).
have hDivides:commutative_divides W V:=(hKernel V).1 hIn.
have hDomain:=(@finite_holomorphic_germ_ring_factorization R (coordinate_space (ComplexScalars.C R) m)
  (@holomorphic_coordinate_norm R m)
  (@holomorphic_coordinate_norm_laws R m) m (@coordinate_basis (ComplexScalars.C R) m) 0 (@coordinate_basisP (ComplexScalars.C R) m)).1.
have hScalarDomain:is_commutative_integral_domain (ComplexScalars.C R).
  move=>a b /eqP;rewrite mulf_eq0;move/orP=>[/eqP hA|/eqP hB0];[by left|by right].
have hDistinguishedW:=@distinguished_polynomial_monic_divisor A P (ComplexScalars.C R) embed variable coefficient hP
  (@HolomorphicGermValue.map R (coordinate_space (ComplexScalars.C R) m) (@holomorphic_coordinate_norm R m)
    (complex_norm_real (@holomorphic_coordinate_norm_laws R m)) 0) hDomain hScalarDomain V W r k
  hDistinguished hMonic hDivides.
exact:hDistinguishedW.
Qed.
(** Source for [holomorphic_reduction_original_distinguished_kernel]:
    the actual monic kernel generator has
    lower coefficients zero at the original
    prefix centre, 3.4.8(10), p. 330.
    The original B_(m+1) yields the prepared
    annihilator; exact original kernel divisibility
    and the earlier factor specialization prove
    the required coefficient values. *)
Theorem holomorphic_reduction_original_distinguished_kernel:
  (0<m)%N ->~@holomorphic_reduction_actual_A R X Herm hHerm n e he omega I (widen_ord (leqnSn n) m) g ->
  injective J /\exists (W:P) k,(0<k)%N /\
    is_distinguished_polynomial coefficient
      (@HolomorphicGermValue.map R (coordinate_space (ComplexScalars.C R) m) (@holomorphic_coordinate_norm R m)
        (complex_norm_real (@holomorphic_coordinate_norm_laws R m)) 0) W k /\
    (forall T:P,@holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR I g (J T) <->
      commutative_divides W T).
Proof.
move=>hPositive hNotA.
have [W [k [hK [hMonic hKernel]]]]:=@holomorphic_reduction_original_minimal_kernel
  R X Herm hHerm n e he omega hDual I hI hProper g C pi hPi m hMN hAllB
  L M inclusion hFraction eta phi hCoefficient P embed variable coefficient hP J hJ hPositive hNotA.
have hDistinguished:=holomorphic_reduction_monic_kernel_distinguished hMonic hKernel.
pose bound:=leq_trans (leqnSn (m:nat)) (ltn_ord m).
have hJBound:is_commutative_polynomial_evaluation embed variable
    (@holomorphic_prefix_germ_map R X NX hNXR n e he omega m bound) (gamma m) J.
  apply:(polynomial_evaluation_change_parameters hJ).
  - move=>a;by rewrite (bool_irrelevance hMN bound).
  - by [].
have hInjection:=(@holomorphic_prefix_distinguished_ideal_polynomial
  R X Herm hHerm n e he omega hDual I g m P embed variable coefficient hP J hJBound hI hProper
  (@hAllB m (leqnn m))).1.
split;first exact:hInjection.
exists W,k;split;first exact:hK.
by split.
Qed.
End OriginalDistinguished.
