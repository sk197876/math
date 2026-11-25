(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(10), pp. 330–331:
    obtain the original polynomial equation data
    from the printed prime-ideal and E_m
    hypotheses. Quotients and fraction fields
    remain local witnesses behind their existing
    opaque interfaces. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import FiniteCoordinates ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexOrderedBases HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup HolomorphicCoordinateNorm FieldCoordinateFunctional Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthonormalFamilies GrassmannAbbreviations EuclideanInnerProduct OrthogonalGroupTopology
  HolomorphicGermRing HolomorphicGermNoetherian HolomorphicScalarsSealed HolomorphicCoordinateGermsSealed HolomorphicPrefixGermMap
  HolomorphicRotatedGermIdeal HolomorphicRotatedIdealPrime HolomorphicReductionLociUP HolomorphicReductionActual
  HolomorphicReductionUniformRelations HolomorphicReductionEquationSaturation HolomorphicReductionProperIdeal
  HolomorphicCoordinateSubringFamilySealed
  CommutativeIdealUP CommutativeIdealSealed CommutativeQuotientSealed CommutativeQuotientLaws
  FractionFieldSealed CoefficientFractionFieldSealed CommutativeFactorizationUP
  CommutativePolynomialUP CommutativePolynomialEvaluationUP FormalPolynomialDerivativeUP
  DistinguishedPolynomialUP HolomorphicGermValueSealed OrdinalCoordinateTail
  SetGermUP SetGermSealed HolomorphicZeroGermSealed HolomorphicIdealVarietyGermSealed HolomorphicEquationSaturationVarietyRecovery.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OriginalEquations.
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
Local Notation Top:=(Topological.clone (real_norm_metric_space hNXR) _).
Variable I:set G.
Variable g:@unitary_group R X Herm hHerm (n+n) eR heR.
Variable m:'I_n.
Hypothesis hMN:((m:nat)<=n)%N.
Local Notation A:=[the comNzRingType of (@holomorphic_germ_ring R (coordinate_space (ComplexScalars.C R) m)
  (@holomorphic_coordinate_norm R m)
  (complex_norm_real (@holomorphic_coordinate_norm_laws R m)) 0)].
Local Notation E:=(@holomorphic_prefix_germ_map R X NX hNXR n e he omega m hMN).
Local Notation gamma:=(fun j:'I_n=>@HolomorphicCoordinateGerms.value R X NX hNX n e he omega j).
Local Notation Ig:=(@holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR I g).
Variable P:comNzRingType.
Variable embed:{rmorphism A->P}.
Variable variable:P.
Variable coefficient:P->nat->A.
Hypothesis hP:is_commutative_polynomial_ring embed variable coefficient.
Variable J:{rmorphism P->G}.
Hypothesis hJ:is_commutative_polynomial_evaluation embed variable E (gamma m) J.

(** Source for [holomorphic_reduction_original_equation_data]:
    the common delta, bounded numerators,
    original equation ideal F and enlarged
    ideal J in 3.4.8(10), pp. 330–331.
    Every algebraic relation, positive-power conclusion
    and variety-germ equation is proved from
    the original prime ideal and E_m
    hypotheses. No field or ideal-saturation
    conclusion is an additional premise. *)
Theorem holomorphic_reduction_original_equation_data:
  is_prime_commutative_ideal I ->(0<m)%N ->
  @holomorphic_reduction_actual_E R X Herm hHerm n e he omega I (widen_ord (leqnSn n) m) g ->
  exists (W derivative:P) k (delta:A) (T:'I_(n-m)->P) (first:'I_(n-m)) (F K:set G),
    (first:nat) = 0%N /\(0<k)%N /\
    is_distinguished_polynomial coefficient
      (@HolomorphicGermValue.map R (coordinate_space (ComplexScalars.C R) m) (@holomorphic_coordinate_norm R m)
        (complex_norm_real (@holomorphic_coordinate_norm_laws R m)) 0) W k /\
    (forall H:P,Ig (J H) <->commutative_divides W H) /\
    is_formal_polynomial_derivative coefficient W derivative /\
    ~Ig (J derivative) /\~Ig (E delta) /\
    (forall i j,(k<=j)%N ->coefficient (T i) j = 0) /\
    Ig (J derivative*J (T first)-E delta) /\
    (forall i:'I_(n-m),i<>first ->Ig (E delta*gamma (ordinal_coordinate_tail_index hMN i)-J (T i))) /\
    is_generated_commutative_ideal
      (fun alpha:G=>exists i:'I_(n-m),alpha = if i==first then J W else
        E delta*gamma (ordinal_coordinate_tail_index hMN i)-J (T i)) F /\
    is_generated_commutative_ideal (Ig `|` [set alpha|alpha = E delta]) K /\
    F `<=` Ig /\
    (forall alpha:G,Ig alpha ->exists u:nat,(0<u)%N /\F ((E delta)^+u*alpha)) /\
    (forall H:set G,is_commutative_ideal H ->Ig `<=` H ->
      (exists alpha:G,H alpha /\~Ig alpha) ->exists beta:G,H beta /\
        @HolomorphicCoordinateSubringFamily.value R X NX hNXR n e he omega m beta /\
        ~Ig beta /\beta<>0) /\
    exists (hIg:is_finitely_generated_commutative_ideal Ig)
      (hF:is_finitely_generated_commutative_ideal F) (hK:is_finitely_generated_commutative_ideal K),
      @HolomorphicIdealVarietyGerm.value R X NX hNXR 0 Ig hIg =
        @SetGerms.join Top 0 (@HolomorphicIdealVarietyGerm.value R X NX hNXR 0 K hK)
          (@SetGerms.meet Top 0 (@HolomorphicIdealVarietyGerm.value R X NX hNXR 0 F hF)
            (@SetGerms.neg Top 0 (@HolomorphicZeroGerm.value R X NX hNXR 0 (E delta)))).
Proof.
move=>hPrime hPositive hEm.
have [hCm [hAllB hNotA]]:=(holomorphic_reduction_E_membership
  (@holomorphic_reduction_actual_laws R X Herm hHerm n e he omega I) m g).1 hEm.
have hPrimeRot:=@holomorphic_rotated_germ_ideal_prime R X Herm hHerm (n+n) eR heR I g hPrime.
pose realG:=@HolomorphicScalars.map R X NX hNXR 0.
pose C:=@CommutativeIdealQuotient.space (ComplexScalars.C R) G realG Ig hPrimeRot.1 hPrimeRot.2.1.
pose pi:=@CommutativeIdealQuotient.projection (ComplexScalars.C R) G realG Ig hPrimeRot.1 hPrimeRot.2.1.
have hPi:=@CommutativeIdealQuotient.laws (ComplexScalars.C R) G realG Ig hPrimeRot.1 hPrimeRot.2.1.
have hDomain:=@prime_commutative_quotient_domain G C Ig pi hPi hPrimeRot.
pose L:=@FractionField.space C hDomain.
pose inclusion:=@FractionField.embed C hDomain.
have hFraction:=@FractionField.laws C hDomain.
pose scalar:{rmorphism A->C}:=GRing.RMorphism.clone A C (pi \o E) _.
pose original:{rmorphism A->L}:=GRing.RMorphism.clone A L (inclusion \o scalar) _.
pose M:=@CoefficientFractionField.space A L original.
pose eta:=@CoefficientFractionField.scalar A L original.
pose phi:=@CoefficientFractionField.inclusion A L original.
have hCoefficient:=@CoefficientFractionField.laws A L original.
have [W [derivative [k [delta [T [first [hFirst [hK [hDistinguished [hKernel
  [hDerivative [hDerivativeOutside [hDeltaPrefix [hDeltaOutside [hBound [hFirstRelation hRelations]]]]]]]]]]]]]]]]:=
  @holomorphic_reduction_uniform_original_relations R X Herm hHerm n e he omega hDual
    I hPrime.1 hPrime.2.1 g C pi hPi m hMN hAllB L M inclusion hFraction eta phi hCoefficient
    P embed variable coefficient hP J hJ hPositive hNotA hCm.
have [F [hGenerated [hFI hPower]]]:=@holomorphic_reduction_equation_ideal_power R X Herm hHerm n e he omega hDual
  I hPrime.1 hPrime.2.1 g C pi hPi m hMN hAllB L inclusion hFraction P embed variable coefficient hP J hJ
  W k delta T first hFirst hK hDistinguished hKernel hDeltaOutside hRelations.
pose K:=@GeneratedCommutativeIdeal.value G (Ig `|` [set alpha|alpha = E delta]).
have hKGenerated:=@GeneratedCommutativeIdeal.laws G (Ig `|` [set alpha|alpha = E delta]).
have hNoetherian:=@finite_holomorphic_germ_ring_noetherian R X NX hNX n e 0 he.
pose hIg:=hNoetherian Ig hPrimeRot.1.
pose hF:=hNoetherian F (generated_commutative_ideal_laws hGenerated).
pose hKFinite:=hNoetherian K (generated_commutative_ideal_laws hKGenerated).
have hLarger:=@holomorphic_reduction_proper_ideal_coefficient R X Herm hHerm n e he omega hDual
  I hPrime.1 hPrime.2.1 g C pi hPi m hMN hAllB L M inclusion hFraction eta phi hCoefficient
  P embed variable coefficient hP J hJ hPositive hNotA hCm.
exists W,derivative,k,delta,T,first,F,K.
split;first exact:hFirst.
split;first exact:hK.
split;first exact:hDistinguished.
split;first exact:hKernel.
split;first exact:hDerivative.
split;first exact:hDerivativeOutside.
split;first exact:hDeltaOutside.
split;first exact:hBound.
split;first exact:hFirstRelation.
split;first exact:hRelations.
split;first exact:hGenerated.
split;first exact:hKGenerated.
split;first exact:hFI.
split;first exact:hPower.
split;first exact:hLarger.
exists hIg,hF,hKFinite.
exact:(@equation_saturation_variety_recovery R X NX hNXR 0 Ig F K hIg hF hKFinite (E delta)
  hFI hPower hKGenerated).
Qed.
End OriginalEquations.
