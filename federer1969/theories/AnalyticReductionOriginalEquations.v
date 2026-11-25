(** Federer (1969), 3.4.8(10), pp. 330–331:
    obtain the original polynomial equation data
    from the printed prime-ideal and E_m
    hypotheses. Quotients and fraction fields
    remain local witnesses behind their existing
    opaque interfaces. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthonormalFamilies GrassmannAbbreviations EuclideanInnerProduct OrthogonalGroupTopology
  AnalyticGermRing AnalyticGermNoetherian AnalyticScalarsSealed AnalyticCoordinateGermsSealed AnalyticPrefixGermMap
  AnalyticRotatedGermIdeal AnalyticRotatedIdealPrime AnalyticReductionLociUP AnalyticReductionActual
  AnalyticReductionUniformRelations AnalyticReductionEquationSaturation AnalyticReductionProperIdeal
  AnalyticCoordinateSubringFamilySealed
  CommutativeIdealUP CommutativeIdealSealed CommutativeQuotientSealed CommutativeQuotientLaws
  FractionFieldSealed CoefficientFractionFieldSealed CommutativeFactorizationUP
  CommutativePolynomialUP CommutativePolynomialEvaluationUP FormalPolynomialDerivativeUP
  DistinguishedPolynomialUP AnalyticGermValueSealed OrdinalCoordinateTail
  SetGermUP SetGermSealed AnalyticZeroGermSealed IdealVarietyGermSealed EquationSaturationVarietyRecovery.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OriginalEquations.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Hypothesis hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Hypothesis hON:orthonormal_family B e.
Variable omega:'I_n->Hom X R^o.
Hypothesis hDual:forall i k,omega i (e k) = if i==k then 1 else 0.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Local Notation Top:=(Topological.clone (real_norm_metric_space hNX) _).
Variable I:set G.
Variable g:@orthogonal_group R X B hB n e he.
Variable m:'I_n.
Hypothesis hMN:((m:nat)<=n)%N.
Local Notation A:=[the comNzRingType of (@analytic_germ_ring R (R_n R m)
  (inner_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R m)) 0)].
Local Notation E:=(@analytic_prefix_germ_map R X NX hNX n e he omega m hMN).
Local Notation gamma:=(fun j:'I_n=>@AnalyticCoordinateGerms.value R X NX hNX n e he omega j).
Local Notation Ig:=(@analytic_rotated_germ_ideal R X B hB n e he I g).
Variable P:comNzRingType.
Variable embed:{rmorphism A->P}.
Variable variable:P.
Variable coefficient:P->nat->A.
Hypothesis hP:is_commutative_polynomial_ring embed variable coefficient.
Variable J:{rmorphism P->G}.
Hypothesis hJ:is_commutative_polynomial_evaluation embed variable E (gamma m) J.

(** Source for [analytic_reduction_original_equation_data]:
    the common delta, bounded numerators,
    original equation ideal F and enlarged
    ideal J in 3.4.8(10), pp. 330–331.
    Every algebraic relation, positive-power conclusion
    and variety-germ equation is proved from
    the original prime ideal and E_m
    hypotheses. No field or ideal-saturation
    conclusion is an additional premise. *)
Theorem analytic_reduction_original_equation_data:
  is_prime_commutative_ideal I ->(0<m)%N ->
  @analytic_reduction_actual_E R X B hB n e he omega I (widen_ord (leqnSn n) m) g ->
  exists (W derivative:P) k (delta:A) (T:'I_(n-m)->P) (first:'I_(n-m)) (F K:set G),
    (first:nat) = 0%N /\(0<k)%N /\
    is_distinguished_polynomial coefficient
      (@AnalyticGermValue.map R (R_n R m) (inner_norm (@euclidean_inner_productP R m))
        (inner_norm_real_norm (@euclidean_inner_productP R m)) 0) W k /\
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
        @AnalyticCoordinateSubringFamily.value R X NX hNX n e he omega m beta /\
        ~Ig beta /\beta<>0) /\
    exists (hIg:is_finitely_generated_commutative_ideal Ig)
      (hF:is_finitely_generated_commutative_ideal F) (hK:is_finitely_generated_commutative_ideal K),
      @IdealVarietyGerm.value R X NX hNX 0 Ig hIg =
        @SetGerms.join Top 0 (@IdealVarietyGerm.value R X NX hNX 0 K hK)
          (@SetGerms.meet Top 0 (@IdealVarietyGerm.value R X NX hNX 0 F hF)
            (@SetGerms.neg Top 0 (@AnalyticZeroGerm.value R X NX hNX 0 (E delta)))).
Proof.
move=>hPrime hPositive hEm.
have [hCm [hAllB hNotA]]:=(analytic_reduction_E_membership
  (@analytic_reduction_actual_laws R X B hB n e he omega I) m g).1 hEm.
have hPrimeRot:=@analytic_rotated_germ_ideal_prime R X B hB n e he I g hPrime.
pose realG:=@AnalyticScalars.map R X NX hNX 0.
pose C:=@CommutativeIdealQuotient.space R G realG Ig hPrimeRot.1 hPrimeRot.2.1.
pose pi:=@CommutativeIdealQuotient.projection R G realG Ig hPrimeRot.1 hPrimeRot.2.1.
have hPi:=@CommutativeIdealQuotient.laws R G realG Ig hPrimeRot.1 hPrimeRot.2.1.
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
  @analytic_reduction_uniform_original_relations R X B hB n e he hON omega hDual
    I hPrime.1 hPrime.2.1 g C pi hPi m hMN hAllB L M inclusion hFraction eta phi hCoefficient
    P embed variable coefficient hP J hJ hPositive hNotA hCm.
have [F [hGenerated [hFI hPower]]]:=@analytic_reduction_equation_ideal_power R X B hB n e he hON omega hDual
  I hPrime.1 hPrime.2.1 g C pi hPi m hMN hAllB L inclusion hFraction P embed variable coefficient hP J hJ
  W k delta T first hFirst hK hDistinguished hKernel hDeltaOutside hRelations.
pose K:=@GeneratedCommutativeIdeal.value G (Ig `|` [set alpha|alpha = E delta]).
have hKGenerated:=@GeneratedCommutativeIdeal.laws G (Ig `|` [set alpha|alpha = E delta]).
have hNoetherian:=@finite_analytic_germ_ring_noetherian R X NX hNX n e 0 he.
pose hIg:=hNoetherian Ig hPrimeRot.1.
pose hF:=hNoetherian F (generated_commutative_ideal_laws hGenerated).
pose hKFinite:=hNoetherian K (generated_commutative_ideal_laws hKGenerated).
have hLarger:=@analytic_reduction_proper_ideal_coefficient R X B hB n e he hON omega hDual
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
exact:(@equation_saturation_variety_recovery R X NX hNX 0 Ig F K hIg hF hKFinite (E delta)
  hFI hPower hKGenerated).
Qed.
End OriginalEquations.
