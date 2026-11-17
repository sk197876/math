(** Federer (1969), 3.4.8(10), p. 331:
    the original equations and derivative inverse
    have one original coefficient denominator and
    bounded polynomial numerators. Apply the
    proved original primitive and separable data
    and uniform field representatives. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis FiniteCoordinates OrthonormalFamilies GrassmannAbbreviations EuclideanInnerProduct OrthogonalGroupTopology
  AnalyticGermRing AnalyticGermFactorization AnalyticCoordinateGermsSealed AnalyticPrefixGermMap
  AnalyticRotatedGermIdeal AnalyticReductionActual AnalyticReductionFieldInputs AnalyticReductionFaithfulPrefix
  CommutativeIdealUP CommutativeQuotientUP CommutativeFactorizationUP FractionFieldUP
  CoefficientFractionFieldUP CoefficientFaithfulFractionField IntegralRingElementUP
  CommutativePolynomialUP CommutativePolynomialMonicUP CommutativePolynomialSealed
  CommutativePolynomialEvaluationUP CommutativePolynomialEvaluationSealed PolynomialScalarComposition
  PolynomialCoefficientMapUP PolynomialCoefficientMapSealed IntegralMinimalPolynomialDescent FieldPolynomialMinimumUP AnalyticReductionSeparablePolynomial AnalyticReductionCPrimitive
  PrimitiveFieldUniformRepresentative FormalPolynomialDerivativeUP FormalPolynomialDerivativeSealed
  DistinguishedPolynomialUP AnalyticGermValueSealed OrdinalCoordinateTail
  AnalyticCoordinateSubringFamilyUP AnalyticCoordinateSubringFamilySealed AnalyticPrefixGermSubring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section UniformOriginal.
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
Variable I:set G.
Hypothesis hI:is_commutative_ideal I.
Hypothesis hProper:~I 1.
Variable g:@orthogonal_group R X B hB n e he.
Variable C:comNzRingType.
Variable pi:{rmorphism G->C}.
Hypothesis hPi:is_commutative_ideal_quotient (@analytic_rotated_germ_ideal R X B hB n e he I g) pi.
Variable m:'I_n.
Hypothesis hMN:((m:nat)<=n)%N.
Hypothesis hAllB:forall j:'I_n,(m<=j)%N ->@analytic_reduction_actual_B R X B hB n e he omega I j g.
Local Notation A:=[the comNzRingType of (@analytic_germ_ring R (R_n R m)
  (inner_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R m)) 0)].
Local Notation A1:=[the comNzRingType of (@analytic_germ_ring R (R_n R (m:nat).+1)
  (inner_norm (@euclidean_inner_productP R (m:nat).+1))
  (inner_norm_real_norm (@euclidean_inner_productP R (m:nat).+1)) 0)].
Local Notation E:=(@analytic_prefix_germ_map R X NX hNX n e he omega m hMN).
Local Notation E1:=(@analytic_prefix_germ_map R X NX hNX n e he omega (m:nat).+1 (ltn_ord m)).
Local Notation scalar:=(GRing.RMorphism.clone A C (pi \o E) _).
Local Notation gamma:=(fun j:'I_n=>@AnalyticCoordinateGerms.value R X NX hNX n e he omega j).
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


(** Source for [analytic_reduction_uniform_original_relations]:
    the original common delta, bounded
    numerators and derivative-inverse identity,
    3.4.8(10), p. 331. The first
    suffix index is the original next
    coordinate; subsequent indices retain exactly
    the original remaining coordinates. Every
    ideal relation and nonzero denominator is proved. *)
Theorem analytic_reduction_uniform_original_relations:
  (0<m)%N ->~@analytic_reduction_actual_A R X B hB n e he omega I (widen_ord (leqnSn n) m) g ->
  @analytic_reduction_actual_C R X B hB n e he omega I m g ->
  exists (W derivative:P) k (delta:A) (T:'I_(n-m)->P) (first:'I_(n-m)),
    (first:nat) = 0%N /\(0<k)%N /\
    is_distinguished_polynomial coefficient
      (@AnalyticGermValue.map R (R_n R m) (inner_norm (@euclidean_inner_productP R m))
        (inner_norm_real_norm (@euclidean_inner_productP R m)) 0) W k /\
    (forall H:P,@analytic_rotated_germ_ideal R X B hB n e he I g (J H) <->commutative_divides W H) /\
    is_formal_polynomial_derivative coefficient W derivative /\
    ~@analytic_rotated_germ_ideal R X B hB n e he I g (J derivative) /\
    @AnalyticCoordinateSubringFamily.value R X NX hNX n e he omega m (E delta) /\
    ~@analytic_rotated_germ_ideal R X B hB n e he I g (E delta) /\
    (forall i j,(k<=j)%N ->coefficient (T i) j = 0) /\
    @analytic_rotated_germ_ideal R X B hB n e he I g (J derivative*J (T first)-E delta) /\
    (forall i:'I_(n-m),i<>first ->@analytic_rotated_germ_ideal R X B hB n e he I g
      (E delta*gamma (ordinal_coordinate_tail_index hMN i)-J (T i))).
Proof.
move=>hPositive hNotA hC.
have [W [k [hK [hDistinguished [hKernel hDerivativeOutside]]]]]:=@analytic_reduction_separable_original_polynomial
  R X B hB n e he hON omega hDual I hI hProper g C pi hPi m hMN hAllB
  L M inclusion hFraction eta phi hCoefficient P embed variable coefficient hP J hJ hPositive hNotA.
pose derivative:=@FormalPolynomialDerivative.value A P embed variable coefficient hP W.
have hDerivative:=@FormalPolynomialDerivative.laws A P embed variable coefficient hP W.
have hOutside:=hDerivativeOutside derivative hDerivative.
have hPrimitive:=@analytic_reduction_C_next_coordinate_primitive R X B hB n e he hON omega hDual
  I hI hProper g C pi hPi m hMN hAllB L M inclusion hFraction eta phi hCoefficient hC.
pose chi:{rmorphism A->L}:=GRing.RMorphism.clone A L (inclusion \o scalar) _.
pose EJ:{rmorphism P->C}:=GRing.RMorphism.clone P C (pi \o J) _.
pose EL:{rmorphism P->L}:=GRing.RMorphism.clone P L (inclusion \o EJ) _.
have hEJ:=@polynomial_evaluation_after_ring_map A P G C embed variable E (gamma m) J pi hJ.
have hEL:=@polynomial_evaluation_after_ring_map A P C L embed variable scalar (pi (gamma m)) EJ inclusion hEJ.
have hFaithful:=@analytic_reduction_not_A_faithful_prefix R X B hB n e he omega hDual
  I g C pi m hMN hPi hPositive hNotA.
have hChi:injective chi.
  move=>a b hEqual;apply:hFaithful;apply:(fraction_field_embedding_injective hFraction);exact:hEqual.
have hField:=@faithful_coefficient_fraction_field A L M chi eta phi hCoefficient hChi.
have hDomain:=(@finite_analytic_germ_ring_factorization R (R_n R m)
  (inner_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R m)) m (@coordinate_basis R m) 0 (@coordinate_basisP R m)).1.
have hInW:@analytic_rotated_germ_ideal R X B hB n e he I g (J W).
  apply:(hKernel W).2;exists 1;by rewrite mul1r.
have hZero:EL W = 0.
  change (inclusion (pi (J W)) = 0);by rewrite (commutative_quotient_kernel hPi _).2 // rmorph0.
have hNonzero:inclusion (pi (J derivative))!=0.
  apply/eqP=>hZeroDerivative;apply:hOutside;apply:(commutative_quotient_kernel hPi _).1.
  apply:(fraction_field_embedding_injective hFraction);by rewrite hZeroDerivative rmorph0.
have hSuffixPositive:(0<n-m)%N by rewrite subn_gt0;exact:ltn_ord m.
pose first:'I_(n-m):=Ordinal hSuffixPositive.
pose x:=fun i:'I_(n-m)=>if i==first then (inclusion (pi (J derivative)))^-1
  else inclusion (pi (gamma (ordinal_coordinate_tail_index hMN i))).
have [delta [hDelta hNumerators]]:=@primitive_field_uniform_original_representatives A P L M
  embed variable coefficient hP hDomain chi eta phi (inclusion (pi (gamma m))) EL W k
  hCoefficient hField hEL hPrimitive hDistinguished.1 hZero (n-m)%N x.
have [T hT]:=choice hNumerators.
have hFirstValue:chi delta*(inclusion (pi (J derivative)))^-1 = EL (T first).
  have h:= (hT first).2;by rewrite /x eqxx in h.
have hProduct:inclusion (pi (J derivative))*EL (T first) = chi delta.
  by rewrite -hFirstValue mulrCA (mulfV hNonzero) mulr1.
have hFirstRelation:@analytic_rotated_germ_ideal R X B hB n e he I g
    (J derivative*J (T first)-E delta).
  apply:(commutative_quotient_kernel hPi _).1;apply:(fraction_field_embedding_injective hFraction).
  rewrite rmorph0 !rmorphB !rmorphM.
  change (inclusion (pi (J derivative))*EL (T first)-chi delta = 0);by rewrite hProduct subrr.
have hOther i (hOther:i<>first):@analytic_rotated_germ_ideal R X B hB n e he I g
    (E delta*gamma (ordinal_coordinate_tail_index hMN i)-J (T i)).
  have hDifferent:(i==first) = false by apply/negP=>/eqP hEqual;exact:hOther hEqual.
  have hValue:chi delta*inclusion (pi (gamma (ordinal_coordinate_tail_index hMN i))) = EL (T i).
    have h:=(hT i).2;by rewrite /x hDifferent in h.
  apply:(commutative_quotient_kernel hPi _).1;apply:(fraction_field_embedding_injective hFraction).
  rewrite rmorph0 !rmorphB !rmorphM.
  change (chi delta*inclusion (pi (gamma (ordinal_coordinate_tail_index hMN i)))-EL (T i) = 0).
  by rewrite hValue subrr.
have hDeltaOutside:~@analytic_rotated_germ_ideal R X B hB n e he I g (E delta).
  move=>hIn.
  have hZeroDelta:pi (E delta) = 0:=(commutative_quotient_kernel hPi _).2 hIn.
  have hFieldZero:phi (eta delta) = 0.
    rewrite (coefficient_fraction_scalar_triangle hCoefficient delta).
    change (inclusion (pi (E delta)) = 0);by rewrite hZeroDelta rmorph0.
  apply:hDelta;apply:(fmorph_inj phi);by rewrite hFieldZero rmorph0.
have hDeltaPrefix:@AnalyticCoordinateSubringFamily.value R X NX hNX n e he omega m (E delta).
  have hQ:=@AnalyticCoordinateSubringFamily.laws R X NX hNX n e he omega.
  rewrite (analytic_coordinate_subring_family_member hQ hMN).
  apply/analytic_prefix_germ_subring_membership;by exists delta.
exists W,derivative,k,delta,T,first;split;first by [].
split;first exact:hK.
split;first exact:hDistinguished.
split;first exact:hKernel.
split;first exact:hDerivative.
split;first exact:hOutside.
split;first exact:hDeltaPrefix.
split;first exact:hDeltaOutside.
split;first by move=>i;exact:(hT i).1.
by split.
Qed.
End UniformOriginal.
