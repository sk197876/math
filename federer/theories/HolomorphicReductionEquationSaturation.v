(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(10), p. 331:
    every original ideal member enters the
    finite equation ideal after multiplication by
    a positive power of the original delta.
    Assemble the checked original prefix induction
    using the opaque generated ideal and saturation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import FiniteCoordinates ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexOrderedBases HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup HolomorphicCoordinateNorm FieldCoordinateFunctional Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthonormalFamilies GrassmannAbbreviations EuclideanInnerProduct OrthogonalGroupTopology
  HolomorphicGermRing HolomorphicCoordinateGermsSealed HolomorphicPrefixGermMap HolomorphicRotatedGermIdeal
  HolomorphicReductionActual HolomorphicScalarsSealed HolomorphicPrefixGermSubring HolomorphicPrefixPolynomialSubring
  HolomorphicCoordinateSubringFamilyUP HolomorphicCoordinateSubringFamilySealed HolomorphicPrefixKernelPrincipal
  HolomorphicPrefixSaturationInduction OrdinalCoordinateTail
  CommutativeIdealUP CommutativeIdealSealed CommutativeQuotientUP CommutativeQuotientSealed
  CommutativeFactorizationUP FractionFieldUP CommutativeIdealSaturationUP CommutativeIdealSaturationSealed
  CommutativeIdealSaturationLaws CommutativeSaturationFieldKernel
  CommutativePolynomialUP CommutativePolynomialEvaluationUP PolynomialScalarComposition
  DistinguishedPolynomialUP HolomorphicGermValueSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section EquationSaturation.
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
Variable L:fieldType.
Variable inclusion:{rmorphism C->L}.
Hypothesis hFraction:is_commutative_fraction_field inclusion.

Variable P:comNzRingType.
Variable embed:{rmorphism A->P}.
Variable variable:P.
Variable coefficient:P->nat->A.
Hypothesis hP:is_commutative_polynomial_ring embed variable coefficient.
Variable J:{rmorphism P->G}.
Hypothesis hJ:is_commutative_polynomial_evaluation embed variable E (gamma m) J.


(** Source for [holomorphic_reduction_equation_ideal_power]:
    sigma in I_g implies delta^u sigma
    in the original equation ideal F for
    some positive u, 3.4.8(10), p. 331.
    The original polynomial kernel and coordinate
    relations have already been proved separately.
    This assembly assumes no saturation or
    variety-germ conclusion. *)
Theorem holomorphic_reduction_equation_ideal_power (W:P) k (delta:A)
  (T:'I_(n-m)->P) (first:'I_(n-m)):
  (first:nat) = 0%N ->(0<k)%N ->
  is_distinguished_polynomial coefficient
    (@HolomorphicGermValue.map R (coordinate_space (ComplexScalars.C R) m) (@holomorphic_coordinate_norm R m)
      (complex_norm_real (@holomorphic_coordinate_norm_laws R m)) 0) W k ->
  (forall H:P,@holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR I g (J H) <->commutative_divides W H) ->
  ~@holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR I g (E delta) ->
  (forall i:'I_(n-m),i<>first ->@holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR I g
    (E delta*gamma (ordinal_coordinate_tail_index hMN i)-J (T i))) ->
  exists F:set G,
    is_generated_commutative_ideal
      (fun alpha:G=>exists i:'I_(n-m),alpha = if i==first then J W else
        E delta*gamma (ordinal_coordinate_tail_index hMN i)-J (T i)) F /\
    F `<=` @holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR I g /\
    forall alpha:G,@holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR I g alpha ->
      exists u:nat,(0<u)%N /\F ((E delta)^+u*alpha).
Proof.
move=>hFirst hK hDistinguished hKernel hDeltaOutside hRelations.
pose rotated:=@holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR I g.
pose Q:=@HolomorphicCoordinateSubringFamily.value R X NX hNXR n e he omega.
pose equations:=fun i:'I_(n-m)=>if i==first then J W else
  E delta*gamma (ordinal_coordinate_tail_index hMN i)-J (T i).
pose generators:set G:=fun alpha=>exists i,alpha = equations i.
pose F:=@GeneratedCommutativeIdeal.value G generators.
have hGenerated:=@GeneratedCommutativeIdeal.laws G generators.
have hFIdeal:=generated_commutative_ideal_laws hGenerated.
have hRotated:is_commutative_ideal rotated:=@holomorphic_rotated_germ_ideal_is_ideal R X Herm hHerm (n+n) eR heR I g hI.
have hWIn:rotated (J W).
  apply:(hKernel W).2;exists 1;by rewrite mul1r.
have hFI:F `<=` rotated.
  apply:(generated_commutative_ideal_minimal hGenerated hRotated)=>alpha [i ->].
  rewrite /equations;case hCase:(i==first);first exact:hWIn.
  apply:hRelations;move=>hEqual;by rewrite hEqual eqxx in hCase.
have hGenerator i:F (equations i).
  apply:(generated_commutative_ideal_contains hGenerated);by exists i.
have hWF:F (J W).
  have h:=hGenerator first;by rewrite /equations eqxx in h.
pose S:=@CommutativeIdealSaturation.value G F (E delta).
have hSaturation:=@CommutativeIdealSaturation.laws G F (E delta).
have hSIdeal:=@commutative_ideal_saturation_is_ideal G F (E delta) S hFIdeal hSaturation.
pose fieldMap:{rmorphism G->L}:=GRing.RMorphism.clone G L (inclusion \o pi) _.
have hDeltaNonzero:fieldMap (E delta)!=0.
  apply/eqP=>hZero;apply:hDeltaOutside;apply:(commutative_quotient_kernel hPi _).1.
  apply:(fraction_field_embedding_injective hFraction);change (fieldMap (E delta) = inclusion 0).
  by rewrite hZero rmorph0.
have hFKernel alpha:F alpha ->fieldMap alpha = 0.
  move=>hMember;change (inclusion (pi alpha) = 0).
  by rewrite (commutative_quotient_kernel hPi _).2 //;[exact:rmorph0|exact:hFI _ hMember].
have hSField:=@commutative_saturation_field_kernel G L fieldMap F S (E delta)
  hSaturation hFKernel hDeltaNonzero.
have hSI:S `<=` rotated.
  move=>alpha hMember;apply:(commutative_quotient_kernel hPi _).1.
  apply:(fraction_field_embedding_injective hFraction);change (fieldMap alpha = inclusion 0).
  by rewrite hSField // rmorph0.
have hSProper:~S 1.
  move=>hOne;apply:(@holomorphic_rotated_germ_ideal_proper R X Herm hHerm (n+n) eR heR I g hProper).
  exact:hSI _ hOne.
pose realScalar:=@HolomorphicScalars.map R X NX hNXR 0.
pose D:=@CommutativeIdealQuotient.space (ComplexScalars.C R) G realScalar S hSIdeal hSProper.
pose rho:=@CommutativeIdealQuotient.projection (ComplexScalars.C R) G realScalar S hSIdeal hSProper.
have hRho:=@CommutativeIdealQuotient.laws (ComplexScalars.C R) G realScalar S hSIdeal hSProper.
have hContains:=@commutative_ideal_saturation_contains G F (E delta) S hSaturation.
have hWS:S (J W):=hContains _ hWF.
pose bound:=leq_trans (leqnSn (m:nat)) (ltn_ord m).
have hJBound:is_commutative_polynomial_evaluation embed variable
    (@holomorphic_prefix_germ_map R X NX hNXR n e he omega m bound) (gamma m) J.
  apply:(polynomial_evaluation_change_parameters hJ).
  - move=>a;by rewrite (bool_irrelevance hMN bound).
  - by [].
have hFamily:=@HolomorphicCoordinateSubringFamily.laws R X NX hNXR n e he omega.
have hBase:forall alpha:G,rotated alpha ->Q (m:nat).+1 alpha ->S alpha.
  move=>alpha hAlpha hPrefix.
  rewrite /Q (holomorphic_coordinate_subring_family_member hFamily (ltn_ord m)) in hPrefix.
  have [a [_ hA]]:=@holomorphic_prefix_polynomial_kernel_principal R X Herm hHerm n e he omega m
    P embed variable coefficient hP J hJBound rotated W k hRotated hDistinguished hK hKernel alpha hAlpha hPrefix.
  rewrite hA;exact:(@commutative_ideal_mul G S hSIdeal a (J W) hWS).
have hDeltaPrefix:Q m (E delta).
  rewrite /Q (holomorphic_coordinate_subring_family_member hFamily hMN).
  apply/holomorphic_prefix_germ_subring_membership;by exists delta.
have hSuffixRelations:forall j:'I_n,(m<j)%N ->exists z:G,Q (m:nat).+1 z /\S (E delta*gamma j-z).
  move=>j hStrict.
  have [i hIndex]:=@ordinal_coordinate_tail_complete n m hMN j (ltnW hStrict).
  have hOther:i<>first.
    move=>hEqual.
    have hValue:=congr1 (fun t:'I_n=>(t:nat)) hIndex.
    rewrite hEqual ordinal_coordinate_tail_value hFirst addn0 in hValue.
    by rewrite -hValue ltnn in hStrict.
  have hDifferent:(i==first) = false by apply/negP=>/eqP hEqual;exact:hOther hEqual.
  exists (J (T i));split.
  - rewrite /Q (holomorphic_coordinate_subring_family_member hFamily (ltn_ord m)).
    exact:(@holomorphic_prefix_polynomial_member R X NX hNX n e he omega m P embed variable coefficient hP J hJBound (T i)).
  - have h:=hContains _ (hGenerator i).
    by rewrite /equations hDifferent hIndex in h.
have hAllInS:=@holomorphic_coordinate_prefix_saturation_induction R X Herm hHerm n e he omega hDual I hI hProper
  g m F S (E delta) D rho hFIdeal hSaturation hRho hSI hAllB hDeltaPrefix hSuffixRelations hBase.
exists F;split;first exact:hGenerated.
split;first exact:hFI.
move=>alpha hAlpha.
exact:(@commutative_ideal_saturation_positive_power G F (E delta) S hFIdeal hSaturation alpha (hAllInS alpha hAlpha)).
Qed.
End EquationSaturation.
