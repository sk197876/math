(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(10), p. 331:
    the original coordinate-prefix induction proves
    the delta-power assertion for every original
    ideal member. Apply original B_j preparation,
    the checked prefix division and the
    checked saturation division step. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import FiniteCoordinates ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexOrderedBases HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup HolomorphicCoordinateNorm FieldCoordinateFunctional Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthonormalFamilies GrassmannAbbreviations EuclideanInnerProduct OrthogonalGroupTopology
  HolomorphicGermRing HolomorphicCoordinateGermsSealed HolomorphicRotatedGermIdeal HolomorphicReductionActual
  HolomorphicPrefixGermMap HolomorphicPrefixGermSubring HolomorphicPrefixGermSubringLaws
  HolomorphicCoordinateSubringFamilyUP HolomorphicCoordinateSubringFamilySealed HolomorphicPrefixSubringMonotonicity
  HolomorphicPrefixPreparedPolynomial HolomorphicPrefixPolynomialDivision HolomorphicFullPrefixGerms
  CommutativeIdealUP CommutativeQuotientUP CommutativeSubringUP CommutativeIdealSaturationUP
  CommutativePolynomialSealed CommutativePolynomialEvaluationSealed PolynomialSaturationDivisionStep.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section PrefixInduction.
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
Local Notation rotated:=(@holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR I g).
Local Notation Q:=(@HolomorphicCoordinateSubringFamily.value R X NX hNXR n e he omega).
Local Notation gamma:=(fun j:'I_n=>@HolomorphicCoordinateGerms.value R X NX hNX n e he omega j).
Variable m:'I_n.
Variables F S:set G.
Variable delta:G.
Variable D:comNzRingType.
Variable pi:{rmorphism G->D}.
Hypothesis hF:is_commutative_ideal F.
Hypothesis hSaturation:is_commutative_ideal_saturation F delta S.
Hypothesis hPi:is_commutative_ideal_quotient S pi.
Hypothesis hSI:S `<=` rotated.
Hypothesis hAllB:forall j:'I_n,(m<=j)%N ->@holomorphic_reduction_actual_B R X Herm hHerm n e he omega I j g.
Hypothesis hDelta:Q m delta.
Hypothesis hRelations:forall j:'I_n,(m<j)%N ->exists z:G,Q (m:nat).+1 z /\S (delta*gamma j-z).
Hypothesis hBase:forall alpha:G,rotated alpha ->Q (m:nat).+1 alpha ->S alpha.

(** Source for [holomorphic_coordinate_prefix_saturation_induction]:
    the original induction over Q_j in
    3.4.8(10), p. 331. The first
    prefix is supplied by the separately
    proved principal-kernel step. Every subsequent
    step applies actual original B_j preparation
    and holomorphic division; the final original
    prefix is the whole germ ring. *)
Theorem holomorphic_coordinate_prefix_saturation_induction:rotated `<=` S.
Proof.
have hFamily:=@HolomorphicCoordinateSubringFamily.laws R X NX hNXR n e he omega.
have hRotated:is_commutative_ideal rotated:=@holomorphic_rotated_germ_ideal_is_ideal R X Herm hHerm (n+n) eR heR I g hI.
pose Property:=fun p:nat=>forall (hPN:(p<=n)%N) (alpha:G),rotated alpha ->Q p alpha ->S alpha.
have hTower r:Property ((m:nat).+1+r)%N.
  elim:r=>[|r IH].
  - rewrite addn0 /Property=>hPN alpha hAlpha hPrefix.
    exact:(@hBase alpha hAlpha hPrefix).
  - rewrite addnS /Property=>hPN alpha hAlpha hPrefix.
    pose j:'I_n:=Ordinal hPN.
    pose hJN:=leq_trans (leqnSn (j:nat)) (ltn_ord j).
    pose A:=[the comNzRingType of (@holomorphic_germ_ring R (coordinate_space (ComplexScalars.C R) j)
      (@holomorphic_coordinate_norm R j)
      (complex_norm_real (@holomorphic_coordinate_norm_laws R j)) 0)].
    pose E:=@holomorphic_prefix_germ_map R X NX hNXR n e he omega j hJN.
    pose P:=CommutativePolynomial.space A.
    pose embed:=CommutativePolynomial.embed A.
    pose variable:=CommutativePolynomial.variable A.
    pose coefficient:=@CommutativePolynomial.coefficient A.
    have hP:=CommutativePolynomial.laws A.
    pose J:=@CommutativePolynomialEvaluation.map A P G embed variable coefficient hP E (gamma j).
    have hJ:=@CommutativePolynomialEvaluation.laws A P G embed variable coefficient hP E (gamma j).
    have hMJ1:((m:nat).+1<=j)%N by rewrite /j /= leq_addr.
    have hMJ:(m<=j)%N:=leq_trans (leqnSn (m:nat)) hMJ1.
    have hBJ:=@hAllB j hMJ.
    have [_ [H [k [hK [hDistinguished hIn]]]]]:=@holomorphic_prefix_distinguished_ideal_polynomial
      R X Herm hHerm n e he omega hDual I g j P embed variable coefficient hP J hJ hI hProper hBJ.
    have [z [hZPrefix hRelation]]:=@hRelations j hMJ1.
    have hPrevious:forall x:G,rotated x ->Q j x ->S x.
      move=>x hX hQX;exact:(IH hJN x hX hQX).
    have hRing:is_commutative_subring (Q j).
      rewrite (holomorphic_coordinate_subring_family_member hFamily hJN).
      exact:(@holomorphic_prefix_germ_subring_laws R X NX hNXR n e he omega j hJN).
    have hCoefficients a:Q j (E a).
      rewrite (holomorphic_coordinate_subring_family_member hFamily hJN).
      apply/holomorphic_prefix_germ_subring_membership;by exists a.
    have hDeltaPrevious:Q j delta.
      exact:(@holomorphic_coordinate_prefix_subring_monotone R X NX hNX n e he omega m j hMJ hJN delta hDelta).
    have hZPrevious:Q j z.
      exact:(@holomorphic_coordinate_prefix_subring_monotone R X NX hNX n e he omega (m:nat).+1 j hMJ1 hJN z hZPrefix).
    have hDivision:forall beta:G,Q (j:nat).+1 beta ->exists a:G,exists p:P,
        (forall i,(k<=i)%N ->coefficient p i = 0) /\beta = a*J H+J p.
      move=>beta hBeta.
      rewrite (holomorphic_coordinate_subring_family_member hFamily (ltn_ord j)) in hBeta.
      have [a [p [hSupport [hEquation _]]]]:=@holomorphic_prefix_distinguished_division
        R X Herm hHerm n e he omega j P embed variable coefficient hP J hJ H k hDistinguished hK beta hBeta.
      exists a,p;by split.
    exact:(@polynomial_saturation_division_step A P G D embed variable coefficient hP E (gamma j) J
      F rotated S (Q j) (Q (j:nat).+1) delta z pi H k hF hRotated hSaturation hPi hSI
      hRing hCoefficients hDeltaPrevious hZPrevious hPrevious hRelation hJ hIn hDivision alpha hAlpha hPrefix).
have hEnd:((m:nat).+1+(n-(m:nat).+1)=n)%N:=subnKC (ltn_ord m).
have hLast:=hTower (n-(m:nat).+1)%N;rewrite hEnd in hLast.
move=>alpha hAlpha.
have [beta hBeta]:=@holomorphic_full_prefix_germ_map_surjective R X NX hNXR n e he omega hDual alpha.
have hFull:Q n alpha.
  rewrite (holomorphic_coordinate_subring_family_member hFamily (leqnn n)).
  apply/holomorphic_prefix_germ_subring_membership;by exists beta.
exact:(hLast (leqnn n) alpha hAlpha hFull).
Qed.
End PrefixInduction.
