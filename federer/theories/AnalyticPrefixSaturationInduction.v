(** Federer (1969), 3.4.8(10), p. 331:
    the original coordinate-prefix induction proves
    the delta-power assertion for every original
    ideal member. Apply original B_j preparation,
    the checked prefix division and the
    checked saturation division step. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthonormalFamilies GrassmannAbbreviations EuclideanInnerProduct OrthogonalGroupTopology
  AnalyticGermRing AnalyticCoordinateGermsSealed AnalyticRotatedGermIdeal AnalyticReductionActual
  AnalyticPrefixGermMap AnalyticPrefixGermSubring AnalyticPrefixGermSubringLaws
  AnalyticCoordinateSubringFamilyUP AnalyticCoordinateSubringFamilySealed AnalyticPrefixSubringMonotonicity
  AnalyticPrefixPreparedPolynomial AnalyticPrefixPolynomialDivision AnalyticFullPrefixGerms
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
Local Notation rotated:=(@analytic_rotated_germ_ideal R X B hB n e he I g).
Local Notation Q:=(@AnalyticCoordinateSubringFamily.value R X NX hNX n e he omega).
Local Notation gamma:=(fun j:'I_n=>@AnalyticCoordinateGerms.value R X NX hNX n e he omega j).
Variable m:'I_n.
Variables F S:set G.
Variable delta:G.
Variable D:comNzRingType.
Variable pi:{rmorphism G->D}.
Hypothesis hF:is_commutative_ideal F.
Hypothesis hSaturation:is_commutative_ideal_saturation F delta S.
Hypothesis hPi:is_commutative_ideal_quotient S pi.
Hypothesis hSI:S `<=` rotated.
Hypothesis hAllB:forall j:'I_n,(m<=j)%N ->@analytic_reduction_actual_B R X B hB n e he omega I j g.
Hypothesis hDelta:Q m delta.
Hypothesis hRelations:forall j:'I_n,(m<j)%N ->exists z:G,Q (m:nat).+1 z /\S (delta*gamma j-z).
Hypothesis hBase:forall alpha:G,rotated alpha ->Q (m:nat).+1 alpha ->S alpha.

(** Source for [analytic_coordinate_prefix_saturation_induction]:
    the original induction over Q_j in
    3.4.8(10), p. 331. The first
    prefix is supplied by the separately
    proved principal-kernel step. Every subsequent
    step applies actual original B_j preparation
    and analytic division; the final original
    prefix is the whole germ ring. *)
Theorem analytic_coordinate_prefix_saturation_induction:rotated `<=` S.
Proof.
have hFamily:=@AnalyticCoordinateSubringFamily.laws R X NX hNX n e he omega.
have hRotated:is_commutative_ideal rotated:=@analytic_rotated_germ_ideal_is_ideal R X B hB n e he I g hI.
pose Property:=fun p:nat=>forall (hPN:(p<=n)%N) (alpha:G),rotated alpha ->Q p alpha ->S alpha.
have hTower r:Property ((m:nat).+1+r)%N.
  elim:r=>[|r IH].
  - rewrite addn0 /Property=>hPN alpha hAlpha hPrefix.
    exact:(@hBase alpha hAlpha hPrefix).
  - rewrite addnS /Property=>hPN alpha hAlpha hPrefix.
    pose j:'I_n:=Ordinal hPN.
    pose hJN:=leq_trans (leqnSn (j:nat)) (ltn_ord j).
    pose A:=[the comNzRingType of (@analytic_germ_ring R (R_n R j)
      (inner_norm (@euclidean_inner_productP R j))
      (inner_norm_real_norm (@euclidean_inner_productP R j)) 0)].
    pose E:=@analytic_prefix_germ_map R X NX hNX n e he omega j hJN.
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
    have [_ [H [k [hK [hDistinguished hIn]]]]]:=@analytic_prefix_distinguished_ideal_polynomial
      R X B hB n e he omega hDual I g j P embed variable coefficient hP J hJ hI hProper hBJ.
    have [z [hZPrefix hRelation]]:=@hRelations j hMJ1.
    have hPrevious:forall x:G,rotated x ->Q j x ->S x.
      move=>x hX hQX;exact:(IH hJN x hX hQX).
    have hRing:is_commutative_subring (Q j).
      rewrite (analytic_coordinate_subring_family_member hFamily hJN).
      exact:(@analytic_prefix_germ_subring_laws R X NX hNX n e he omega j hJN).
    have hCoefficients a:Q j (E a).
      rewrite (analytic_coordinate_subring_family_member hFamily hJN).
      apply/analytic_prefix_germ_subring_membership;by exists a.
    have hDeltaPrevious:Q j delta.
      exact:(@analytic_coordinate_prefix_subring_monotone R X NX hNX n e he omega m j hMJ hJN delta hDelta).
    have hZPrevious:Q j z.
      exact:(@analytic_coordinate_prefix_subring_monotone R X NX hNX n e he omega (m:nat).+1 j hMJ1 hJN z hZPrefix).
    have hDivision:forall beta:G,Q (j:nat).+1 beta ->exists a:G,exists p:P,
        (forall i,(k<=i)%N ->coefficient p i = 0) /\beta = a*J H+J p.
      move=>beta hBeta.
      rewrite (analytic_coordinate_subring_family_member hFamily (ltn_ord j)) in hBeta.
      have [a [p [hSupport [hEquation _]]]]:=@analytic_prefix_distinguished_division
        R X B hB n e he omega j P embed variable coefficient hP J hJ H k hDistinguished hK beta hBeta.
      exists a,p;by split.
    exact:(@polynomial_saturation_division_step A P G D embed variable coefficient hP E (gamma j) J
      F rotated S (Q j) (Q (j:nat).+1) delta z pi H k hF hRotated hSaturation hPi hSI
      hRing hCoefficients hDeltaPrevious hZPrevious hPrevious hRelation hJ hIn hDivision alpha hAlpha hPrefix).
have hEnd:((m:nat).+1+(n-(m:nat).+1)=n)%N:=subnKC (ltn_ord m).
have hLast:=hTower (n-(m:nat).+1)%N;rewrite hEnd in hLast.
move=>alpha hAlpha.
have [beta hBeta]:=@analytic_full_prefix_germ_map_surjective R X B hB n e he hON omega hDual alpha.
have hFull:Q n alpha.
  rewrite (analytic_coordinate_subring_family_member hFamily (leqnn n)).
  apply/analytic_prefix_germ_subring_membership;by exists beta.
exact:(hLast (leqnn n) alpha hAlpha hFull).
Qed.
End PrefixInduction.
