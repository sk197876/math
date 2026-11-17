(** Supporting Federer (1969), 3.4.8(5), p. 328:
    finite original prefix actions on one original quotient.
    Use the existing finite quotient and faithful-prefix theorems;
    actual pointed pullbacks preserve constants and centre values. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness LinearBasis
  OrthonormalFamilies GrassmannAbbreviations EuclideanInnerProduct OrthogonalGroupTopology
  AnalyticGermUP AnalyticGermRing AnalyticScalarsSealed AnalyticGermValueSealed AnalyticVanishingIdealSealed
  AnalyticPrefixCoordinatesSealed AnalyticPrefixGermMap AnalyticPrefixGermMapLaws AnalyticPrefixRealScalars PointedAnalyticPullbackValue
  AnalyticRotatedGermIdeal AnalyticReductionActual AnalyticReductionFiniteQuotient
  AnalyticReductionFaithfulPrefix CommutativeIdealUP CommutativeQuotientUP
  RingScalarRestriction RingSubmoduleUP AnalyticOriginalQuotientRotation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Actions.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Variable hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Variable hON:orthonormal_family B e.
Variable omega:'I_n->Hom X R^o.
Hypothesis hDual:forall i k,omega i (e k) = if i==k then 1 else 0.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Local Notation O:=(@orthogonal_group R X B hB n e he).
Local Notation constants:=(@AnalyticScalars.map R X NX hNX 0).
Local Notation M:=(@AnalyticVanishingIdeal.value R X NX hNX 0).
Variable I:set G.
Hypothesis hI:is_commutative_ideal I.
Hypothesis hProper:~I 1.
Variable C:comNzRingType.
Variable pi:{rmorphism G->C}.
Hypothesis hPi:is_commutative_ideal_quotient I pi.

(** Source for [analytic_original_finite_coefficient_action]: supporting
    the arbitrary-ideal coefficient comparison in Federer 3.4.8(5),
    p. 328. All original prefix actions on O/I use actual inverse
    rotations, have the same scalar constants, preserve the maximal
    ideal image and are finite under the original B-tail. Not-A
    gives faithfulness only at its original positive interior index. *)
Theorem analytic_original_finite_coefficient_action (g:O) m (hMN:(m<=n)%N):
  (forall j:'I_n,(m<=j)%N ->@analytic_reduction_actual_B R X B hB n e he omega I j g) ->
  exists phi:{rmorphism [the comNzRingType of (@analytic_germ_ring R (R_n R m)
      (inner_norm (@euclidean_inner_productP R m)) (inner_norm_real_norm (@euclidean_inner_productP R m)) 0)]->C},
    is_finitely_generated_ring_submodule
      (setT:set [the lmodType [the comNzRingType of (@analytic_germ_ring R (R_n R m)
        (inner_norm (@euclidean_inner_productP R m)) (inner_norm_real_norm (@euclidean_inner_productP R m)) 0)] of
        ring_restricted_space phi C^o]) /\
    (forall c:R,phi (@AnalyticScalars.map R (R_n R m)
      (inner_norm (@euclidean_inner_productP R m)) (inner_norm_real_norm (@euclidean_inner_productP R m)) 0 c) = pi (constants c)) /\
    (forall alpha,@AnalyticVanishingIdeal.value R (R_n R m)
      (inner_norm (@euclidean_inner_productP R m)) (inner_norm_real_norm (@euclidean_inner_productP R m)) 0 alpha ->
      (pi @` M) (phi alpha)) /\
    (forall hLess:(m<n)%N,(0<m)%N ->
      ~@analytic_reduction_actual_A R X B hB n e he omega I (@Ordinal n.+1 m hMN) g ->injective phi).
Proof.
move=>hTail.
have [rho [hRho [hConstants hMaximal]]]:=@analytic_original_quotient_rotation R X B hB n e he I C pi hPi g.
pose A:=[the comNzRingType of (@analytic_germ_ring R (R_n R m)
  (inner_norm (@euclidean_inner_productP R m)) (inner_norm_real_norm (@euclidean_inner_productP R m)) 0)].
pose E:=@analytic_prefix_germ_map R X NX hNX n e he omega m hMN.
pose phi:=GRing.RMorphism.clone A C (rho \o E) _.
exists phi;split.
- exact:(@analytic_reduction_finite_original_quotient R X B hB n e he hON omega hDual
    I g C rho m hMN hI hProper hRho hTail).
- split.
  + move=>c;change (rho (E (@AnalyticScalars.map R (R_n R m)
      (inner_norm (@euclidean_inner_productP R m)) (inner_norm_real_norm (@euclidean_inner_productP R m)) 0 c)) =
      pi (constants c)).
    by rewrite (@analytic_prefix_real_scalar_triangle R X NX hNX n e he omega m hMN c) hConstants.
  + split.
    * move=>alpha hAlpha;apply:hMaximal.
      apply/(@AnalyticVanishingIdeal.laws R X NX hNX 0).
      rewrite (@pointed_analytic_pullback_centre_value R X (R_n R m) NX
        (inner_norm (@euclidean_inner_productP R m)) hNX
        (inner_norm_real_norm (@euclidean_inner_productP R m)) 0 0
        (@AnalyticPrefixCoordinates.projection R X n omega m hMN) E
        (@analytic_prefix_germ_map_specification R X NX hNX n e he omega m hMN)
        (@analytic_prefix_projection_zero R X n omega m hMN)).
      exact:(@AnalyticVanishingIdeal.laws R (R_n R m)
        (inner_norm (@euclidean_inner_productP R m)) (inner_norm_real_norm (@euclidean_inner_productP R m)) 0 alpha).1 hAlpha.
    * move=>hLess hPositive hNotA.
      pose j:'I_n:=Ordinal hLess.
      have hIndex:widen_ord (leqnSn n) j = @Ordinal n.+1 m hMN by apply:val_inj.
      have hNot:~@analytic_reduction_actual_A R X B hB n e he omega I (widen_ord (leqnSn n) j) g.
        by rewrite hIndex.
      exact:(@analytic_reduction_not_A_faithful_prefix R X B hB n e he omega hDual I g C rho j hMN
        hRho hPositive hNot).
Qed.
End Actions.
