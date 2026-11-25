(** Federer (1969), 3.4.8(15), pp. 328, 337:
    a proper nonempty irreducible subgerm of an irreducible
    analytic germ has strictly smaller dimension. The original
    prime-model larger-ideal assertion contradicts a common E_m
    rotation if the dimensions agree. Both endpoints remain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions cardinality reals
  constructive_ereal topology subtype_topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
  EuclideanInnerProduct EuclideanStiefelInnerSplitting InnerNorm InnerMetric HomInner HilbertFormCompactness
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology LinearGroupSealed IsotropyGroupTopology
  HaarIntegralUP CompactGroupHaarNormalisation MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostPositiveWitness
  SetGermUP SetGermOrder AnalyticGermRing CommutativeIdealUP GermVanishingSealed GermVanishingIdeal GermVanishingMonotonicity
  AnalyticIrreducibleGermUP AnalyticIrreducibleProperPrime AnalyticDepthSealed AnalyticReductionDepthUP
  AnalyticReductionActual AnalyticReductionLociUP AnalyticDepthReductionAlmost AnalyticIdealDepthMonotonicity
  AnalyticZeroDepthPointGerm AnalyticFullDimensionWholeGerm AnalyticProperSubgermIdeal
  AnalyticRotatedGermIdeal AnalyticRotatedStrictIdeal AnalyticPrimeLocalModelUP Federer348PrimeReduction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section StrictDrop.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation B:=(@euclidean_inner_product R n).
Local Notation hB:=(@euclidean_inner_productP R n).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation G:=(@set_germ_space T 0).
Local Notation A:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Local Notation e:=(@coordinate_basis R n).
Local Notation he:=(@coordinate_basisP R n).
Local Notation omega:=(dual_basis he).
Local Notation O:=(@orthogonal_group R X B hB n e he).
Local Notation ideal:=(@AnalyticSetIdeal.value R X NX hNX 0).
Local Notation depth:=(@AnalyticDepth.value R X B hB n e he omega).

(** Source for [analytic_irreducible_strict_subgerm_depth_drop]: the
    irreducible beta case of original 3.4.8(15),
    p. 337. Every model and common generic
    coordinate system is derived from the original germs. *)
Theorem analytic_irreducible_strict_subgerm_depth_drop (alpha beta:G):
  @is_nonempty_irreducible_analytic_germ R X NX hNX 0 alpha ->
  @is_nonempty_irreducible_analytic_germ R X NX hNX 0 beta ->
  set_germ_subset beta alpha ->alpha<>beta ->
  (depth (ideal beta)<depth (ideal alpha))%N.
Proof.
move=>hAlpha hBeta hSub hDifferent.
have hMono:=@analytic_variety_ideal_depth_monotone R X B hB n e he omega beta alpha hSub.
rewrite ltn_neqAle hMono andbT;apply/negP=>/eqP hEqual.
have hDual i j:omega i (e j)=if i==j then 1 else 0 by rewrite dual_basisE eq_sym.
case:(posnP (depth (ideal alpha)))=>[hZero|hPositive].
- have hAlphaPoint:=@analytic_zero_depth_point_germ R X B hB n e he omega hDual alpha hAlpha.1.1 hAlpha.2 hZero.
  have hBetaZero:depth (ideal beta)=0%N by rewrite hEqual.
  have hBetaPoint:=@analytic_zero_depth_point_germ R X B hB n e he omega hDual beta hBeta.1.1 hBeta.2 hBetaZero.
  apply:hDifferent;exact:eq_trans hAlphaPoint (esym hBetaPoint).
- case:(ltnP (depth (ideal alpha)) n)=>hMN.
  + pose m:'I_n:=Ordinal hMN.
    pose I:=ideal alpha;pose J:=ideal beta.
    have hPrimeI:=(@analytic_irreducible_proper_prime_equivalence R X NX hNX 0 alpha hAlpha.1.1).1 hAlpha.
    have hPrimeJ:=(@analytic_irreducible_proper_prime_equivalence R X NX hNX 0 beta hBeta.1.1).1 hBeta.
    have [mulO [invO [unitO hO]]]:=@orthogonal_group_restriction_exists R X B hB n e he.
    have [theta hTheta]:=@orthogonal_normalised_haar_measure_exists R X B hB n e he mulO invO unitO hO.
    have hAlmostI:=@analytic_depth_reduction_haar_almost R n I hPrimeI (ex_intro _ alpha erefl)
      mulO invO unitO hO (widen_ord (leqnSn n) m) theta erefl hTheta.
    have hAlmostJ:=@analytic_depth_reduction_haar_almost R n J hPrimeJ (ex_intro _ beta erefl)
      mulO invO unitO hO (widen_ord (leqnSn n) m) theta hEqual hTheta.
    have [lambda [hLambda hMeasure hRepresentation hRegular]]:=hTheta.1.
    have hMass:theta setT<>0%E.
      rewrite hTheta.2;move=>hE.
      have hOne:(1:R)=0:=EFin_inj hE.
      have hDifferentOne:(1:R)!=0 by rewrite oner_eq0.
      apply:(negP hDifferentOne);apply/eqP;exact:hOne.
    have [g [_ [hEmI hEmJ]]]:=measure_almost_positive_set_witness hMeasure hMass
      (measure_almost_everywhere_and hMeasure hAlmostI hAlmostJ).
    have hBound:(m<=n)%N:=ltnW (ltn_ord m).
    have [k [first [U [delta [coeff [f [Z [K [hI [hIg [hK [hModel hNonempty]]]]]]]]]]]]:=
      @federer_3_4_8_10 R n e he (@euclidean_coordinate_orthonormal_family R n) omega hDual
        I g m hBound hPrimeI hPositive hEmI.
    pose Ig:=@analytic_rotated_germ_ideal R X B hB n e he I g.
    pose Jg:=@analytic_rotated_germ_ideal R X B hB n e he J g.
    have hInclusion:I `<=` J:=@analytic_set_ideal_antitone R X NX hNX 0 beta alpha hSub.
    have hRotatedInclusion:=@analytic_rotated_ideal_inclusion R X B hB n e he I J g hInclusion.
    have hStrict:=@analytic_proper_subgerm_ideal_witness R X NX hNX 0 alpha beta hBeta.1.1 hSub hDifferent.
    have hRotatedStrict:=@analytic_rotated_strict_ideal_witness R X B hB n e he I J g hStrict.
    have hJg:=@analytic_rotated_germ_ideal_is_ideal R X B hB n e he J g hPrimeJ.1.
    have hFields:=hModel;do 19 (case:hFields=>_ hFields).
    have [phi [hPhi [hQ [hOutside hNonzero]]]]:=hFields Jg hJg hRotatedInclusion hRotatedStrict.
    have hLociJ:=@analytic_reduction_actual_laws R X B hB n e he omega J.
    have hNotA:=((analytic_reduction_E_membership hLociJ m g).1 hEmJ).2.2.
    apply:hNotA;apply:(analytic_reduction_A_membership hLociJ (widen_ord (leqnSn n) m) g).2.
    split;first exact:hPositive.
    exists phi;split;first exact:hPhi.
    by split.
  + have hBound:=analytic_reduction_depth_bound (@AnalyticDepth.laws R X B hB n e he omega (ideal alpha)).
    have hFull:depth (ideal alpha)=n by apply/eqP;rewrite eqn_leq hBound hMN.
    have hAlphaWhole:=@analytic_full_dimension_whole_germ R n alpha hAlpha.1.1 hAlpha.2 hFull.
    have hBetaFull:depth (ideal beta)=n by rewrite hEqual.
    have hBetaWhole:=@analytic_full_dimension_whole_germ R n beta hBeta.1.1 hBeta.2 hBetaFull.
    apply:hDifferent;exact:eq_trans hAlphaWhole (esym hBetaWhole).
Qed.
End StrictDrop.
