(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.8(15), pp. 328, 337:
    a proper nonempty irreducible subgerm of an irreducible
    holomorphic germ has strictly smaller dimension. The original
    prime-model larger-ideal assertion contradicts a common E_m
    rotation if the dimensions agree. Both endpoints remain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions cardinality reals
  constructive_ereal topology subtype_topology.
From Federer Require Import UnitaryGroupHaar FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
  EuclideanInnerProduct EuclideanStiefelInnerSplitting InnerNorm InnerMetric HomInner HilbertFormCompactness
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology LinearGroupSealed IsotropyGroupTopology
  HaarIntegralUP CompactGroupHaarNormalisation MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostPositiveWitness
  SetGermUP SetGermOrder HolomorphicGermRing CommutativeIdealUP HolomorphicGermVanishingSealed HolomorphicGermVanishingIdeal HolomorphicGermVanishingMonotonicity
  HolomorphicIrreducibleGermUP HolomorphicIrreducibleProperPrime HolomorphicDepthSealed AnalyticReductionDepthUP
  HolomorphicReductionActual HolomorphicReductionLociUP HolomorphicDepthReductionAlmost HolomorphicIdealDepthMonotonicity
  HolomorphicZeroDepthPointGerm HolomorphicFullDimensionWholeGerm HolomorphicProperSubgermIdeal
  HolomorphicRotatedGermIdeal HolomorphicRotatedStrictIdeal HolomorphicPrimeLocalModelUP Federer3412PrimeReduction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section StrictDrop.
Variable R:realType.
Variable n:nat.
Local Notation X:=(coordinate_space (ComplexScalars.C R) n).
Local Notation Herm:=(@standard_hermitian_product R n).
Local Notation hHerm:=(@standard_hermitian_productP R n).
Local Notation B:=(hermitian_real_part Herm).
Local Notation hB:=(hermitian_real_inner_product hHerm).
Local Notation NX:=(@holomorphic_coordinate_norm R n).
Local Notation hNX:=(complex_norm_real (@holomorphic_coordinate_norm_laws R n)).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation G:=(@set_germ_space T 0).
Local Notation A:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNX 0)].
Local Notation e:=(@coordinate_basis (ComplexScalars.C R) n).
Local Notation he:=(@coordinate_basisP (ComplexScalars.C R) n).
Local Notation omega:=(dual_basis he).
Local Notation eR:=(ordered_real_basis e).
Local Notation heR:=(ordered_real_basisP he).
Local Notation O:=(@unitary_group R X Herm hHerm (n+n) eR heR).
Local Notation ideal:=(@HolomorphicSetIdeal.value R X NX hNX 0).
Local Notation depth:=(@HolomorphicDepth.value R X Herm hHerm n e he omega).

(** Source for [holomorphic_irreducible_strict_subgerm_depth_drop]: the
    irreducible beta case of original 3.4.8(15),
    p. 337. Every model and common generic
    coordinate system is derived from the original germs. *)
Theorem holomorphic_irreducible_strict_subgerm_depth_drop (alpha beta:G):
  @is_nonempty_irreducible_holomorphic_germ R X NX hNX 0 alpha ->
  @is_nonempty_irreducible_holomorphic_germ R X NX hNX 0 beta ->
  set_germ_subset beta alpha ->alpha<>beta ->
  (depth (ideal beta)<depth (ideal alpha))%N.
Proof.
move=>hAlpha hBeta hSub hDifferent.
have hMono:=@holomorphic_variety_ideal_depth_monotone R X Herm hHerm n e he omega beta alpha hSub.
rewrite ltn_neqAle hMono andbT;apply/negP=>/eqP hEqual.
have hDual i j:omega i (e j)=if i==j then 1 else 0 by rewrite dual_basisE eq_sym.
case:(posnP (depth (ideal alpha)))=>[hZero|hPositive].
- have hAlphaPoint:=@holomorphic_zero_depth_point_germ R X Herm hHerm n e he omega hDual alpha hAlpha.1.1 hAlpha.2 hZero.
  have hBetaZero:depth (ideal beta)=0%N by rewrite hEqual.
  have hBetaPoint:=@holomorphic_zero_depth_point_germ R X Herm hHerm n e he omega hDual beta hBeta.1.1 hBeta.2 hBetaZero.
  apply:hDifferent;exact:eq_trans hAlphaPoint (esym hBetaPoint).
- case:(ltnP (depth (ideal alpha)) n)=>hMN.
  + pose m:'I_n:=Ordinal hMN.
    pose I:=ideal alpha;pose J:=ideal beta.
    have hPrimeI:=(@holomorphic_irreducible_proper_prime_equivalence R X NX hNX 0 alpha hAlpha.1.1).1 hAlpha.
    have hPrimeJ:=(@holomorphic_irreducible_proper_prime_equivalence R X NX hNX 0 beta hBeta.1.1).1 hBeta.
    have [mulO [invO [unitO [hO [mulU [invU [unitU [hU [hLocal [theta hTheta]]]]]]]]]]:=
      @unitary_group_haar_exists R X Herm hHerm (n+n) eR heR.
    have hAlmostI:=@holomorphic_depth_reduction_haar_almost R n I hPrimeI (ex_intro _ alpha erefl)
      mulO invO unitO hO mulU invU unitU hU (widen_ord (leqnSn n) m) theta erefl hTheta.
    have hAlmostJ:=@holomorphic_depth_reduction_haar_almost R n J hPrimeJ (ex_intro _ beta erefl)
      mulO invO unitO hO mulU invU unitU hU (widen_ord (leqnSn n) m) theta hEqual hTheta.
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
      @federer_3_4_12_10 R n e he omega hDual
        I g m hBound hPrimeI hPositive hEmI.
    pose Ig:=@holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR I g.
    pose Jg:=@holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR J g.
    have hInclusion:I `<=` J:=@holomorphic_set_ideal_antitone R X NX hNX 0 beta alpha hSub.
    have hRotatedInclusion:=@holomorphic_rotated_ideal_inclusion R X Herm hHerm n e he I J g hInclusion.
    have hStrict:=@holomorphic_proper_subgerm_ideal_witness R X NX hNX 0 alpha beta hBeta.1.1 hSub hDifferent.
    have hRotatedStrict:=@holomorphic_rotated_strict_ideal_witness R X Herm hHerm n e he I J g hStrict.
    have hJg:=@holomorphic_rotated_germ_ideal_is_ideal R X Herm hHerm (n+n) eR heR J g hPrimeJ.1.
    have hFields:=hModel;do 19 (case:hFields=>_ hFields).
    have [phi [hPhi [hQ [hOutside hNonzero]]]]:=hFields Jg hJg hRotatedInclusion hRotatedStrict.
    have hLociJ:=@holomorphic_reduction_actual_laws R X Herm hHerm n e he omega J.
    have hNotA:=((holomorphic_reduction_E_membership hLociJ m g).1 hEmJ).2.2.
    apply:hNotA;apply:(holomorphic_reduction_A_membership hLociJ (widen_ord (leqnSn n) m) g).2.
    split;first exact:hPositive.
    exists phi;split;first exact:hPhi.
    by split.
  + have hBound:=analytic_reduction_depth_bound (@HolomorphicDepth.laws R X Herm hHerm n e he omega (ideal alpha)).
    have hFull:depth (ideal alpha)=n by apply/eqP;rewrite eqn_leq hBound hMN.
    have hAlphaWhole:=@holomorphic_full_dimension_whole_germ R n alpha hAlpha.1.1 hAlpha.2 hFull.
    have hBetaFull:depth (ideal beta)=n by rewrite hEqual.
    have hBetaWhole:=@holomorphic_full_dimension_whole_germ R n beta hBeta.1.1 hBeta.2 hBetaFull.
    apply:hDifferent;exact:eq_trans hAlphaWhole (esym hBetaWhole).
Qed.
End StrictDrop.
