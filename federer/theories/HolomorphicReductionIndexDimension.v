(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.8(13), pp. 335–336:
    a positive original E_m reduction of an irreducible
    variety has m equal to its actual ideal depth.
    Apply the proved model (10), upper-null representative
    from (11), and positive measure of every nonempty
    m-dimensional holomorphic manifold germ. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import HolomorphicPrimeReductionDimension HolomorphicLastReductionDepth StandardHermitianBasisValues UnitaryGroupHaar UnitaryComplexMapSealed HolomorphicRotatedCompositionInverse FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct EuclideanStiefelInnerSplitting InnerNorm InnerMetric
  HilbertFormCompactness OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  HolomorphicGermRing CommutativeIdealUP SetGermUP SetGermSealed SetGermOrder SetGermBooleanOrder
  HolomorphicGermVanishingSealed HolomorphicIdealVarietyGermUP HolomorphicIdealVarietyGermSealed HolomorphicIdealVarietyGermExistence
  HolomorphicReductionActual HolomorphicReductionLociUP AnalyticReductionDepthUP HolomorphicDepthSealed
  HolomorphicRotatedGermIdeal HolomorphicRotatedIdealDepth HolomorphicRotatedIdealRecovery
  HolomorphicPrimeLocalModelUP HolomorphicPrimeLocalModelLaws Federer3412PrimeReduction
  FunctionalHolomorphicManifold HolomorphicGermHigherDegreeNull HolomorphicSubmanifoldGermNonNull.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section IndexDimension.
Variable R:realType.
Variable n:nat.
Local Notation X:=(coordinate_space (ComplexScalars.C R) n).
Local Notation Herm:=(@standard_hermitian_product R n).
Local Notation hHerm:=(@standard_hermitian_productP R n).
Local Notation B:=(hermitian_real_part Herm).
Local Notation hB:=(hermitian_real_inner_product hHerm).
Local Notation NX:=(@holomorphic_coordinate_norm R n).
Local Notation hNX:=(complex_norm_real (@holomorphic_coordinate_norm_laws R n)).
Local Notation E:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNX 0)].
Local Notation e:=(@coordinate_basis (ComplexScalars.C R) n).
Local Notation he:=(@coordinate_basisP (ComplexScalars.C R) n).
Local Notation omega:=(dual_basis he).
Local Notation eR:=(ordered_real_basis e).
Local Notation heR:=(ordered_real_basisP he).
Local Notation O:=(@unitary_group R X Herm hHerm (n+n) eR heR).
Local Notation ideal:=(@HolomorphicSetIdeal.value R X NX hNX 0).
Local Notation depth:=(@HolomorphicDepth.value R X Herm hHerm n e he omega).


(** Source for [holomorphic_prime_reduction_index_dimension]: every
    original E_m index equals the original complex ideal depth,
    extending 3.4.8(13), pp. 335–336, under 3.4.12,
    p. 339. Keep both dimension endpoints and every actual
    vanishing ideal; no dimension comparison is assumed. *)
Theorem holomorphic_prime_reduction_index_dimension (I:set G) (m:'I_n.+1) (g:O):
  is_prime_commutative_ideal I ->(exists sigma:@set_germ_space E 0,I=ideal sigma) ->
  @holomorphic_reduction_actual_E R X Herm hHerm n e he omega I m g ->
  depth I=(m:nat).
Proof.
move=>hPrime hVanishing hEm.

have hDual i j:omega i (e j)=if i==j then 1 else 0 by rewrite dual_basisE eq_sym.
case:(ltnP m n)=>hMN.
- pose mi:'I_n:=Ordinal hMN.
  have hIndex:widen_ord (leqnSn n) mi=m by apply:val_inj.
  have hInterior:@holomorphic_reduction_actual_E R X Herm hHerm n e he omega I (widen_ord (leqnSn n) mi) g.
    by rewrite hIndex.
  case:(posnP (m:nat))=>[hZero|hPositive].
  + have hLoci:=@holomorphic_reduction_actual_laws R X Herm hHerm n e he omega I.
    have hTail:=((holomorphic_reduction_E_membership hLoci mi g).1 hInterior).2.1.
    have hBound:=(analytic_reduction_depth_minimal (@HolomorphicDepth.laws R X Herm hHerm n e he omega I)
      (ex_intro _ g hTail)).
    apply/eqP;rewrite eqn_leq hBound /= hZero;exact:leq0n.
  + exact:(@holomorphic_prime_positive_reduction_dimension R n I mi g hPrime hVanishing hPositive hInterior).
- have hEqual:(m:nat)=n by apply/eqP;rewrite eqn_leq hMN andbT;exact:ltn_ord m.
  have hIndex:m=ord_max by apply:val_inj;exact:hEqual.
  rewrite hEqual;apply:(@holomorphic_last_reduction_depth R X Herm hHerm n e he omega hDual I g hPrime.1).
  by rewrite -hIndex.
Qed.
End IndexDimension.
