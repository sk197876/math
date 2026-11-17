(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(2), p. 326:
    the actual zero ideal has no positive directional
    witness, and its depth is the prescribed n. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import CommutativeIdealUP HolomorphicFullPrefixGermSubring HolomorphicUnitaryPullback HolomorphicReductionZeroIdeal ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexOrderedBases HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup HolomorphicCoordinateNorm FieldCoordinateFunctional Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness LinearBasis
  OrthogonalGroupTopology ContinuousMultilinearUP ContinuousMultilinearSealed HolomorphicGermRing
  HolomorphicGermJetZeroNegate HolomorphicReductionLociUP HolomorphicReductionActual
  HolomorphicRotatedGermIdeal AnalyticReductionDepthUP AnalyticReductionDepthLaws HolomorphicDepthSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section LastIndex.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable Herm:X->X->ComplexScalars.C R.
Hypothesis hHerm:is_hermitian_product Herm.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation B:=(hermitian_real_part Herm).
Local Notation hB:=(hermitian_real_inner_product hHerm).
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Variable omega:'I_n->Hom X (ComplexScalars.C R)^o.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(hermitian_complex_norm hHerm).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation eR:=(ordered_real_basis e).
Local Notation heR:=(ordered_real_basisP he).
Local Notation G:=(@holomorphic_germ_ring R X NX hNXR 0).
Local Notation O:=(@unitary_group R X Herm hHerm (n+n) eR heR).
Local Notation I0:=([set alpha:G|alpha = 0]).


Hypothesis hDual:forall i j,omega i (e j) = if i==j then 1 else 0.
(** Source for [holomorphic_last_reduction_depth]: the original full
    E_n endpoint forces the zero ideal and depth n,
    extending 3.4.8(13), p. 335, under 3.4.12, p. 339.
    Keep the literal zero ambient dimension case. *)
Lemma holomorphic_last_reduction_depth (I:set G) (g:O):
  is_commutative_ideal I ->
  @holomorphic_reduction_actual_E R X Herm hHerm n e he omega I ord_max g ->
  @HolomorphicDepth.value R X Herm hHerm n e he omega I=n.
Proof.
move=>hI hEn.
have hBound:=analytic_reduction_depth_bound (@HolomorphicDepth.laws R X Herm hHerm n e he omega I).
case:(posnP n)=>[hZero|hPositive].
- apply/eqP;rewrite eqn_leq hBound /=.
  have hN0:(n<=0)%N by rewrite hZero.
  exact:leq_trans hN0 (leq0n _).
-

  have hLoci:=@holomorphic_reduction_actual_laws R X Herm hHerm n e he omega I.
  have hNotA:=(holomorphic_reduction_E_last_membership hLoci g).1 hEn.
  have hQ:=@holomorphic_full_prefix_germ_subring R X NX hNXR n e he omega hDual.
  have hIZero:I=[set alpha:G|alpha=0].
    apply/seteqP;split.
    * move=>alpha hAlpha;apply:contrapT=>hNonzero;apply:hNotA.
      apply:(holomorphic_reduction_A_membership hLoci ord_max g).2;split;first exact:hPositive.
      pose M:=@holomorphic_unitary_germ_map R X Herm hHerm (n+n) eR heR g.
      exists (M alpha);split.
      -- apply/holomorphic_rotated_germ_ideal_membership;by exists alpha.
      -- split;first by rewrite hQ.
         move=>hMapZero;apply:hNonzero.
         apply:(@holomorphic_unitary_germ_map_injective R X Herm hHerm (n+n) eR heR g).
         by rewrite rmorph0.
    * move=>alpha ->;exact:commutative_ideal_zero hI.
  rewrite hIZero;exact:holomorphic_depth_zero_ideal.
Qed.

End LastIndex.
