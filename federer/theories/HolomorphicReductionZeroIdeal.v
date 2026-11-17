(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(2), p. 326:
    the actual zero ideal has no positive directional
    witness, and its depth is the prescribed n. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import HolomorphicGermFormsSealed HolomorphicGermFormsUP ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexOrderedBases HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup HolomorphicCoordinateNorm FieldCoordinateFunctional Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness LinearBasis
  OrthogonalGroupTopology ContinuousMultilinearUP ContinuousMultilinearSealed HolomorphicGermRing
  HolomorphicGermJetZeroNegate HolomorphicReductionLociUP HolomorphicReductionActual
  HolomorphicRotatedGermIdeal AnalyticReductionDepthUP AnalyticReductionDepthLaws HolomorphicDepthSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ZeroIdeal.
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

(** Source for [holomorphic_rotated_zero_ideal]: actual
    orthogonal pullback preserves the zero ideal,
    supporting depth({0}) in 3.4.8(2), p. 326. *)
Lemma holomorphic_rotated_zero_ideal (g:O) (alpha:G):
  @holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR I0 g alpha <->alpha = 0.
Proof.
rewrite holomorphic_rotated_germ_ideal_membership;split.
- move=>[beta [hBeta <-]];by rewrite hBeta rmorph0.
- move=>->;exists 0;split=>//;exact:rmorph0.
Qed.

(** Source for [holomorphic_reduction_zero_B_empty]: the
    original positive-order derivative test fails for
    the actual zero ideal, 3.4.8(2), p. 326. *)
Lemma holomorphic_reduction_zero_B_empty j (g:O):
  ~@holomorphic_reduction_actual_B R X Herm hHerm n e he omega I0 j g.
Proof.
have hLaws:=@holomorphic_reduction_actual_laws R X Herm hHerm n e he omega I0.
move/(holomorphic_reduction_B_membership hLaws j g)=>[alpha [hAlpha [hQ [k [hK hJet]]]]].
have hZero:alpha = 0 by exact:(holomorphic_rotated_zero_ideal g alpha).1 hAlpha.
apply:hJet;rewrite hZero (@HolomorphicGermForms.laws R X NX hNX 0 k (0:G))
  holomorphic_germ_jet_zero linear0.
by [].
Qed.

(** Source for [holomorphic_depth_zero_ideal]: the original
    special convention depth({0})=n follows from the
    same finite-minimum laws, 3.4.8(2), p. 326. *)
Lemma holomorphic_depth_zero_ideal:@HolomorphicDepth.value R X Herm hHerm n e he omega I0 = n.
Proof.
exact:(analytic_reduction_depth_empty_family holomorphic_reduction_zero_B_empty
  (@HolomorphicDepth.laws R X Herm hHerm n e he omega I0)).
Qed.
End ZeroIdeal.
