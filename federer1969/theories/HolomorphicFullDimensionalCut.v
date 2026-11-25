(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(11), p. 333:
    a full-dimensional holomorphic germ is the whole
    germ. An original nonzero equation vanishing on
    beta cuts out an empty or strictly smaller
    exceptional variety. These assertions use the
    proved nonzero-ideal depth bound and original
    ideal separation, before the stratification induction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexOrderedBases HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup HolomorphicCoordinateNorm FieldCoordinateFunctional Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthonormalFamilies HolomorphicGermUP HolomorphicGermRing HolomorphicGermRingLaws HolomorphicGermRepresentatives
  CommutativeIdealUP SetGermUP SetGermSealed SetGermOrder SetGermBoundary HolomorphicVarietyGermUP
  HolomorphicGermVanishingSealed HolomorphicGermVanishingIdeal HolomorphicIdealPropriety HolomorphicProperVarietyNonzeroIdeal
  HolomorphicDepthSealed HolomorphicNonzeroIdealDepth HolomorphicZeroGermSealed HolomorphicZeroGermIdeal
  HolomorphicZeroGermVarieties.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FullDimensionalCut.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable Herm:X->X->ComplexScalars.C R.
Hypothesis hHerm:is_hermitian_product Herm.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation B:=(hermitian_real_part Herm).
Local Notation hB:=(hermitian_real_inner_product hHerm).
Variable n:nat.
Variable e:'I_n.+1->X.
Variable he:is_basis e.
Variable hON:orthonormal_family Herm e.
Variable omega:'I_n.+1->Hom X (ComplexScalars.C R)^o.
Hypothesis hDual:forall i j,omega i (e j) = if i==j then 1 else 0.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(hermitian_complex_norm hHerm).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation eR:=(ordered_real_basis e).
Local Notation heR:=(ordered_real_basisP he).
Local Notation A:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNXR 0)].
Local Notation T:=(Topological.clone (real_norm_metric_space hNXR) _).
Local Notation germ:=(@set_germ T 0).
Local Notation ideal:=(@HolomorphicSetIdeal.value R X NX hNXR 0).
Local Notation depth:=(@HolomorphicDepth.value R X Herm hHerm n.+1 e he omega).
Local Notation zero:=(@HolomorphicZeroGerm.value R X NX hNXR 0).

(** Source for [holomorphic_full_dimensional_variety_whole]:
    alpha=gamma_0(R^m) in the original n=m
    case of 3.4.8(11), p. 333.
    A proper holomorphic germ would have a
    nonzero proper ideal and hence strictly smaller depth. *)
Lemma holomorphic_full_dimensional_variety_whole (alpha:@set_germ_space T 0):
  @is_holomorphic_variety_germ R X NX hNXR 0 alpha ->alpha<>germ set0 ->
  depth (ideal alpha) = n.+1 ->alpha = germ setT.
Proof.
move=>hAlpha hNonempty hDepth;apply:contrapT=>hProper.
have hIProper:~ideal alpha (1:A).
  move=>hUnit;apply:hNonempty;exact:(holomorphic_set_ideal_contains_one alpha).1 hUnit.
have [phi [hPhi hNonzero]]:=holomorphic_proper_variety_nonzero_ideal hAlpha hProper.
have hDrop:=@holomorphic_nonzero_proper_ideal_depth_lt R X Herm hHerm n e he omega hDual hON
  (ideal alpha) (holomorphic_set_ideal_ring_laws alpha) hIProper (ex_intro _ phi (conj hPhi hNonzero)).
by move:hDrop;rewrite hDepth ltnn.
Qed.

(** Source for [holomorphic_nonzero_equation_depth_drop]:
    the zero variety of the original nonzero
    equation has depth below the full source
    dimension, as used in 3.4.8(11), p. 333.
    The zero germ is treated separately. *)
Lemma holomorphic_nonzero_equation_depth_drop (phi:A):
  phi<>0 ->zero phi = germ set0 \/(depth (ideal (zero phi))<n.+1)%N.
Proof.
move=>hNonzero;case:(pselect (zero phi = germ set0))=>hEmpty;first by left.
right.
have hProper:~ideal (zero phi) (1:A).
  move=>hUnit;apply:hEmpty;exact:(holomorphic_set_ideal_contains_one _).1 hUnit.
have hPhi:ideal (zero phi) phi.
  apply:(@holomorphic_zero_germ_ideal_equivalence R X NX hNXR 0 (zero phi) phi).2.
  exact:set_germ_subset_reflexive.
exact:(@holomorphic_nonzero_proper_ideal_depth_lt R X Herm hHerm n e he omega hDual hON
  (ideal (zero phi)) (holomorphic_set_ideal_ring_laws _) hProper (ex_intro _ phi (conj hPhi hNonzero))).
Qed.

(** Source for [holomorphic_full_dimensional_exceptional_equation]:
    choose the actual Phi vanishing on beta,
    with gamma_0(Phi) nonzero, in the full
    source-dimensional case of 3.4.8(11), p. 333.
    Its original zero germ contains beta and
    has the strict dimension drop required for induction. *)
Theorem holomorphic_full_dimensional_exceptional_equation (beta:@set_germ_space T 0):
  @is_holomorphic_variety_germ R X NX hNXR 0 beta ->beta<>germ setT ->
  exists f:@holomorphic_representative_type R X NX hNXR 0,
    holomorphic_germ f<>(0:A) /\ideal beta (holomorphic_germ f) /\
    set_germ_subset beta (zero (holomorphic_germ f)) /\
    (zero (holomorphic_germ f) = germ set0 \/(depth (ideal (zero (holomorphic_germ f)))<n.+1)%N).
Proof.
move=>hBeta hProper.
have [phi [hPhi hNonzero]]:=holomorphic_proper_variety_nonzero_ideal hBeta hProper.
have [f hF]:=@holomorphic_germ_has_representative R X NX hNXR 0 phi.
exists f;rewrite hF;split;first exact:hNonzero.
split;first exact:hPhi.
split.
- exact:(@holomorphic_zero_germ_ideal_equivalence R X NX hNXR 0 beta phi).1 hPhi.
- exact:holomorphic_nonzero_equation_depth_drop hNonzero.
Qed.
End FullDimensionalCut.
