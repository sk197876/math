(** Federer (1969), 3.4.12, p. 339, extending 3.4.11, p. 338:
    the actual holomorphic hull of the original tangent
    cone has dimension at most the original germ.
    Reuse the proved leading-ideal depth inequality and
    tangent vanishing inclusion, then the original hull
    and ideal-recovery theorems. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct InnerNorm HilbertFormCompactness HolomorphicGermRing
  SetGermUP SetGermOrder SetGermBoundary HolomorphicGermVanishingSealed HolomorphicGermVanishingIdeal
  CommutativeIdealUP HolomorphicGermNoetherian HolomorphicIdealVarietyGermUP HolomorphicIdealVarietyGermSealed
  HolomorphicIdealVarietyVanishingLaws HolomorphicVarietyGermUP HolomorphicDepthSealed HolomorphicIdealDepthMonotonicity
  HolomorphicInitialIdealSealed HolomorphicInitialIdealDepth HolomorphicInitialIdealTangent TangentConeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Hull.
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
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNX 0)].
Local Notation e:=(@coordinate_basis (ComplexScalars.C R) n).
Local Notation he:=(@coordinate_basisP (ComplexScalars.C R) n).
Local Notation omega:=(dual_basis he).
Local Notation ideal:=(@HolomorphicSetIdeal.value R X NX hNX 0).
Local Notation depth:=(@HolomorphicDepth.value R X Herm hHerm n e he omega).

(** Source for [holomorphic_tangent_hull_depth_bound]: the
    original holomorphic-hull dimension inequality in 3.4.11,
    p. 338, in its defining ideal-depth form.
    The hull uses the actual tangent vanishing ideal;
    its finite generation is proved internally. *)
Theorem holomorphic_tangent_hull_depth_bound (S:set X):
  @is_holomorphic_variety_germ R X NX hNX 0 (@set_germ T 0%R S) ->
  @set_germ T 0%R S<>@set_germ T 0%R set0 ->
  exists hJ:@is_finitely_generated_commutative_ideal G (ideal (@set_germ T 0%R (@norm_tangent_cone R (restricted_space (ComplexScalars.embed R) X) NX S 0))),
    let nu:=@HolomorphicIdealVarietyGerm.value R X NX hNX 0
      (ideal (@set_germ T 0%R (@norm_tangent_cone R (restricted_space (ComplexScalars.embed R) X) NX S 0))) hJ in
    @is_holomorphic_variety_germ R X NX hNX 0 nu /\
    set_germ_subset (@set_germ T 0%R (@norm_tangent_cone R (restricted_space (ComplexScalars.embed R) X) NX S 0)) nu /\
    (depth (ideal nu)<=depth (ideal (@set_germ T 0%R S)))%N.
Proof.
move=>hHolomorphic hNonempty.
pose sigma:=@set_germ T 0%R (@norm_tangent_cone R (restricted_space (ComplexScalars.embed R) X) NX S 0).
have hJ:=@finite_holomorphic_germ_ring_noetherian R X NX (@holomorphic_coordinate_norm_laws R n) n e 0 he (ideal sigma)
  (@holomorphic_set_ideal_ring_laws R X NX hNX 0 sigma).
exists hJ=>nu;split.
- exact:(@HolomorphicIdealVarietyGermUP.holomorphic_ideal_variety_germ_is_variety R X NX hNX 0 _ nu
    (@HolomorphicIdealVarietyGerm.laws R X NX hNX 0 _ hJ)).
split;first exact:(@HolomorphicIdealVarietyVanishingLaws.set_germ_in_variety_of_its_ideal R X NX hNX 0 sigma hJ).
rewrite (@HolomorphicIdealVarietyVanishingLaws.vanishing_ideal_variety_recovery R X NX hNX 0 sigma hJ).
apply:(leq_trans _ (@holomorphic_initial_ideal_depth_bound R n (@set_germ T 0%R S) hHolomorphic hNonempty)).
apply:(@holomorphic_ideal_depth_antitone R X Herm hHerm n e he omega).
exact:(@holomorphic_initial_ideal_tangent_inclusion R X NX hNX S).
Qed.
End Hull.
