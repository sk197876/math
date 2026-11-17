(** Federer (1969), 3.4.12, p. 339, extending 3.4.11, p. 338:
    the complete original tangent-hull dimension assertion
    at the original centre. Every dimension is the
    original opaque nonempty variety-germ dimension; actual
    translation and tangent locality supply the reduction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct InnerNorm HilbertFormCompactness
  HolomorphicGermRing CommutativeIdealUP SetGermUP SetGermOrder SetGermBoundary SetGermCentreMember
  HolomorphicGermVanishingSealed HolomorphicVarietyGermUP HolomorphicSetNonemptyCentres HolomorphicSetLocalDepth
  HolomorphicDepthSealed HolomorphicVarietyGermDimensionSealed HolomorphicVarietyGermDimensionLaws
  HolomorphicIdealVarietyGermSealed TangentConeUP TangentConeBasic TangentConeTranslation
  HolomorphicTangentHullDimension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_3_4_12_tangent]: the first original
    dimension display of 3.4.12, p. 339, extending 3.4.11, p. 338.
    Original open U, holomorphic S, centre a and
    nonempty source germ remain. The actual tangent hull,
    both nonempty holomorphic germs and the finite ideal
    witnesses are constructed internally. *)
Theorem federer_3_4_12_tangent (R:realType) n (U S:set (coordinate_space (ComplexScalars.C R) n)) a:
  let X:=coordinate_space (ComplexScalars.C R) n in
  let B:=@standard_hermitian_product R n in
  let hB:=@standard_hermitian_productP R n in
  let NX:=@holomorphic_coordinate_norm R n in
  let hNX:=complex_norm_real (@holomorphic_coordinate_norm_laws R n) in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  let e:=@coordinate_basis (ComplexScalars.C R) n in
  let he:=@coordinate_basisP (ComplexScalars.C R) n in
  let omega:=dual_basis he in
  @open T U ->S `<=` U ->@is_holomorphic_set_in R X NX hNX U S ->U a ->
  @set_germ T a S<>@set_germ T a set0 ->
  exists hSource:@is_holomorphic_variety_germ R X NX hNX 0 (@set_germ T 0 [set x|S (a+x)]),
  exists hNonempty:@set_germ T 0 [set x|S (a+x)]<>@set_germ T 0 set0,
  exists hJ:@is_finitely_generated_commutative_ideal
    [the comNzRingType of (@holomorphic_germ_ring R X NX hNX 0)]
    (@HolomorphicSetIdeal.value R X NX hNX 0 (@set_germ T 0 (@norm_tangent_cone R (restricted_space (ComplexScalars.embed R) X) NX S a))),
  let nu:=@HolomorphicIdealVarietyGerm.value R X NX hNX 0
    (@HolomorphicSetIdeal.value R X NX hNX 0 (@set_germ T 0 (@norm_tangent_cone R (restricted_space (ComplexScalars.embed R) X) NX S a))) hJ in
  exists hNu:@is_holomorphic_variety_germ R X NX hNX 0 nu,
  exists hNuNonempty:nu<>@set_germ T 0 set0,
    set_germ_subset (@set_germ T 0 (@norm_tangent_cone R (restricted_space (ComplexScalars.embed R) X) NX S a)) nu /\
    (@HolomorphicVarietyGermDimension.value R X B hB n e he omega nu hNu hNuNonempty<=
      @HolomorphicVarietyGermDimension.value R X B hB n e he omega
        (@set_germ T 0%R [set x|S ((a+x)%R)]) hSource hNonempty)%N.
Proof.
move=>X B hB NX hNX T e he omega hU hSU hHolomorphic haU hSourceNonempty.
have haS:=(@holomorphic_set_nonempty_germ_centres R X NX hNX U S a hHolomorphic haU).1 hSourceNonempty.
have hSource:=@holomorphic_set_translated_germ R n S a (hHolomorphic a haU).
have hNonempty:=@holomorphic_set_translated_nonempty R n S a haS.
have hHull:=@holomorphic_tangent_hull_depth_bound R n [set x|S (a+x)] hSource hNonempty.
rewrite (@norm_tangent_source_translation R (restricted_space (ComplexScalars.embed R) X) NX S a) in hHull.
have [hJ [hNu [hContain hBound]]]:=hHull.
exists hSource,hNonempty,hJ.
pose nu:=@HolomorphicIdealVarietyGerm.value R X NX hNX 0
  (@HolomorphicSetIdeal.value R X NX hNX 0 (@set_germ T 0 (@norm_tangent_cone R (restricted_space (ComplexScalars.embed R) X) NX S a))) hJ.
have hTangentZero:@norm_tangent_cone R (restricted_space (ComplexScalars.embed R) X) NX S a 0.
  apply:(@norm_tangent_zero_closure R (restricted_space (ComplexScalars.embed R) X) NX hNX S a).2.
  exact:(@subset_closure T S a haS).
have hTangentNonempty:=@set_germ_centre_member_nonempty T 0
  (@norm_tangent_cone R (restricted_space (ComplexScalars.embed R) X) NX S a) hTangentZero.
have hNuNonempty:nu<>@set_germ T 0 set0.
  move=>hEmpty;apply:hTangentNonempty;apply:set_germ_subset_empty.
  by rewrite -hEmpty.
exists hNu,hNuNonempty;split;first exact:hContain.
rewrite !holomorphic_variety_germ_dimension_depth;exact:hBound.
Qed.
