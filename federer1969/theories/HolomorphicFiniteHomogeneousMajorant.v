(** Federer (1969), 3.4.12, p. 339, extending 3.4.11, p. 338:
    an actual finite family of original homogeneous
    polynomials contains the whole tangent cone in its
    global zero set. Its original global dimension is
    at most the original source-germ dimension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import FiniteAnalyticVarietyUP HolomorphicInitialPolynomialComplexLaws FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct InnerNorm HilbertFormCompactness HolomorphicGermUP HolomorphicGermRing
  HolomorphicGermRepresentatives SetGermUP HolomorphicGermVanishingUP HolomorphicGermVanishingSealed HolomorphicGermVanishingIdeal
  HolomorphicGermVanishingRepresentative CommutativeIdealUP HolomorphicGermNoetherian
  HolomorphicDepthSealed HolomorphicIdealDepthMonotonicity HolomorphicVarietyGermUP HolomorphicUP
  FiniteHolomorphicVarietyUP FiniteZeroSetSealed TangentConeUP HomogeneousPolynomialFunctions
  HolomorphicInitialFiniteFamily HolomorphicInitialPolynomialLaws HolomorphicInitialPolynomialGlobalAnalytic
  HolomorphicInitialTangentVanishing HolomorphicInitialIdealSealed HolomorphicInitialIdealDepth
  HolomorphicConeDimension HolomorphicSetDimension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Majorant.
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

(** Source for [holomorphic_finite_homogeneous_majorant_exists]: the
    full finite homogeneous polynomial conclusion of 3.4.11,
    p. 338, in indexed form. All
    original polynomials are retained, and the bound
    concerns their global zero set, rather than only
    its germ at the origin. *)
Theorem holomorphic_finite_homogeneous_majorant_exists (S:set X):
  @is_holomorphic_variety_germ R X NX hNX 0 (@set_germ T 0%R S) ->
  @set_germ T 0%R S<>@set_germ T 0%R set0 ->
  exists J:finType,exists k:J->nat,exists P:J->X->ComplexScalars.C R,
    (forall j,(0<k j)%N /\@is_homogeneous_polynomial (ComplexScalars.C R) X (ComplexScalars.C R)^o (k j) (P j)) /\
    let V:=@FiniteZeroSet.value [the zmodType of (ComplexScalars.C R)^o] X setT J P in
    (@norm_tangent_cone R (restricted_space (ComplexScalars.embed R) X) NX S 0 `<=` V) /\
    (@holomorphic_set_dimension R n V<=depth (ideal (@set_germ T 0%R S)))%N.
Proof.
move=>hHolomorphic hNonempty.
pose I:set G:=ideal (@set_germ T 0%R S).
pose K:set G:=@HolomorphicInitialIdeal.value R X NX hNX I.
have [J [a [k [P [f [hFamily hGenerated]]]]]]:=
  @holomorphic_initial_finite_family_exists R X NX hNX I (@finite_holomorphic_germ_ring_noetherian R X NX (@holomorphic_coordinate_norm_laws R n) n e 0 he).
have hInitial j:HolomorphicInitialPolynomialUP.is_initial_holomorphic_germ_polynomial (a j) (k j) (P j).
  exact:(hFamily j).2.1.
have hProperties j:=@holomorphic_initial_polynomial_laws R X NX hNX (a j) (k j) (P j) (hInitial j).
have hComplex j:=@holomorphic_initial_polynomial_complex_homogeneous R X Herm hHerm n e he
  (a j) (k j) (P j) (hInitial j).
have hPolynomial j:@is_holomorphic R X (ComplexScalars.C R)^o NX (@complex_modulus R) hNX
    (@complex_modulus_real_norm R) setT (P j).
  exact:(@holomorphic_initial_polynomial_global_analytic R X Herm hHerm n e he (a j) (k j) (P j) (hInitial j)).
exists J,k,P;split.
- move=>j;split;[exact:(hInitial j).1|exact:(hComplex j)].
move=>V.
have hEquations:=@FiniteZeroSet.laws [the zmodType of (ComplexScalars.C R)^o] X setT J P.
have hVHolomorphic:@is_holomorphic_set_in R X NX hNX setT V.
  move=>x _;exists setT,V;split;first done.
  split;last reflexivity.
  split;first exact:openT.
  exists J,P;split;[exact:hPolynomial|exact:original_zero_set_membership hEquations].
have hCone (t:R) (ht:0<t) x (hx:V x):V (t*:(x:restricted_space (ComplexScalars.embed R) X)).
  apply/(original_zero_set_membership hEquations).
  split;first done.
  move=>j;by rewrite (hProperties j).2.2.1 ((original_zero_set_membership hEquations x).1 hx).2 // scaler0.
split.
- move=>v hv;apply/(original_zero_set_membership hEquations).
  split;first done.
  move=>j;exact:(@holomorphic_initial_polynomial_tangent_vanishes R X NX hNX S (a j) (k j) (P j)
    (hFamily j).1 (hInitial j) v hv).
- have hInclusion:K `<=` ideal (@set_germ T 0%R V).
    apply:(generated_commutative_ideal_minimal hGenerated
      (@holomorphic_set_ideal_ring_laws R X NX hNX 0 (@set_germ T 0%R V))).
    move=>beta [j <-];apply/(@holomorphic_set_ideal_representative_equation R X NX hNX 0 (f j) V).
    exists setT;split;first exact:openT.
    split;first done.
    move=>x hx _;rewrite (hFamily j).2.2.
    exact:((original_zero_set_membership hEquations x).1 hx).2 j.
  apply:(leq_trans (@holomorphic_cone_global_dimension_bound R n V hVHolomorphic hCone)).
  apply:(leq_trans (@holomorphic_ideal_depth_antitone R X Herm hHerm n e he omega K
    (ideal (@set_germ T 0%R V)) hInclusion)).
  exact:(@holomorphic_initial_ideal_depth_bound R n (@set_germ T 0%R S) hHolomorphic hNonempty).
Qed.
End Majorant.
