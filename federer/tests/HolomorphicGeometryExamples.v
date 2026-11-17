(** Federer (1969), 3.4.12, p. 339, extending 3.4.9, p. 337:
    actual positive-radius ball, whole-plane dimension and
    negative-base square-cover regressions,
    retaining the zero ambient dimension and the original
    whole-plane depth in the uniform-ball theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import Hom ComplexEuclideanCoordinates AnalyticDepthSealed GermVanishingSealed HolomorphicGeometry HolomorphicWholeGermIdeal FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
  EuclideanInnerProduct InnerNorm HilbertFormCompactness SetGermUP SetGermBoundary
  FiniteHolomorphicVarietyUP FiniteHolomorphicVarietyBoundary HolomorphicVarietyGermUP
  HolomorphicVarietyGermBooleanClosure  LocallyFiniteFamilyUP
  FunctionalHolomorphicWhole HolomorphicFamilies HolomorphicFiniteStratificationUP
  HolomorphicDepthSealed HolomorphicReductionZeroIdeal HolomorphicGermVanishingSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_ball_all_radii_regression]: the actual
    ball in every ambient dimension, including zero,
    has finitely many components for every positive radius.
    This tests the absence of exceptional radii in
    the component argument of 3.4.12, p. 339, extending 3.4.9, p. 337. *)
Example holomorphic_ball_all_radii_regression (R:realType) n (r:R):
  0<r ->
  finite_set (@connected_component
    (Topological.clone (real_norm_metric_space (complex_norm_real (@holomorphic_coordinate_norm_laws R n))) _)
    [set x|@holomorphic_coordinate_norm R n x<r] @`
    [set x|@holomorphic_coordinate_norm R n x<r]).
Proof.
move=>hR.
have h:=@functional_holomorphic_ball_finite_components R n n setT setT r
  (@functional_holomorphic_whole R n) hR (fun _ _=>Logic.I).
by rewrite setTI in h.
Qed.

(** Source for [holomorphic_whole_plane_uniform_ball_regression]: the
    actual whole plane has depth two and admits
    one original stratification valid after restriction to
    every sufficiently small positive ball, as asserted
    in 3.4.12, p. 339, extending 3.4.9, p. 337. Every premise is proved. *)
Example holomorphic_whole_plane_uniform_ball_regression (R:realType):
  let X:=coordinate_space (ComplexScalars.C R) 2 in
  let NX:=@holomorphic_coordinate_norm R 2 in
  let hN:=complex_norm_real (@holomorphic_coordinate_norm_laws R 2) in
  let T:=Topological.clone (real_norm_metric_space hN) _ in
  exists mu,exists V S G:'I_mu->set X,exists rho:R,
    0<rho /\@is_holomorphic_finite_stratification R 2 (@set_germ T 0 setT)
      (@set_germ T 0 set0) 2 setT set0 mu V S G /\
    forall r:R,0<r ->r<rho ->
      @is_holomorphic_finite_stratification R 2 (@set_germ T 0 setT)
        (@set_germ T 0 set0) 2 setT set0 mu
        (fun _=>[set x|NX x<r]) (fun i=>[set x|NX x<r] `&` S i)
        (fun i=>[set x|NX x<r] `&` G i).
Proof.
move=>X NX hN T.
have hNonempty:@set_germ T 0 setT<>@set_germ T 0 set0.
  move=>h;exact:(@set_germ_empty_not_whole T 0) (esym h).
have hDepth:@HolomorphicDepth.value R X (@standard_hermitian_product R 2) (@standard_hermitian_productP R 2)
    2 (@coordinate_basis (ComplexScalars.C R) 2) (@coordinate_basisP (ComplexScalars.C R) 2) (dual_basis (@coordinate_basisP (ComplexScalars.C R) 2))
    (@HolomorphicSetIdeal.value R X NX hN 0 (@set_germ T 0 setT))= 2%N.
  rewrite (@holomorphic_whole_germ_ideal_zero R X NX hN 0).
  exact:holomorphic_depth_zero_ideal.
exact:(@federer_3_4_12_families_uniform_balls R 2 _ _ 2 setT set0
  (@holomorphic_variety_germ_whole R X NX hN 0) hNonempty hDepth Logic.I
  (@finite_holomorphic_variety_domain_empty R X NX hN setT openT) erefl).
Qed.

Section DimensionRegression.
Variable R:realType.
Local Notation X:=(coordinate_space (ComplexScalars.C R) 2).
Local Notation Y:=(R_n R 4).
Local Notation NX:=(@holomorphic_coordinate_norm R 2).
Local Notation hNX:=(complex_norm_real (@holomorphic_coordinate_norm_laws R 2)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R 4)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R 4)).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation TY:=(Topological.clone (real_norm_metric_space hNY) _).
Local Notation u:=(@complex_from_real_coordinate_hom R 2).
Local Notation depthC:=(@HolomorphicDepth.value R X (@standard_hermitian_product R 2)
  (@standard_hermitian_productP R 2) 2 (@coordinate_basis (ComplexScalars.C R) 2)
  (@coordinate_basisP (ComplexScalars.C R) 2) (dual_basis (@coordinate_basisP (ComplexScalars.C R) 2))).
Local Notation depthR:=(@AnalyticDepth.value R Y (@euclidean_inner_product R 4)
  (@euclidean_inner_productP R 4) 4 (@coordinate_basis R 4)
  (@coordinate_basisP R 4) (dual_basis (@coordinate_basisP R 4))).

(** Source for [holomorphic_plane_real_dimension_regression]: the actual
    complex plane C squared has complex dimension two and underlying
    real dimension four, testing the corrected final display of
    3.4.12, p. 339. Every source and dimension premise is proved. *)
Example holomorphic_plane_real_dimension_regression:
  depthC (@HolomorphicSetIdeal.value R X NX hNX 0 (@set_germ T 0 setT))= 2%N /\
  depthR (@AnalyticSetIdeal.value R Y NY hNY 0 (@set_germ TY 0 (u @^-1` (setT:set X))))= 4%N.
Proof.
have hDimension:depthC (@HolomorphicSetIdeal.value R X NX hNX 0 (@set_germ T 0 setT))= 2%N.
  rewrite (@holomorphic_whole_germ_ideal_zero R X NX hNX 0).
  exact:holomorphic_depth_zero_ideal.
split;first exact:hDimension.
have hWhole:=@holomorphic_variety_germ_whole R X NX hNX 0.
have hNonempty:@set_germ T 0 setT<>@set_germ T 0 set0.
  move=>h;exact:(@set_germ_empty_not_whole T 0) (esym h).
have hComparison:=@holomorphic_real_germ_dimension_doubling R 2 setT hWhole hNonempty.
by rewrite hDimension in hComparison.
Qed.
End DimensionRegression.

(** Source for [holomorphic_negative_base_square_cover_regression]: the
    actual base value minus one has two local holomorphic root
    sections, while the entire punctured square graph is connected
    and its component projection is not injective, 3.4.12, p. 339. *)
Example holomorphic_negative_base_square_cover_regression (R:realType):
  let C:=ComplexScalars.C R in
  let M:=real_norm_metric_space (@complex_modulus_real_norm R) in
  exists W:set M,exists s:'I_2->C->C,
    is_original_complex_square_local_cover (-1:C) W s /\
    connected (@complex_square_punctured_graph R) /\
    exists a b:M*M,complex_square_punctured_graph a /\complex_square_punctured_graph b /\
      a<>b /\connected_component (@complex_square_punctured_graph R) a b /\a.1=b.1.
Proof.
move=>C M.
have hNegative:(-1:C)<>0 by apply/eqP;rewrite oppr_eq0;exact:oner_neq0.
have [W [s hCover]]:=@original_complex_square_local_cover_exists R (-1:C) hNegative.
exists W,s;split;first exact:hCover.
have [hConnected [hLocal hObstruction]]:=@original_complex_square_cover_component_obstruction R.
by split.
Qed.
