(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(11), p. 327,
    proved on pp. 333–335: the complete original
    finite holomorphic stratification. Apply the published
    correction at p. 327 line 24 in full.
    The underlying depth is the original dimension;
    all existence and component bounds are proved by
    the simultaneous induction within this project. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
  EuclideanInnerProduct InnerNorm HilbertFormCompactness SetGermUP HolomorphicVarietyGermUP
  FiniteHolomorphicVarietyUP HolomorphicGermVanishingSealed HolomorphicDepthSealed HolomorphicFiniteStratificationUP
  HolomorphicFiniteStratificationExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_3_4_12_11]:
    every assertion of corrected 3.4.12, p. 339, extending 3.4.8(11), p. 327:
    exact difference germ, finite actual components,
    functional holomorphic strata of dimension at most m,
    disjointness from earlier strata, and smaller holomorphic
    boundaries contained in those earlier strata.
    Empty boundary germs are explicit because the book
    defines dimension only for nonempty variety germs. *)
Theorem federer_3_4_12_11 (R:realType) n
    (alpha beta:@set_germ_space (Topological.clone (real_norm_metric_space
      (complex_norm_real (@holomorphic_coordinate_norm_laws R n))) _) 0)
    m (U0 S0:set (coordinate_space (ComplexScalars.C R) n)):
  @is_holomorphic_variety_germ R (coordinate_space (ComplexScalars.C R) n) (@holomorphic_coordinate_norm R n)
    (complex_norm_real (@holomorphic_coordinate_norm_laws R n)) 0 alpha ->
  alpha<>@set_germ (Topological.clone (real_norm_metric_space
    (complex_norm_real (@holomorphic_coordinate_norm_laws R n))) _) 0 set0 ->
  @HolomorphicDepth.value R (coordinate_space (ComplexScalars.C R) n) (@standard_hermitian_product R n) (@standard_hermitian_productP R n)
    n (@coordinate_basis (ComplexScalars.C R) n) (@coordinate_basisP (ComplexScalars.C R) n) (dual_basis (@coordinate_basisP (ComplexScalars.C R) n))
    (@HolomorphicSetIdeal.value R (coordinate_space (ComplexScalars.C R) n) (@holomorphic_coordinate_norm R n)
      (complex_norm_real (@holomorphic_coordinate_norm_laws R n)) 0 alpha) = m ->
  U0 0 ->@is_finite_holomorphic_variety R (coordinate_space (ComplexScalars.C R) n) (@holomorphic_coordinate_norm R n)
    (complex_norm_real (@holomorphic_coordinate_norm_laws R n)) U0 S0 ->
  @set_germ (Topological.clone (real_norm_metric_space
    (complex_norm_real (@holomorphic_coordinate_norm_laws R n))) _) 0 S0 = beta ->
  exists mu,exists V S G:'I_mu->set (coordinate_space (ComplexScalars.C R) n),
    @is_holomorphic_finite_stratification R n alpha beta m U0 S0 mu V S G.
Proof.
move=>[U [H [hU0 [hH hAlpha]]]] hNonempty hDepth hU00 hS0 hBeta.
have hBound:=hDepth;rewrite -hAlpha in hBound.
have hAtBound:(@HolomorphicDepth.value R (coordinate_space (ComplexScalars.C R) n) (@standard_hermitian_product R n)
    (@standard_hermitian_productP R n) n (@coordinate_basis (ComplexScalars.C R) n) (@coordinate_basisP (ComplexScalars.C R) n)
    (dual_basis (@coordinate_basisP (ComplexScalars.C R) n))
    (@HolomorphicSetIdeal.value R (coordinate_space (ComplexScalars.C R) n) (@holomorphic_coordinate_norm R n)
      (complex_norm_real (@holomorphic_coordinate_norm_laws R n)) (0%R:coordinate_space (ComplexScalars.C R) n)
      (@set_germ (Topological.clone (real_norm_metric_space
        (complex_norm_real (@holomorphic_coordinate_norm_laws R n))) _) (0%R:coordinate_space (ComplexScalars.C R) n) H))<=m)%N.
  by rewrite hBound.
have [mu [V [S [G [hLaws hInside]]]]]:=@holomorphic_finite_stratification_exists_at_bound R m
  n U H U0 S0 hU0 hH hU00 hS0 hAtBound.
rewrite hAlpha hBeta in hLaws.
exists mu,V,S,G;exact:hLaws.
Qed.
