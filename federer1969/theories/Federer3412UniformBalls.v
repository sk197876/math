(** Federer (1969), 3.4.12, p. 339, extending 3.4.9, p. 337:
    every sufficiently small positive radius gives the
    original corrected stratification with a common ball
    neighbourhood. The strata themselves are retained and
    restricted; the radius has no exceptional-value condition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import NormOpenDomainLaws NormBoundedLinearTopology FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
  EuclideanInnerProduct InnerNorm HilbertFormCompactness SetGermUP HolomorphicVarietyGermUP
  FiniteHolomorphicVarietyUP HolomorphicGermVanishingSealed HolomorphicDepthSealed HolomorphicFiniteStratificationUP
  HolomorphicFiniteStratificationExistence Federer3412Stratification
  HolomorphicStratificationBallRestriction FiniteNormCommonClosedBall MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_3_4_12_families_uniform_balls]: the entire second
    assertion of 3.4.12, p. 339, extending 3.4.9, p. 337, with all
    corrected conclusions of 3.4.8(11). The original
    hypotheses alone choose the strata and common radius. *)
Theorem federer_3_4_12_families_uniform_balls (R:realType) n
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
  exists mu,exists V S G:'I_mu->set (coordinate_space (ComplexScalars.C R) n),exists rho:R,
    0<rho /\@is_holomorphic_finite_stratification R n alpha beta m U0 S0 mu V S G /\
    forall r:R,0<r ->r<rho ->
      @is_holomorphic_finite_stratification R n alpha beta m U0 S0 mu
        (fun _=>[set x|@holomorphic_coordinate_norm R n x<r])
        (fun i=>[set x|@holomorphic_coordinate_norm R n x<r] `&` S i)
        (fun i=>[set x|@holomorphic_coordinate_norm R n x<r] `&` G i).
Proof.
move=>hAlpha hNonempty hDepth hU00 hS0 hBeta.
have [mu [V [S [G hLaws]]]]:=@federer_3_4_12_11 R n alpha beta m U0 S0
  hAlpha hNonempty hDepth hU00 hS0 hBeta.
pose X:=coordinate_space (ComplexScalars.C R) n.
pose NX:=@holomorphic_coordinate_norm R n.
pose hNX:=complex_norm_real (@holomorphic_coordinate_norm_laws R n).
pose T:=Topological.clone (real_norm_metric_space hNX) _.
have hEach i:@open (real_norm_metric_space hNX) (V i) /\V i 0.
  have [hOpen [hZero hInside]]:=holomorphic_stratification_neighbourhoods hLaws i;by split.
have [rho [hRho hCommon]]:=@finite_norm_common_closed_ball R (restricted_space (ComplexScalars.embed R) X) NX hNX
  (Finite.clone 'I_mu _) U0 V hS0.1 hU00 hEach.
exists mu,V,S,G,rho;split;first exact:hRho.
split;first exact:hLaws.
move=>r hR hUpper.
have hBall:@open T [set x|NX x<r].
  rewrite openE=>x hx.
  apply:(@norm_domain_interior_neighbourhood R (restricted_space (ComplexScalars.embed R) X)
    NX hNX [set x|NX x<r] x).1.
  have hSame:(fun y:restricted_space (ComplexScalars.embed R) X=>is_true (NX (y-0)<r))=
      (fun y:restricted_space (ComplexScalars.embed R) X=>is_true (NX y<r)).
    apply:funext=>y.
    exact:(congr1 (fun z:restricted_space (ComplexScalars.embed R) X=>is_true (NX z<r))
      (@subr0 [the zmodType of restricted_space (ComplexScalars.embed R) X] y)).
  have hInterior:=@norm_open_ball_domain_interior R (restricted_space (ComplexScalars.embed R) X)
    NX hNX 0 r x.
  rewrite hSame in hInterior.
  apply:hInterior.
  exact:(eq_ind_r (fun y:restricted_space (ComplexScalars.embed R) X=>is_true (NX y<r)) hx
    (@subr0 [the zmodType of restricted_space (ComplexScalars.embed R) X] x)).
have hClosed i:[set x|NX x<=r] `<=` V i.
  move=>x hx;exact:(hCommon r hR hUpper x hx).2 i.
have hInside:[set x|NX x<r] `<=` U0.
  move=>x hx;exact:(hCommon r hR hUpper x (ltW hx)).1.
exact:(@holomorphic_stratification_ball_restriction R n alpha beta m U0 S0 mu V S G r
  hLaws hR hBall hInside hClosed).
Qed.
