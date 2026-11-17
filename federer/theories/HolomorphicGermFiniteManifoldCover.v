(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.10, p. 337:
    a set germ contained in a holomorphic germ
    of dimension at most k has a finite
    local cover by holomorphic manifolds of dimension
    at most k. Apply the already proved
    corrected stratification; empty germs remain explicit. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric GrassmannAbbreviations
  FiniteCoordinates FiniteDualDimension EuclideanInnerProduct InnerNorm HilbertFormCompactness
  SetGermUP SetGermSealed SetGermLaws SetGermExistence SetGermOrder
  HolomorphicVarietyGermUP FiniteHolomorphicVarietyUP FiniteHolomorphicVarietyBoundary
  HolomorphicGermVanishingSealed HolomorphicDepthSealed HolomorphicFiniteStratificationUP
  HolomorphicFiniteStratificationExistence FunctionalHolomorphicManifold HolomorphicSubmanifoldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ManifoldCover.
Variable R:realType.
Variable n:nat.
Local Notation X:=(coordinate_space (ComplexScalars.C R) n).
Local Notation hB:=(hermitian_real_inner_product (@standard_hermitian_productP R n)).
Local Notation NX:=(@holomorphic_coordinate_norm R n).
Local Notation hNX:=(complex_norm_real (@holomorphic_coordinate_norm_laws R n)).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation G0:=(@set_germ_space T 0).
Local Notation germ:=(@set_germ T 0).
Local Notation ideal:=(@HolomorphicSetIdeal.value R X NX hNX 0).
Local Notation depth:=(@HolomorphicDepth.value R X (@standard_hermitian_product R n)
  (@standard_hermitian_productP R n) n (@coordinate_basis (ComplexScalars.C R) n) (@coordinate_basisP (ComplexScalars.C R) n)
  (dual_basis (@coordinate_basisP (ComplexScalars.C R) n))).

(** Source for [holomorphic_germ_finite_manifold_cover]: the
    local finite cover used in 3.4.10,
    p. 337. All manifold pieces and their
    dimensions are chosen from corrected 3.4.12, p. 339, extending 3.4.8(11),
    p. 327; no dimension or covering conclusion
    is assumed for the original set. *)
Theorem holomorphic_germ_finite_manifold_cover (A:set X) (nu:G0) k:
  @is_holomorphic_variety_germ R X NX hNX 0 nu ->
  set_germ_subset (germ A) nu ->
  (nu=germ set0 \/(depth (ideal nu)<=k)%N) ->
  exists J:finType,exists F:J->set X,exists d:J->nat,
    (forall j,(d j<=k)%N /\@is_holomorphic_submanifold R (coordinate_space (ComplexScalars.C R) n) (@holomorphic_coordinate_norm R n) (complex_norm_real (@holomorphic_coordinate_norm_laws R n)) (d j) (F j)) /\
    set_germ_subset (germ A) (germ (\bigcup_j F j)).
Proof.
move=>hNu hSub [hEmpty|hDepth].
- exists (Finite.clone unit _),(fun _=>set0),(fun _=>0%N);split.
  + move=>j;split;first exact:leq0n.
    by move=>x.
  + have hUnion:(\bigcup_(j:unit) (set0:set X))=set0.
      apply/seteqP;split;[by move=>x [j _]|by move=>x].
    by rewrite hUnion -hEmpty.
- have [U [H [hU0 [hH hEquation]]]]:=hNu.
  have hBound:(depth (ideal (germ H))<=k)%N by rewrite hEquation.
  have hVoid:=@finite_holomorphic_variety_domain_empty R X NX hNX U hH.1.
  have [mu [V [F [G [hLaws hInside]]]]]:=@holomorphic_finite_stratification_exists_at_bound R k n
    U H U set0 hU0 hH hU0 hVoid hBound.
  have [d hD]:=choice (fun i=>holomorphic_stratification_functional hLaws i).
  exists (Finite.clone 'I_mu _),F,d;split.
  + move=>j;split;first exact:(hD j).1.
    exact:functional_holomorphic_submanifold_holomorphic (hD j).2.
  + have hUnion:=holomorphic_stratification_germ hLaws.
    rewrite (@set_germ_complement_equation T 0 _ _ _ (@SetGerms.laws T 0)) setC0
      (@set_germ_intersection_equation T 0 _ _ _ (@SetGerms.laws T 0)) setIT in hUnion.
    by rewrite -hUnion hEquation.
Qed.
End ManifoldCover.
