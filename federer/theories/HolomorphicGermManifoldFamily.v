(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.10, p. 337:
    express the proved finite local manifold cover
    as an actual finite family of subsets.
    Removing duplicate indices preserves the cover and
    every original dimension bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric GrassmannAbbreviations
  FiniteCoordinates FiniteDualDimension EuclideanInnerProduct InnerNorm HilbertFormCompactness
  SetGermUP SetGermOrder HolomorphicVarietyGermUP HolomorphicGermVanishingSealed HolomorphicDepthSealed
  HolomorphicSubmanifoldUP HolomorphicGermFiniteManifoldCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_germ_manifold_family]: the
    finite local family used for the manifold
    cover in 3.4.10, p. 337.
    This only converts the already proved indexed
    cover into a family of actual sets. *)
Theorem holomorphic_germ_manifold_family (R:realType) n (A:set (coordinate_space (ComplexScalars.C R) n))
    (nu:@set_germ_space (Topological.clone
      (real_norm_metric_space (complex_norm_real (@holomorphic_coordinate_norm_laws R n))) _) 0) k:
  let X:=coordinate_space (ComplexScalars.C R) n in
  let hB:=hermitian_real_inner_product (@standard_hermitian_productP R n) in
  let NX:=@holomorphic_coordinate_norm R n in
  let hNX:=complex_norm_real (@holomorphic_coordinate_norm_laws R n) in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  @is_holomorphic_variety_germ R X NX hNX 0 nu ->
  set_germ_subset (@set_germ T 0 A) nu ->
  (nu=@set_germ T 0 set0 \/
    (@HolomorphicDepth.value R X (@standard_hermitian_product R n) (@standard_hermitian_productP R n) n
      (@coordinate_basis (ComplexScalars.C R) n) (@coordinate_basisP (ComplexScalars.C R) n) (dual_basis (@coordinate_basisP (ComplexScalars.C R) n))
      (@HolomorphicSetIdeal.value R X NX hNX 0 nu)<=k)%N) ->
  exists F:set (set X),finite_set F /\
    (forall P,F P ->exists d,(d<=k)%N /\@is_holomorphic_submanifold R (coordinate_space (ComplexScalars.C R) n) (@holomorphic_coordinate_norm R n) (complex_norm_real (@holomorphic_coordinate_norm_laws R n)) d P) /\
    set_germ_subset (@set_germ T 0 A) (@set_germ T 0 (\bigcup_(P in F) P)).
Proof.
move=>X hB NX hNX T hNu hSub hBound.
have [J [P [d [hP hCover]]]]:=@holomorphic_germ_finite_manifold_cover R n A nu k hNu hSub hBound.
exists (P @` setT);split;first exact:(finite_image P (@finite_finset J setT)).
split.
- move=>Q [j _ <-];exists (d j);exact:hP j.
- have hUnion:(\bigcup_(Q in P @` setT) Q)=\bigcup_j P j.
    apply/seteqP;split.
    + move=>x [Q [j _ <-] hx];by exists j.
    + move=>x [j _ hx];exists (P j);[by exists j|exact:hx].
  by rewrite hUnion.
Qed.
