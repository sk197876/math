(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.10, p. 337:
    every point of the original domain has
    a neighbourhood on which the nonregular part
    is covered by finitely many holomorphic manifolds
    of dimension less than the actual global dimension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP RealNormUP NormMetric GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness HolomorphicVarietyGermUP
  HolomorphicSetLocalDepth HolomorphicSetDimension BoundedNaturalSupremumUP
  HolomorphicSetNonemptyCentres HolomorphicRegularLocusUP HolomorphicRegularLocusSealed
  HolomorphicSubmanifoldUP HolomorphicCentreSingularManifoldCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [federer_3_4_12_global_local_singular_cover]: the
    finite local cover behind the globally locally
    finite family in 3.4.10, p. 337.
    At points outside the original holomorphic set,
    its proved relative closedness supplies an empty
    local cover. The regular part remains opaque. *)
Theorem federer_3_4_12_global_local_singular_cover (R:realType) n (U S:set (coordinate_space (ComplexScalars.C R) n)) u:
  let X:=coordinate_space (ComplexScalars.C R) n in
  let hB:=hermitian_real_inner_product (@standard_hermitian_productP R n) in
  let hNX:=complex_norm_real (@holomorphic_coordinate_norm_laws R n) in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  @open T U ->S `<=` U ->
  @is_holomorphic_set_in R X (inner_norm hB) hNX U S ->
  @holomorphic_set_dimension R n S=u.+1 ->
  forall a,U a ->exists W:set X,exists F:set (set X),
    @open T W /\W a /\W `<=` U /\finite_set F /\
    (forall P,F P ->exists d,(d<u.+1)%N /\@is_holomorphic_submanifold R (coordinate_space (ComplexScalars.C R) n) (@holomorphic_coordinate_norm R n) (complex_norm_real (@holomorphic_coordinate_norm_laws R n)) d P) /\
    (S `\` @HolomorphicRegularLocus.value R n u.+1 U S) `&` W `<=` \bigcup_(P in F) P.
Proof.
move=>X hB hNX T hU hSU hHolomorphic hDimension a haU.
case:(pselect (S a))=>haS.
- have hBound:(@holomorphic_set_local_depth R n S a<=u.+1)%N.
    rewrite -hDimension.
    exact:(@bounded_natural_supremum_upper X S (@holomorphic_set_local_depth R n S)
      (@holomorphic_set_dimension R n S) (@holomorphic_set_dimension_laws R n S) a haS).
  exact:(@holomorphic_centre_singular_manifold_cover R n U S
    (@HolomorphicRegularLocus.value R n u.+1 U S) a u hU haU
    (hHolomorphic a haU) hBound (@HolomorphicRegularLocus.laws R n u.+1 U S)).
- have [V [hV [hVa hEmpty]]]:=@holomorphic_set_outside_empty_neighbourhood R X
    (inner_norm hB) hNX U S a hHolomorphic haU haS.
  exists (U `&` V),set0;split;first exact:openI hU hV.
  split;first by split.
  split;first by move=>x hx;exact:hx.1.
  split;first exact:finite_set0.
  split;first by move=>P.
  move=>x [[hxS _] [_ hxV]];have h:(S `&` V) x by split.
  by rewrite hEmpty in h.
Qed.
