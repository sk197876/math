(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.10, p. 337:
    the actual nonregular part is covered by
    holomorphic manifolds of strictly smaller dimension,
    and each compact subset of the original
    domain meets only finitely many members.
    Dimension zero is included through its empty
    nonregular part. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP RealNormUP NormMetric GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness InnerNormTopologyAdapters
  HolomorphicVarietyGermUP HolomorphicSetDimension HolomorphicRegularLocusSealed
  HolomorphicSubmanifoldUP Federer3412GlobalZeroRegular Federer3412GlobalLocalSingularCover
  HolomorphicLocallyFiniteManifoldCover LocallyFiniteFamilyUP LocallyFiniteFamilyCompact.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [federer_3_4_12_global_manifold_cover]: the
    original manifold-cover assertion of 3.4.10,
    p. 337, with its literal finite
    incidence condition for every compact C in U.
    The set covered is the difference from
    the original opaque regular part, which is
    not assumed to be holomorphic. *)
Theorem federer_3_4_12_global_manifold_cover (R:realType) n (U S:set (coordinate_space (ComplexScalars.C R) n)) m:
  let X:=coordinate_space (ComplexScalars.C R) n in
  let hB:=hermitian_real_inner_product (@standard_hermitian_productP R n) in
  let hNX:=complex_norm_real (@holomorphic_coordinate_norm_laws R n) in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  let E:=inner_metric_space hB in
  @open T U ->S `<=` U ->
  @is_holomorphic_set_in R X (inner_norm hB) hNX U S ->
  @holomorphic_set_dimension R n S=m ->
  exists F:set (set X),
    S `\` @HolomorphicRegularLocus.value R n m U S `<=` \bigcup_(P in F) P /\
    (forall P,F P ->exists d,(d<m)%N /\@is_holomorphic_submanifold R (coordinate_space (ComplexScalars.C R) n) (@holomorphic_coordinate_norm R n) (complex_norm_real (@holomorphic_coordinate_norm_laws R n)) d P) /\
    forall C:set X,@compact E C ->C `<=` U ->
      finite_set (F `&` [set P|exists x,C x /\P x]).
Proof.
move=>X hB hNX T E hU hSU hHolomorphic.
case:m=>[|u] hDimension.
- have hRegular:=@federer_3_4_12_global_zero_regular R n U S hU hSU hHolomorphic hDimension.
  exists set0;split.
  + rewrite hRegular;by move=>x [hx hNot].
  split;first by move=>P.
  move=>C hC hCU;rewrite set0I;exact:finite_set0.
- pose L:=@HolomorphicRegularLocus.value R n u.+1 U S.
  have hLocal a:U a ->exists W:set X,exists F:set (set X),
      @open T W /\W a /\W `<=` U /\finite_set F /\
      (forall P,F P ->exists d,(d<=u)%N /\
        @is_holomorphic_submanifold R X (@holomorphic_coordinate_norm R n) hNX d P) /\
      (S `\` L) `&` W `<=` \bigcup_(P in F) P.
    move=>ha;exact:(@federer_3_4_12_global_local_singular_cover R n U S u
      hU hSU hHolomorphic hDimension a ha).
  have hAU:(S `\` L) `<=` U by move=>x hx;exact:hSU x hx.1.
  have [F [hCover [hPieces hCompact]]]:=@holomorphic_locally_finite_manifold_cover R n
    U (S `\` L) u hU hAU hLocal.
  exists F;split;first exact:hCover.
  split;last exact:hCompact.
  move=>P hP;have [d [hD hManifold]]:=hPieces P hP.
  exists d;split;last exact:hManifold.
  by rewrite ltnS.
Qed.
