(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.10, p. 337:
    locally cover the actual nonregular part by
    finitely many holomorphic manifolds of smaller dimension.
    Apply the proved stratification to its holomorphic
    exceptional germs and retain the actual sets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric GrassmannAbbreviations
  FiniteCoordinates FiniteDualDimension EuclideanInnerProduct InnerNorm HilbertFormCompactness
  SetGermUP SetGermExistence SetGermOrder HolomorphicVarietyGermUP HolomorphicGermVanishingSealed
  HolomorphicDepthSealed HolomorphicSubmanifoldUP HolomorphicRegularLocusUP
  HolomorphicOriginSingularExceptions HolomorphicGermManifoldFamily FiniteSetGermUnionOrder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SingularCover.
Variable R:realType.
Variable n:nat.
Local Notation X:=(coordinate_space (ComplexScalars.C R) n).
Local Notation hB:=(hermitian_real_inner_product (@standard_hermitian_productP R n)).
Local Notation NX:=(@holomorphic_coordinate_norm R n).
Local Notation hNX:=(complex_norm_real (@holomorphic_coordinate_norm_laws R n)).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation germ:=(@set_germ T 0).
Local Notation ideal:=(@HolomorphicSetIdeal.value R X NX hNX 0).
Local Notation depth:=(@HolomorphicDepth.value R X (@standard_hermitian_product R n)
  (@standard_hermitian_productP R n) n (@coordinate_basis (ComplexScalars.C R) n) (@coordinate_basisP (ComplexScalars.C R) n)
  (dual_basis (@coordinate_basisP (ComplexScalars.C R) n))).

(** Source for [holomorphic_origin_singular_manifold_cover]: the
    local covering assertion underlying the globally
    locally finite family in 3.4.10, p. 337.
    Finiteness and the strict dimension bound follow
    from the actual exceptional germs, without assuming
    the singular set itself to be holomorphic. *)
Theorem holomorphic_origin_singular_manifold_cover (U S L:set X) u:
  @open T U ->U 0 ->
  @is_holomorphic_variety_germ R X NX hNX 0 (germ S) ->
  (depth (ideal (germ S))<=u.+1)%N ->
  @is_holomorphic_regular_locus R n u.+1 U S L ->
  exists W:set X,exists F:set (set X),
    @open T W /\W 0 /\W `<=` U /\finite_set F /\
    (forall P,F P ->exists d,(d<u.+1)%N /\@is_holomorphic_submanifold R (coordinate_space (ComplexScalars.C R) n) (@holomorphic_coordinate_norm R n) (complex_norm_real (@holomorphic_coordinate_norm_laws R n)) d P) /\
    (S `\` L) `&` W `<=` \bigcup_(P in F) P.
Proof.
move=>hU hU0 hS hDepth hL.
have [J [V [A [nu [hV [hV0 [hVU [hCover hNu]]]]]]]]:=
  @holomorphic_origin_singular_exceptions R n U S L u.+1 hU hU0 hS hDepth hL.
have hEach j:exists F:set (set X),finite_set F /\
    (forall P,F P ->exists d,(d<=u)%N /\@is_holomorphic_submanifold R (coordinate_space (ComplexScalars.C R) n) (@holomorphic_coordinate_norm R n) (complex_norm_real (@holomorphic_coordinate_norm_laws R n)) d P) /\
    set_germ_subset (germ (A j)) (germ (\bigcup_(P in F) P)).
  apply:(@holomorphic_germ_manifold_family R n (A j) (nu j) u (hNu j).1 (hNu j).2.1).
  case:(hNu j).2.2=>h;first by left.
  right;by move:h;rewrite ltnS.
have [B hBFamily]:=choice hEach.
pose F:set (set X):=\bigcup_j B j.
have hFinite:finite_set F.
  apply:bigcup_finite;first exact:(@finite_finset J setT).
  by move=>j _;exact:(hBFamily j).1.
have hUnion:(\bigcup_j (\bigcup_(P in B j) P))=\bigcup_(P in F) P.
  apply/seteqP;split.
  - move=>x [j _ [P hP hx]];exists P;[by exists j|exact:hx].
  - move=>x [P [j _ hP] hx];exists j;first exact:Logic.I.
    by exists P.
have hGerms:=@finite_set_germ_union_monotone T 0 J A
  (fun j=>\bigcup_(P in B j) P) (fun j=>(hBFamily j).2.2).
rewrite hUnion in hGerms.
have hOriginal:set_germ_subset (germ (S `\` L)) (germ (\bigcup_j A j)).
  apply/set_germ_subset_original;exists V;split;first exact:hV.
  split;first exact:hV0.
  move=>x hx hxV;exact:hCover x (conj hx hxV).
have hAll:=set_germ_subset_transitive hOriginal hGerms.
have [O [hO [hO0 hLocal]]]:=(@set_germ_subset_original T 0
  (S `\` L) (\bigcup_(P in F) P)).1 hAll.
exists (V `&` O),F;split;first exact:openI hV hO.
split;first by split.
split;first by move=>x hx;exact:hVU x hx.1.
split;first exact:hFinite.
split.
- move=>P [j _ hP];have [d [hD hManifold]]:=(hBFamily j).2.1 P hP.
  exists d;split;last exact:hManifold.
  by rewrite ltnS.
- move=>x [hx hxW];exact:hLocal x hx hxW.2.
Qed.
End SingularCover.
