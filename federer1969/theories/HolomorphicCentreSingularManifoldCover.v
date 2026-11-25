(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.10, p. 337:
    return the finite local lower-dimensional manifold
    cover to the original centre. All actual
    sets and their holomorphic charts are translated
    by the previously proved source-translation laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP RealNormUP NormMetric NormClosureLaws GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness SetGermUP HolomorphicVarietyGermUP
  HolomorphicSetLocalDepth HolomorphicRegularLocusUP HolomorphicRegularLocusSourceTranslation
  HolomorphicSubmanifoldUP HolomorphicSubmanifoldSourceTranslation HolomorphicOriginSingularManifoldCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_centre_singular_manifold_cover]: the
    all-centre local form of the manifold-cover
    assertion of 3.4.10, p. 337.
    This only transports the already proved original
    exceptional-family cover; no new stratification is needed. *)
Theorem holomorphic_centre_singular_manifold_cover (R:realType) n
    (U S L:set (coordinate_space (ComplexScalars.C R) n)) (a:coordinate_space (ComplexScalars.C R) n) u:
  let X:=coordinate_space (ComplexScalars.C R) n in
  let hB:=hermitian_real_inner_product (@standard_hermitian_productP R n) in
  let hNX:=complex_norm_real (@holomorphic_coordinate_norm_laws R n) in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  @open T U ->U a ->
  @is_holomorphic_variety_germ R X (inner_norm hB) hNX a (@set_germ T a S) ->
  (@holomorphic_set_local_depth R n S a<=u.+1)%N ->
  @is_holomorphic_regular_locus R n u.+1 U S L ->
  exists W:set X,exists F:set (set X),
    @open T W /\W a /\W `<=` U /\finite_set F /\
    (forall P,F P ->exists d,(d<u.+1)%N /\@is_holomorphic_submanifold R (coordinate_space (ComplexScalars.C R) n) (@holomorphic_coordinate_norm R n) (complex_norm_real (@holomorphic_coordinate_norm_laws R n)) d P) /\
    (S `\` L) `&` W `<=` \bigcup_(P in F) P.
Proof.
move=>X hB hNX T hU haU hHolomorphic hBound hL.
pose t:=fun x:T=>(a+x:T).
pose v:=fun x:T=>(x-a:T).
have hT:continuous t:=@real_norm_metric_translate_continuous R (restricted_space (ComplexScalars.embed R) X)
  (inner_norm hB) hNX a.
have hV:continuous v.
  have hSame:v=(fun x:T=>(-a+x:T)) by apply:funext=>x;rewrite /v addrC.
  rewrite hSame;exact:real_norm_metric_translate_continuous.
have hVT:cancel t v by move=>x;rewrite /t /v addrAC subrr add0r.
have hTV:cancel v t by move=>x;rewrite /t /v addrC subrK.
have hOpen:@open T (t @^-1` U):=@open_comp T T t U (fun x _=>hT x) hU.
have hZero:(t @^-1` U) 0 by change (U (a+0));rewrite addr0.
have hTranslated:=@holomorphic_set_translated_germ R n S a hHolomorphic.
have hRegular:=@holomorphic_regular_locus_source_translation R n u.+1 U S L (-a) hL.
have hEq (A:set X):[set x|A (x-(-a))]=t @^-1` A.
  apply:funext=>x;change (A (x-(-a))=A (a+x));by rewrite opprK addrC.
rewrite !hEq in hRegular.
have [O [B [hO [hO0 [hOU [hFinite [hPieces hCover]]]]]]]:=
  @holomorphic_origin_singular_manifold_cover R n (t @^-1` U) (t @^-1` S)
    (t @^-1` L) u hOpen hZero hTranslated hBound hRegular.
pose imagePiece:=fun P:set X=>v @^-1` P.
exists (v @^-1` O),(imagePiece @` B);split.
- exact:(@open_comp T T v O (fun x _=>hV x) hO).
split;first by change (O (a-a));rewrite subrr.
split.
- move=>x hx;have h:=hOU (v x) hx.
  change (U (t (v x))) in h;by rewrite hTV in h.
split;first exact:finite_image imagePiece hFinite.
split.
- move=>P [Q hQ <-];have [d [hD hManifold]]:=hPieces Q hQ.
  exists d;split;first exact:hD.
  exact:(@holomorphic_submanifold_source_translation R n d Q a hManifold).
- move=>x [[hxS hxNotL] hxO].
  have hAt:(((t @^-1` S) `\` (t @^-1` L)) `&` O) (v x).
    split;last exact:hxO.
    change (S (t (v x)) /\~L (t (v x)));by rewrite hTV.
  have [P hP hxP]:=hCover (v x) hAt.
  exists (imagePiece P);[by exists P|exact:hxP].
Qed.
