(** Federer (1969), 3.4.12, p. 339: assemble the actual
    local holomorphic manifold covers into one family meeting
    each compact set only finitely often. Reuse the proved
    Euclidean open-piece refinement in the exact paired coordinates. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import Hom RealNormUP NormMetric ScalarRestriction ComplexScalarSealed ComplexNormUP
  FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  StandardHermitian HermitianRealImaginary HolomorphicCoordinateNorm StandardHermitianCoordinates
  ComplexEuclideanCoordinates ComplexEuclideanCoordinateTopology HolomorphicSubmanifoldUP
  HolomorphicSubmanifoldOpenRestriction EuclideanLocallyFiniteOpenPieceRefinement LocallyFiniteFamilyCompact.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_locally_finite_manifold_cover]: the
    complex version of the local-to-global manifold-cover step of
    3.4.10, p. 337, under 3.4.12, p. 339. The
    refinement preserves the original holomorphic charts and complex
    dimensions; the literal compact incidence condition is retained. *)
Theorem holomorphic_locally_finite_manifold_cover (R:realType) n
    (U A:set (coordinate_space (ComplexScalars.C R) n)) k:
  let X:=coordinate_space (ComplexScalars.C R) n in
  let NX:=@holomorphic_coordinate_norm R n in
  let hNX:=complex_norm_real (@holomorphic_coordinate_norm_laws R n) in
  let TX:=real_norm_metric_space hNX in
  let EC:=inner_metric_space (hermitian_real_inner_product (@standard_hermitian_productP R n)) in
  @open TX U ->A `<=` U ->
  (forall a,U a ->exists W:set X,exists F:set (set X),
    @open TX W /\W a /\W `<=` U /\finite_set F /\
    (forall P,F P ->exists d,(d<=k)%N /\@is_holomorphic_submanifold R X NX hNX d P) /\
    A `&` W `<=` \bigcup_(P in F) P) ->
  exists F:set (set X),A `<=` \bigcup_(P in F) P /\
    (forall P,F P ->exists d,(d<=k)%N /\@is_holomorphic_submanifold R X NX hNX d P) /\
    forall C:set X,@compact EC C ->C `<=` U ->finite_set (F `&` [set P|exists x,C x /\P x]).
Proof.
move=>X NX hNX TX EC hU hAU hLocal.
pose Y:=R_n R (n+n).
pose hB:=@euclidean_inner_productP R (n+n).
pose ER:=inner_metric_space hB.
pose u:=@complex_from_real_coordinate_hom R n.
pose v:=@complex_real_coordinate_hom R n.
have hUV:cancel v u:=@complex_real_coordinatesK R n.
have hVU:cancel u v:=@complex_from_real_coordinatesK R n.
have hUContinuous:continuous (fun y:ER=>(u y:TX)):=@complex_from_real_coordinate_hom_continuous R n.
have hVContinuous:continuous (fun x:TX=>(v x:ER)):=@complex_real_coordinate_hom_continuous R n.
have hCancel (S:set X):v @^-1` (u @^-1` S)=S.
  apply:funext=>x;change (S (u (v x))=S x);by rewrite hUV.
pose Piece:=fun d (B:set Y)=>@is_holomorphic_submanifold R X NX hNX d (v @^-1` B).
have hPiece d (B W:set Y):Piece d B ->@open ER W ->Piece d (B `&` W).
  move=>hBMan hW;apply:(holomorphic_submanifold_open_restriction hBMan).
  exact:(@open_comp TX ER v W (fun x _=>hVContinuous x) hW).
have hRealOpen:@open ER (u @^-1` U):=@open_comp ER TX u U (fun x _=>hUContinuous x) hU.
have hRealInside:(u @^-1` A) `<=` (u @^-1` U) by move=>y hy;exact:hAU (u y) hy.
have hRealLocal y (hy:U (u y)):exists W:set ER,exists F:set (set ER),
    @open ER W /\W y /\W `<=` (u @^-1` U) /\finite_set F /\
    (forall P,F P ->exists d,(d<=k)%N /\Piece d P) /\
    (u @^-1` A) `&` W `<=` \bigcup_(P in F) P.
  have [W [F [hW [hWY [hWU [hFinite [hPieces hCover]]]]]]]:=hLocal (u y) hy.
  exists (u @^-1` W),((fun P:set X=>u @^-1` P) @` F);split.
  - exact:(@open_comp ER TX u W (fun x _=>hUContinuous x) hW).
  split;first exact:hWY.
  split;first by move=>z hz;exact:hWU (u z) hz.
  split;first exact:finite_image _ hFinite.
  split.
  - move=>P [S hS <-];have [d [hD hManifold]]:=hPieces S hS.
    exists d;split;first exact:hD.
    by rewrite /Piece hCancel.
  - move=>z hz;have [P hP hzP]:=hCover (u z) hz.
    exists (u @^-1` P);last exact:hzP;by exists P.
have [F [hCover [hPieces hFinite]]]:=@euclidean_locally_finite_open_piece_refinement R (n+n)
  Piece hPiece (u @^-1` U) (u @^-1` A) k hRealOpen hRealInside hRealLocal.
pose imagePiece:=fun P:set Y=>v @^-1` P.
exists (imagePiece @` F);split.
- move=>x hx;have hxReal:(u @^-1` A) (v x) by change (A (u (v x)));rewrite hUV.
  have [P hP hxP]:=hCover (v x) hxReal.
  exists (imagePiece P);last exact:hxP;by exists P.
split.
- move=>P [B hBIn <-];exact:hPieces B hBIn.
- move=>C hCompact hCU.
  have hCompactReal:@compact ER (v @` C).
    exact:continuous_compact (continuous_subspaceT hVContinuous) hCompact.
  have hInsideReal:(v @` C) `<=` (u @^-1` U).
    move=>y [x hx <-];change (U (u (v x)));rewrite hUV;exact:hCU x hx.
  have hFiniteReal:=@locally_finite_family_compact ER [the choiceType of set ER]
    (u @^-1` U) F (fun P=>P) (v @` C) hFinite hCompactReal hInsideReal.
  apply:(sub_finite_set _ (finite_image imagePiece hFiniteReal)).
  move=>P [[B hBIn hEquation] [x [hxC hxP]]].
  exists B;last exact:hEquation.
  split;first exact:hBIn.
  exists (v x);split;first by exists x.
  by rewrite -hEquation in hxP.
Qed.
