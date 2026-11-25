(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.10, p. 337:
    the nonregular part has locally finite H^(2m-2)
    mass when m is positive. Its actual
    finite exceptional family is already constructed;
    compact germ representatives provide the mass. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  SetGermUP SetGermOrder HolomorphicVarietyGermUP HolomorphicGermVanishingSealed HolomorphicDepthSealed
  HolomorphicRegularLocusUP HolomorphicOriginSingularExceptions HolomorphicGermCompactDomination
  FiniteGermLocalMass HausdorffMeasure MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SingularMass.
Variable R:realType.
Variable n:nat.
Local Notation X:=(coordinate_space (ComplexScalars.C R) n).
Local Notation hB:=(hermitian_real_inner_product (@standard_hermitian_productP R n)).
Local Notation NX:=(@holomorphic_coordinate_norm R n).
Local Notation hNX:=(complex_norm_real (@holomorphic_coordinate_norm_laws R n)).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation E:=(inner_metric_space hB).
Local Notation germ:=(@set_germ T 0).
Local Notation ideal:=(@HolomorphicSetIdeal.value R X NX hNX 0).
Local Notation depth:=(@HolomorphicDepth.value R X (@standard_hermitian_product R n)
  (@standard_hermitian_productP R n) n (@coordinate_basis (ComplexScalars.C R) n) (@coordinate_basisP (ComplexScalars.C R) n)
  (dual_basis (@coordinate_basisP (ComplexScalars.C R) n))).

(** Source for [holomorphic_origin_singular_positive_mass]: the
    local positive-dimensional singular-part mass bound
    underlying 3.4.10, p. 337. All
    compact dominating sets are obtained internally
    from the proved smaller-dimensional holomorphic germs;
    no finite-mass conclusion is assumed. *)
Theorem holomorphic_origin_singular_positive_mass (U S L:set X) u:
  @open T U ->U 0 ->
  @is_holomorphic_variety_germ R X NX hNX 0 (germ S) ->
  (depth (ideal (germ S))<=u.+1)%N ->
  @is_holomorphic_regular_locus R n u.+1 U S L ->
  exists W:set X,@open T W /\W 0 /\W `<=` U /\
    (@hausdorff_measure R E (u+u) ((S `\` L) `&` W)< +oo)%E.
Proof.
move=>hU hU0 hS hDepth hL.
have [J [V [A [nu [hV [hV0 [hVU [hCover hNu]]]]]]]]:=
  @holomorphic_origin_singular_exceptions R n U S L u.+1 hU hU0 hS hDepth hL.
have hEach j:exists K:set X,@compact E K /\
    set_germ_subset (germ (A j)) (germ K) /\(@hausdorff_measure R E (u+u) K< +oo)%E.
  apply:(@holomorphic_germ_compact_domination R n (A j) u (nu j) (hNu j).1 (hNu j).2.1).
  case:(hNu j).2.2=>hDimension;first by left.
  right;by move:hDimension;rewrite ltnS.
have [K hK]:=choice hEach.
have [O [hO [hO0 hMass]]]:=@finite_germ_local_mass R T J 0
  (@hausdorff_measure R E (u+u)) A K (@hausdorff_measure_is_measure R E (u+u))
  (fun j=>(hK j).2.1) (fun j=>(hK j).2.2).
exists (V `&` O);split;first exact:openI hV hO.
split;first by split.
split;first by move=>x hx;exact:hVU x hx.1.
apply:(le_lt_trans (@measure_mono R E (@hausdorff_measure R E (u+u))
  (@hausdorff_measure_is_measure R E (u+u)) ((S `\` L) `&` (V `&` O))
  ((\bigcup_j A j) `&` O) _) hMass).
move=>x [hx [hxV hxO]];split;last exact:hxO.
exact:hCover x (conj hx hxV).
Qed.
End SingularMass.
