(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.10, p. 337:
    a zero-dimensional holomorphic set is regular
    at each of its actual points.
    The exceptional family has only empty germs;
    the printed negative-degree expression is unnecessary. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct InnerNorm HilbertFormCompactness SetGermUP SetGermOrder
  SetGermBoundary SetGermCentreMember FiniteSetGermUnionOrder HolomorphicVarietyGermUP
  HolomorphicGermVanishingSealed HolomorphicDepthSealed HolomorphicRegularLocusUP HolomorphicOriginSingularExceptions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_origin_zero_regular]: the
    zero-dimensional endpoint of the regular-part
    assertion in 3.4.10, p. 337.
    The proved exceptional family is empty
    as a germ; an actual nonregular
    centre would give a nonempty contained germ. *)
Theorem holomorphic_origin_zero_regular (R:realType) n (U S L:set (coordinate_space (ComplexScalars.C R) n)):
  let hB:=hermitian_real_inner_product (@standard_hermitian_productP R n) in
  let NX:=@holomorphic_coordinate_norm R n in
  let hNX:=complex_norm_real (@holomorphic_coordinate_norm_laws R n) in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  @open T U ->U 0 ->
  @is_holomorphic_variety_germ R (coordinate_space (ComplexScalars.C R) n) NX hNX 0 (@set_germ T 0 S) ->
  (@HolomorphicDepth.value R (coordinate_space (ComplexScalars.C R) n) (@standard_hermitian_product R n) (@standard_hermitian_productP R n) n
    (@coordinate_basis (ComplexScalars.C R) n) (@coordinate_basisP (ComplexScalars.C R) n) (dual_basis (@coordinate_basisP (ComplexScalars.C R) n))
    (@HolomorphicSetIdeal.value R (coordinate_space (ComplexScalars.C R) n) NX hNX 0%R (@set_germ T 0%R S))<=0)%N ->
  @is_holomorphic_regular_locus R n 0 U S L ->S 0 ->L 0.
Proof.
move=>hB NX hNX T hU hU0 hS hDepth hL hS0.
have [J [W [A [nu [hW [hW0 [hWU [hCover hNu]]]]]]]]:=
  @holomorphic_origin_singular_exceptions R n U S L 0 hU hU0 hS hDepth hL.
have hEmpty j:nu j=@set_germ T 0 set0.
  case:(hNu j).2.2=>h;first exact:h.
  by rewrite ltn0 in h.
have hAEmpty j:@set_germ T 0 (A j)=@set_germ T 0 set0.
  apply:set_germ_subset_empty;rewrite -(hEmpty j);exact:(hNu j).2.1.
have hUnion:=@finite_set_germ_empty_union T 0 J A hAEmpty.
have hSub:set_germ_subset (@set_germ T 0 (S `\` L)) (@set_germ T 0 (\bigcup_j A j)).
  apply/set_germ_subset_original;exists W;split;first exact:hW.
  split;first exact:hW0.
  move=>x hx hxW;exact:hCover x (conj hx hxW).
rewrite hUnion in hSub.
have hSingularEmpty:=set_germ_subset_empty hSub.
apply:contrapT=>hNot.
exact:(@set_germ_centre_member_nonempty T 0 (S `\` L) (conj hS0 hNot) hSingularEmpty).
Qed.
