(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.10, p. 337:
    the original nonregular part has locally finite
    H^(m-1) mass at every source centre.
    Reuse the origin theorem, the exact regular-locus
    translation and Hausdorff isometry invariance. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP RealNormUP NormMetric NormClosureLaws GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness SetGermUP
  HolomorphicVarietyGermUP HolomorphicSetLocalDepth HolomorphicRegularLocusUP
  HolomorphicRegularLocusSourceTranslation HolomorphicOriginSingularMass
  HolomorphicLocalMassTranslation HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_centre_singular_positive_mass]: the
    local positive-dimensional singular-part bound in
    3.4.10, p. 337, at the
    actual original centre. All regular-locus criteria
    and holomorphic germs are transported by proved equations. *)
Theorem holomorphic_centre_singular_positive_mass (R:realType) n
    (U S L:set (coordinate_space (ComplexScalars.C R) n)) (a:coordinate_space (ComplexScalars.C R) n) u:
  let hB:=hermitian_real_inner_product (@standard_hermitian_productP R n) in
  let hNX:=complex_norm_real (@holomorphic_coordinate_norm_laws R n) in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  @open T U ->U a ->
  @is_holomorphic_variety_germ R (coordinate_space (ComplexScalars.C R) n) (inner_norm hB) hNX a (@set_germ T a S) ->
  (@holomorphic_set_local_depth R n S a<=u.+1)%N ->
  @is_holomorphic_regular_locus R n u.+1 U S L ->
  exists W:set (coordinate_space (ComplexScalars.C R) n),@open T W /\W a /\
    (@hausdorff_measure R (inner_metric_space hB) (u+u) ((S `\` L) `&` W)< +oo)%E.
Proof.
move=>hB hNX T hU haU hHolomorphic hBound hL.
pose t:=fun x:T=>(a+x:T).
have hT:continuous t:=@real_norm_metric_translate_continuous R (restricted_space (ComplexScalars.embed R) (coordinate_space (ComplexScalars.C R) n))
  (inner_norm hB) hNX a.
have hOpen:@open T (t @^-1` U):=@open_comp T T t U (fun x _=>hT x) hU.
have hZero:(t @^-1` U) 0 by change (U (a+0));rewrite addr0.
have hTranslated:=@holomorphic_set_translated_germ R n S a hHolomorphic.
have hRegular:=@holomorphic_regular_locus_source_translation R n u.+1 U S L (-a) hL.
have hEq (A:set (coordinate_space (ComplexScalars.C R) n)):[set x|A (x-(-a))]=t @^-1` A.
  apply:funext=>x;change (A (x-(-a))=A (a+x));by rewrite opprK addrC.
rewrite !hEq in hRegular.
have [O [hO [hO0 [hOU hMass]]]]:=@holomorphic_origin_singular_positive_mass R n
  (t @^-1` U) (t @^-1` S) (t @^-1` L) u hOpen hZero hTranslated hBound hRegular.
apply:(@holomorphic_local_mass_translation R n (S `\` L) a (u+u)).
exists O;split;first exact:hO.
split;first exact:hO0.
exact:hMass.
Qed.
