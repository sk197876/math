(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.10, p. 337:
    every actual point of a zero-dimensional
    holomorphic set is regular. Translate the proved
    origin assertion and its exact manifold criterion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP RealNormUP NormMetric NormClosureLaws GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness SetGermUP HolomorphicVarietyGermUP
  HolomorphicSetLocalDepth HolomorphicRegularLocusUP HolomorphicRegularLocusSourceTranslation
  HolomorphicOriginZeroRegular.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_centre_zero_regular]: the
    zero-dimensional endpoint of 3.4.10, p. 337.
    The original centre is retained; the
    proof uses no negative measure degree. *)
Theorem holomorphic_centre_zero_regular (R:realType) n
    (U S L:set (coordinate_space (ComplexScalars.C R) n)) (a:coordinate_space (ComplexScalars.C R) n):
  let hB:=hermitian_real_inner_product (@standard_hermitian_productP R n) in
  let hNX:=complex_norm_real (@holomorphic_coordinate_norm_laws R n) in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  @open T U ->U a ->
  @is_holomorphic_variety_germ R (coordinate_space (ComplexScalars.C R) n) (inner_norm hB) hNX a (@set_germ T a S) ->
  (@holomorphic_set_local_depth R n S a<=0)%N ->
  @is_holomorphic_regular_locus R n 0 U S L ->S a ->L a.
Proof.
move=>hB hNX T hU haU hHolomorphic hBound hL haS.
pose t:=fun x:T=>(a+x:T).
have hT:continuous t:=@real_norm_metric_translate_continuous R (restricted_space (ComplexScalars.embed R) (coordinate_space (ComplexScalars.C R) n))
  (inner_norm hB) hNX a.
have hOpen:@open T (t @^-1` U):=@open_comp T T t U (fun x _=>hT x) hU.
have hZero:(t @^-1` U) 0 by change (U (a+0));rewrite addr0.
have hTranslated:=@holomorphic_set_translated_germ R n S a hHolomorphic.
have hRegular:=@holomorphic_regular_locus_source_translation R n 0 U S L (-a) hL.
have hEq (A:set (coordinate_space (ComplexScalars.C R) n)):[set x|A (x-(-a))]=t @^-1` A.
  apply:funext=>x;change (A (x-(-a))=A (a+x));by rewrite opprK addrC.
rewrite !hEq in hRegular.
have hS0:(t @^-1` S) 0 by change (S (a+0));rewrite addr0.
have h:=@holomorphic_origin_zero_regular R n (t @^-1` U) (t @^-1` S) (t @^-1` L)
  hOpen hZero hTranslated hBound hRegular hS0.
change (L (a+0)) in h;by rewrite addr0 in h.
Qed.
