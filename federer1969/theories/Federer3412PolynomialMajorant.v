(** Federer (1969), 3.4.12, p. 339, extending 3.4.11, p. 338:
    the literal finite set F of complex homogeneous
    polynomial functions contains the whole original tangent
    cone in its global common zero set. The
    original global dimension is bounded by dim gamma_a(S). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import FiniteAnalyticVarietyUP FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness SetGermUP HolomorphicVarietyGermUP HolomorphicSetNonemptyCentres
  HolomorphicSetLocalDepth HolomorphicSetDimension HomogeneousPolynomialFunctions FiniteHolomorphicVarietyUP
  FiniteZeroSetSealed TangentConeUP TangentConeTranslation HolomorphicFiniteHomogeneousMajorant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_3_4_12_tangent_finite_polynomial_majorant]: the
    entire second displayed conclusion of 3.4.12, p. 339, extending 3.4.11, p. 338.
    F is an actual finite set of original homogeneous
    polynomial functions; its global common zero set has
    dimension at most the original source-germ dimension. *)
Theorem federer_3_4_12_tangent_finite_polynomial_majorant (R:realType) n (U S:set (coordinate_space (ComplexScalars.C R) n)) a:
  let X:=coordinate_space (ComplexScalars.C R) n in
  let hB:=hermitian_real_inner_product (@standard_hermitian_productP R n) in
  let NX:=@holomorphic_coordinate_norm R n in
  let hNX:=complex_norm_real (@holomorphic_coordinate_norm_laws R n) in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  @open T U ->S `<=` U ->@is_holomorphic_set_in R X NX hNX U S ->U a ->
  @set_germ T a S<>@set_germ T a set0 ->
  exists F:set (X->ComplexScalars.C R),finite_set F /\
    (forall P,F P ->exists k,(0<k)%N /\@is_homogeneous_polynomial (ComplexScalars.C R) X (ComplexScalars.C R)^o k P) /\
    (@norm_tangent_cone R (restricted_space (ComplexScalars.embed R) X) NX S a `<=` [set v|forall P,F P ->P v=0%R]) /\
    (@holomorphic_set_dimension R n [set v|forall P,F P ->P v=0%R]<=
      @holomorphic_set_local_depth R n S a)%N.
Proof.
move=>X hB NX hNX T hU hSU hHolomorphic haU hSourceNonempty.
have haS:=(@holomorphic_set_nonempty_germ_centres R X NX hNX U S a hHolomorphic haU).1 hSourceNonempty.
have hSource:=@holomorphic_set_translated_germ R n S a (hHolomorphic a haU).
have hNonempty:=@holomorphic_set_translated_nonempty R n S a haS.
have [J [k [P [hPolynomial [hContain hDimension]]]]]:=
  @holomorphic_finite_homogeneous_majorant_exists R n [set x|S (a+x)] hSource hNonempty.
pose F:set (X->ComplexScalars.C R):=P @` setT.
exists F;split;first exact:(finite_image P (@finite_finset J setT)).
split.
- move=>Q [j _ <-];exists (k j);exact:hPolynomial j.
have hEqual:@FiniteZeroSet.value [the zmodType of (ComplexScalars.C R)^o] X setT J P=
    [set v|forall Q,F Q ->Q v=0].
  apply/seteqP;split.
  + move=>v /(@original_zero_set_membership _ _ _ _ _ _ (@FiniteZeroSet.laws _ _ _ _ _)) [_ hV].
    by move=>Q [j _ <-];exact:hV j.
  + move=>v hV;apply/(@original_zero_set_membership _ _ _ _ _ _ (@FiniteZeroSet.laws _ _ _ _ _)).
    split;first done.
    move=>j;apply:hV;by exists j.
rewrite (@norm_tangent_source_translation R (restricted_space (ComplexScalars.embed R) X) NX S a) hEqual in hContain.
rewrite hEqual in hDimension.
by split.
Qed.
