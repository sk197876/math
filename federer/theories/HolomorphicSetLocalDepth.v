(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.10, p. 337:
    local dimensions at actual centres, expressed in
    translated original coordinates. The original opaque
    ideal depth remains the only dimension value. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric NormClosureLaws GrassmannAbbreviations
  FiniteCoordinates FiniteDualDimension EuclideanInnerProduct InnerNorm HilbertFormCompactness
  SetGermUP SetGermExistence SetGermContinuousPreimage HolomorphicVarietyGermUP
  FiniteHolomorphicVarietyUP HolomorphicSourceTranslation HolomorphicGermVanishingSealed
  HolomorphicDepthSealed AnalyticReductionDepthUP HolomorphicVarietyGermDimensionSealed
  HolomorphicVarietyGermDimensionLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section LocalDepth.
Variable R:realType.
Variable n:nat.
Local Notation X:=(coordinate_space (ComplexScalars.C R) n).
Local Notation hB:=(hermitian_real_inner_product (@standard_hermitian_productP R n)).
Local Notation NX:=(@holomorphic_coordinate_norm R n).
Local Notation hNX:=(complex_norm_real (@holomorphic_coordinate_norm_laws R n)).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).

(** Source for [holomorphic_set_local_depth]: the original
    dimension at a in 3.4.10, p. 337,
    after translating a to zero. This total ideal
    depth is used as dimension only for nonempty
    holomorphic germs; no empty-germ dimension is defined. *)
Definition holomorphic_set_local_depth (S:set X) (a:X):nat:=
  @HolomorphicDepth.value R X (@standard_hermitian_product R n) (@standard_hermitian_productP R n) n
    (@coordinate_basis (ComplexScalars.C R) n) (@coordinate_basisP (ComplexScalars.C R) n) (dual_basis (@coordinate_basisP (ComplexScalars.C R) n))
    (@HolomorphicSetIdeal.value R X NX hNX 0 (@set_germ T 0 [set x|S (a+x)])).

(** Source for [holomorphic_set_local_depth_bound]: the local
    dimension bound by ambient dimension in 3.4.10,
    p. 337, directly from the existing opaque
    minimum laws of 3.4.8(2), p. 326. *)
Lemma holomorphic_set_local_depth_bound (S:set X) a:(holomorphic_set_local_depth S a<=n)%N.
Proof.
exact:(analytic_reduction_depth_bound (@HolomorphicDepth.laws R X
  (@standard_hermitian_product R n) (@standard_hermitian_productP R n) n (@coordinate_basis (ComplexScalars.C R) n)
  (@coordinate_basisP (ComplexScalars.C R) n) (dual_basis (@coordinate_basisP (ComplexScalars.C R) n))
  (@HolomorphicSetIdeal.value R X NX hNX 0 (@set_germ T 0 [set x|S (a+x)])))).
Qed.

(** Source for [holomorphic_set_translated_germ]: actual local
    holomorphic germs remain holomorphic after changing their
    centre to zero, as used in the dimension
    definition of 3.4.10, p. 337. Reuse
    the original source-translation theorem. *)
Lemma holomorphic_set_translated_germ (S:set X) a:
  @is_holomorphic_variety_germ R X NX hNX a (@set_germ T a S) ->
  @is_holomorphic_variety_germ R X NX hNX 0 (@set_germ T 0 [set x|S (a+x)]).
Proof.
move=>[U [H [haU [hH hGerm]]]].
pose u:=fun x:T=>(a+x:T).
have hU:continuous u:=@real_norm_metric_translate_continuous R (restricted_space (ComplexScalars.embed R) X) NX hNX a.
have hCentre:u 0=a by rewrite /u addr0.
have hVariety:=@finite_holomorphic_variety_source_translation R X NX hNX U H a hH.
have hBack:=@set_germ_continuous_preimage_equality T T u 0 a H S hU hCentre hGerm.
exists (u @^-1` U),(u @^-1` H);split.
- change (U (a+0));by rewrite addr0.
- by split.
Qed.

(** Source for [holomorphic_set_translated_nonempty]: a point
    of S has a nonempty local germ, as
    required for the original dimension in 3.4.10,
    p. 337. This uses only neighbourhood equality. *)
Lemma holomorphic_set_translated_nonempty (S:set X) a:S a ->
  @set_germ T 0 [set x|S (a+x)]<>@set_germ T 0 set0.
Proof.
move=>ha /set_germ_equality_original [U [hU [hU0 hEqual]]].
have hAt:([set x|S (a+x)] `&` U) 0.
  split;last exact:hU0;change (S (a+0));by rewrite addr0.
by rewrite hEqual in hAt;case:hAt=>[].
Qed.
End LocalDepth.
