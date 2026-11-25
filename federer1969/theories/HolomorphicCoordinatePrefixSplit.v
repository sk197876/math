(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(8),
    p. 329: the original last complex coordinate splits
    from its prefix with the original inherited norm.
    Use field coordinate laws and the standard Hermitian product. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexScalarLaws ComplexNormUP
  ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicLinear LinearBasis FiniteCoordinates FieldCoordinateFunctional
  FieldCoordinateExpansion FieldPrefixCoordinatesUP FieldPrefixCoordinateLaws
  StandardHermitian HermitianRealImaginary InnerNorm HilbertFormCompactness NormFiniteLinearBound
  ComplexWeierstrassTransverseUP HolomorphicCoordinateNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory ComplexScalarTheory.
Local Open Scope ring_scope.
Section Split.
Variable R:realType.
Variable j:nat.
Local Notation C:=(ComplexScalars.C R).
Local Notation X:=(coordinate_space C j.+1).
Local Notation K:=(coordinate_space C j).
Local Notation omega:=(fun i:'I_j.+1=>@field_coordinate_functional C j.+1 i).
Variable P:Hom X K.
Variable S:Hom K X.
Hypothesis hP:is_field_prefix_projection omega (leqnSn j) P.
Hypothesis hS:is_field_prefix_section (@coordinate_basis C j.+1) (leqnSn j) S.
Local Notation NX:=(@holomorphic_coordinate_norm R j.+1).
Local Notation NK:=(@holomorphic_coordinate_norm R j).

(** Source for [holomorphic_coordinate_prefix_dual]: the original
    dual coordinate equation, 3.4.12, p. 339. *)
Lemma holomorphic_coordinate_prefix_dual i k:omega i (@coordinate_basis C j.+1 k)=if i==k then 1 else 0.
Proof. by rewrite /field_coordinate_functional /= /coordinate_basis ffunE eq_sym. Qed.

(** Source for [holomorphic_coordinate_prefix_section_sum]: the
    original prefix inclusion has its actual finite expansion,
    supporting 3.4.12, p. 339. *)
Lemma holomorphic_coordinate_prefix_section_sum (y:K):
  S y=\sum_(i<j) y i*:@coordinate_basis C j.+1 (widen_ord (leqnSn j) i).
Proof.
rewrite -{1}(field_coordinate_expansion y) linear_sum /=.
apply:eq_bigr=>i _;by rewrite linearZ /= hS.
Qed.

(** Source for [holomorphic_coordinate_prefix_section_last]: the
    original included prefix has zero last coordinate,
    3.4.12, p. 339. *)
Lemma holomorphic_coordinate_prefix_section_last (y:K):omega ord_max (S y)=0.
Proof.
rewrite holomorphic_coordinate_prefix_section_sum linear_sum /=.
apply:big1=>i _.
rewrite ffunE /coordinate_basis ffunE.
have hDifferent:ord_max!=widen_ord (leqnSn j) i.
  apply/eqP=>hEqual;have hValues:=congr1 (fun t:'I_j.+1=>(t:nat)) hEqual.
  change (j=(i:nat)) in hValues.
  have hSmall:(j<j)%N by rewrite {1}hValues;exact:ltn_ord i.
  by rewrite ltnn in hSmall.
by rewrite (negbTE hDifferent) scaler0.
Qed.

(** Source for [holomorphic_coordinate_prefix_section_first]: the
    original included prefix retains each first coordinate,
    3.4.12, p. 339. *)
Lemma holomorphic_coordinate_prefix_section_first (y:K) (i:'I_j):
  S y (widen_ord (leqnSn j) i)=y i.
Proof.
have hSection:=@field_prefix_projection_section C X j.+1 (@coordinate_basis C j.+1)
  omega j (leqnSn j) P S holomorphic_coordinate_prefix_dual hP hS y.
have hValue:=congr1 (fun z:K=>z i) hSection.
by rewrite hP in hValue.
Qed.

(** Source for [holomorphic_coordinate_prefix_section_norm]: the
    prefix has precisely the inherited original Hermitian norm,
    3.4.12, p. 339. *)
Lemma holomorphic_coordinate_prefix_section_norm (y:K):NX (S y)=NK y.
Proof.
apply:inner_norm_value;first exact:inner_norm_nonnegative.
rewrite /holomorphic_coordinate_norm inner_norm_sqr.
change (ComplexScalars.re (standard_hermitian_product y y)=
  ComplexScalars.re (standard_hermitian_product (S y) (S y))).
rewrite !standard_hermitian_diagonal big_ord_recr.
have hLast:S y ord_max=0:=holomorphic_coordinate_prefix_section_last y.
rewrite hLast /norm_square re_zero im_zero !expr0n /= !addr0.
apply:eq_bigr=>i _;by rewrite holomorphic_coordinate_prefix_section_first.
Qed.

(** Source for [holomorphic_last_coordinate_prefix_split]: the
    actual original prefix satisfies every transverse law for
    complex division and preparation, 3.4.12, p. 339. *)
Theorem holomorphic_last_coordinate_prefix_split:
  is_complex_weierstrass_transverse_space NX NK (@coordinate_basis C j.+1 ord_max) (omega ord_max) S P.
Proof.
have hProjection x:S (P x)=x-(omega ord_max x)*:@coordinate_basis C j.+1 ord_max.
  have hSP:S (P x)=\sum_(i<j) x (widen_ord (leqnSn j) i)*:@coordinate_basis C j.+1 (widen_ord (leqnSn j) i).
    rewrite holomorphic_coordinate_prefix_section_sum;apply:eq_bigr=>i _;by rewrite hP.
  have hExpansion:=field_coordinate_expansion x.
  rewrite big_ord_recr in hExpansion.
  rewrite -{2}hExpansion addrK.
  exact:hSP.
constructor.
- by rewrite holomorphic_coordinate_prefix_dual eqxx.
- exact:holomorphic_coordinate_prefix_section_last.
- exact:hProjection.
- exact:(@field_prefix_projection_section C X j.+1 (@coordinate_basis C j.+1) omega j
    (leqnSn j) P S holomorphic_coordinate_prefix_dual hP hS).
- exact:holomorphic_coordinate_prefix_section_norm.
- exact:(@norm_finite_linear_bounded R (restricted_space (ComplexScalars.embed R) K)
    (restricted_space (ComplexScalars.embed R) X) NK NX
    (complex_norm_real (@holomorphic_coordinate_norm_laws R j))
    (complex_norm_real (@holomorphic_coordinate_norm_laws R j.+1)) (j+j)
    (ordered_real_basis (@coordinate_basis C j)) (ordered_real_basisP (@coordinate_basisP C j)) (complex_hom_real S)).
- exact:(@norm_finite_linear_bounded R (restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) K) NX NK
    (complex_norm_real (@holomorphic_coordinate_norm_laws R j.+1))
    (complex_norm_real (@holomorphic_coordinate_norm_laws R j)) (j.+1+j.+1)
    (ordered_real_basis (@coordinate_basis C j.+1)) (ordered_real_basisP (@coordinate_basisP C j.+1)) (complex_hom_real P)).
Qed.
End Split.
