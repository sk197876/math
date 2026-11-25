(** Actual-space endpoint regressions for Federer (1969),
    4.1.24, pp. 380–382: empty indices and opens,
    above-dimensional degrees, nonzero and negative R^0
    point currents, the exact integral flat size,
    and the excluded half-point. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology lra.
From Federer Require Import Bilinear Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingZero SmoothCompactSet CurrentSpaces CurrentBoundary FunctionalSupportUP CurrentEvaluation
  CurrentSupportExtensionality CurrentDirac DiracCurrentBounds CurrentMassSealed
  CurrentMassFiniteAlgebra CurrentFiniteMassLinearBound CurrentPointEvaluation
  CurrentFlatNorm IntegralCurrents IntegralPolyhedralZeroLipschitzImage
  FiniteIntegerPointMassGap PolyhedralCurrentAlgebra.
From FedererTests Require Import FlatCurrentEndpointExamples.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section IntegralEmptyIndexEndpoints.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation K:=(@smooth_compact_empty R X NX hNX U).

(** Source for [integer_classes_empty_index_only_zero]:
    all three original same-empty-index integer classes
    are exactly zero, testing 4.1.24, pp. 380–381. *)
Example integer_classes_empty_index_only_zero (T:C):
  (@is_rectifiable_current_supported_in R h2 n m U hU K T<->T=0) /\
  (@is_integral_current_supported_in R h2 n U hU m K T<->T=0) /\
  (@is_integral_flat_current_supported_in R h2 n U hU m K T<->T=0).
Proof.
split;first exact:rectifiable_current_empty_index_iff_zero.
split;[exact:integral_current_empty_index_iff_zero|exact:integral_flat_current_empty_index_iff_zero].
Qed.

(** Source for [integer_classes_above_dimension_endpoint]:
    every actual above-dimensional current remains zero
    in the original integer classes, including empty
    compact indices, 4.1.24, pp. 380–381. *)
Example integer_classes_above_dimension_endpoint
    (L:smooth_compact_set hNX U) (T:C) (hNM:(n<m)%N):
  @is_rectifiable_current_supported_in R h2 n m U hU L T /\
  @is_integral_current_supported_in R h2 n U hU m L T /\
  @is_integral_flat_current_supported_in R h2 n U hU m L T.
Proof. exact:integer_current_classes_above_dimension hNM. Qed.
End IntegralEmptyIndexEndpoints.

Section IntegralEmptyOpenEndpoint.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation U:=(set0:set X).
Local Notation hU:=(fun (x:X) (hx:U x)=>False_ind
  (norm_domain_interior NX U x) hx).
Local Notation K:=(@smooth_compact_empty R X NX hNX U).

(** Source for [integer_empty_open_current_endpoint]: the
    original empty open admits only the actual
    zero current, which belongs to all three
    integer classes, 4.1.24, pp. 380–381. *)
Example integer_empty_open_current_endpoint (T:@current_space R h2 n U hU m):
  T=0 /\@is_rectifiable_current_supported_in R h2 n m U hU K T /\
  @is_integral_current_supported_in R h2 n U hU m K T /\
  @is_integral_flat_current_supported_in R h2 n U hU m K T.
Proof.
have hZero:T=0.
  apply:(@current_empty_support_iff_zero R h2 n m U hU T).1.
  by move=>x hx;exact:hx.1.
rewrite hZero;split;first by [].
split;first exact:rectifiable_current_zero.
split;[exact:integral_current_zero_supported|exact:integral_flat_current_zero_supported].
Qed.
End IntegralEmptyOpenEndpoint.

Section IntegralPointEndpoints.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X:=(R_n R 0%N).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R 0%N)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R 0%N)).
Local Notation U:=(fun _:X=>True).
Local Notation hU:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation C:=(@current_space R h2 0%N U hU 0%N).
Local Notation K:=(@flat_point_singleton_index R).
Local Notation P:=(@dirac_current R h2 0%N U hU (0:X)).
Local Notation Rect:=(@is_rectifiable_current_supported_in R h2 0%N 0%N U hU K).
Local Notation Integral:=(@is_integral_current_supported_in R h2 0%N U hU 0%N K).
Local Notation IF:=(@is_integral_flat_current_supported_in R h2 0%N U hU 0%N K).
Local Notation M:=(@CurrentMass.value R h2 0%N 0%N U hU).

(** Source for [integral_point_rectifiable]: the actual
    nonzero R^0 point belongs to the original
    integer zero-current class, 4.1.24, p. 380. *)
Local Lemma integral_point_rectifiable:Rect P.
Proof.
apply:(@rectifiable_zero_polyhedral_iff R h2 0%N U hU K P).2.
apply:integral_polyhedral_dirac_in_index;by [].
Qed.

(** Source for [integral_point_nonzero]: the retained
    original point current is nonzero, rather than
    a degenerate positive-dimensional simplex, testing
    the zero-degree clause of 4.1.24, p. 380. *)
Local Lemma integral_point_nonzero:P<>0.
Proof.
move=>hZero;have[phi hPhi]:=@dirac_current_unit_test R h2 0%N U hU (0:X) Logic.I.
rewrite hZero (lin0 (hom_linear (@current_value R h2 0%N U hU 0%N))) hom_zeroE in hPhi.
have hBad:(0:R)!=1 by rewrite eq_sym oner_eq0.
by rewrite hPhi eqxx in hBad.
Qed.

(** Source for [integral_point_all_integer_classes]: the
    original R^0 point lies in every original
    integer class and remains nonzero, testing the
    separate degree-zero definition, 4.1.24, pp. 380–381. *)
Example integral_point_all_integer_classes:
  P<>0 /\Rect P /\Integral P /\IF P.
Proof.
split;first exact:integral_point_nonzero.
split;first exact:integral_point_rectifiable.
split;first exact:integral_point_rectifiable.
exact:rectifiable_current_is_integral_flat_supported integral_point_rectifiable.
Qed.

(** Source for [integral_negative_point_endpoint]: negative
    integer multiplicities remain in the original
    additive groups; no positive-coefficient restriction
    replaces their definitions, 4.1.24, pp. 380–381. *)
Example integral_negative_point_endpoint:
  -P<>0 /\Rect (-P) /\Integral (-P) /\IF (-P).
Proof.
have hRect:Rect (-P):=rectifiable_current_negate integral_point_rectifiable.
split.
- move=>hZero;apply:integral_point_nonzero.
  by rewrite -{1}(opprK P) hZero oppr0.
- split;first exact:hRect.
  split;first exact:hRect.
  exact:rectifiable_current_is_integral_flat_supported hRect.
Qed.

(** Source for [integral_point_size_one]: the actual
    opaque integral flat value of the R^0 point
    is one, testing the exact original infimum
    and its sharp ordinary-flat comparison, 4.1.24, p. 382. *)
Example integral_point_size_one (hP:IF P):
  @IntegralFlatSize.value R h2 0%N 0%N U hU K P hP= 1.
Proof.
pose a:=@IntegralFlatSize.value R h2 0%N 0%N U hU K P hP.
pose hSize:=@IntegralFlatSize.laws R h2 0%N 0%N U hU K P hP.
have hLower:=@ordinary_flat_le_integral_flat_size R h2 0%N 0%N U hU K P a hP hSize.
rewrite (@zero_dimensional_point_flat_norm_one R h2) lee_fin in hLower.
have hPair:P= P+@current_boundary R h2 0%N 0%N U hU
    (0:@current_space R h2 0%N U hU 1%N).
  by rewrite (lin0 (hom_linear (@current_boundary R h2 0%N 0%N U hU))) addr0.
have hUpper:=@integral_flat_size_lower R h2 0%N 0%N U hU K P a hSize
  P 0 integral_point_rectifiable (@rectifiable_current_zero R h2 0%N 1%N U hU K) hPair.
rewrite (@zero_dimensional_point_mass_one R h2) current_mass_zero adde0 lee_fin in hUpper.
apply/eqP;by rewrite eq_le hUpper hLower.
Qed.

(** Source for [integral_half_point_excluded]: half of
    the nonzero R^0 point belongs to none
    of the three original integer classes. This
    tests R_0=P-script_0 and excludes accidental
    real-vector-space definitions, 4.1.24, pp. 380–381. *)
Example integral_half_point_excluded:
  ~Rect ((1/2:R)*:P) /\~Integral ((1/2:R)*:P) /\~IF ((1/2:R)*:P).
Proof.
have hNotRect:~Rect ((1/2:R)*:P).
  move=>hRect.
  have hPoly:=(@rectifiable_zero_polyhedral_iff R h2 0%N U hU K ((1/2:R)*:P)).1 hRect.
  have hPBound:(M P<=1)%E by rewrite (@zero_dimensional_point_mass_one R h2).
  have hMass:=@current_finite_mass_scale_bound R h2 0%N 0%N U hU (1/2) P 1 hPBound.
  have hHalfPositive:(0:R)<=1/2 by lra.
  rewrite (ger0_norm hHalfPositive) mulr1 in hMass.
  have hSmall:(M ((1/2:R)*:P)<1)%E.
    apply:(le_lt_trans hMass);rewrite lte_fin;lra.
  have hZero:=@integral_polyhedral_zero_mass_gap R h2 0%N U hU K
    ((1/2:R)*:P) hPoly hSmall.
  have[phi hPhi]:=@dirac_current_unit_test R h2 0%N U hU (0:X) Logic.I.
  pose E:=@current_point_evaluation R h2 0%N 0%N U hU phi.
  have h:=congr1 E hZero.
  rewrite linearZ linear0 in h.
  change ((1/2:R)*@current_value R h2 0%N U hU 0%N P phi=0) in h.
  rewrite hPhi mulr1 in h;have hPositive:(0:R)<1/2 by lra.
  by rewrite h ltxx in hPositive.
split;first exact:hNotRect.
split;first exact:hNotRect.
move=>hIF;apply:hNotRect.
exact:(@zero_ambient_integral_flat_rectifiable_iff R h2 U hU K ((1/2:R)*:P)).1 hIF.
Qed.
End IntegralPointEndpoints.
