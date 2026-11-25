(** Federer (1969), 4.1.24, pp. 380–382:
    the original three fixed-index integer classes
    retain empty compact indices and degrees above
    the ambient dimension. Use original current support
    and dimension laws, rather than introducing
    inhabitance assumptions. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentSpaces CurrentSupportExtensionality CurrentAboveDimension
  FlatCurrentsUP FlatCurrentFinite RectifiableCurrentApproximationUP
  RectifiableCurrentBasic RectifiableCurrentWitnesses IntegralCurrentClassesUP
  IntegralCurrentAlgebra IntegralCurrentInclusions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section IntegralCurrentBoundaryCases.
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
Local Notation Empty:=(@smooth_compact_empty R X NX hNX U).

(** Source for [rectifiable_current_empty_index_iff_zero]:
    the original mass approximation property at empty K
    gives exactly zero, 4.1.24, p. 380. *)
Theorem rectifiable_current_empty_index_iff_zero (T:C):
  @is_rectifiable_current_supported_in R h2 n m U hU Empty T<->T=0.
Proof.
split;last by move=>->;exact:rectifiable_current_zero.
move=>hT;apply:(@current_empty_support_iff_zero R h2 n m U hU T).1.
exact:(@rectifiable_current_support R h2 n m U hU Empty T hT).
Qed.

(** Source for [integral_current_empty_index_iff_zero]:
    the original fixed empty-index integral class
    is the zero group, 4.1.24, p. 381. *)
Theorem integral_current_empty_index_iff_zero (T:C):
  @is_integral_current_supported_in R h2 n U hU m Empty T<->T=0.
Proof.
split;last by move=>->;exact:integral_current_zero_supported.
move=>hT;apply:(rectifiable_current_empty_index_iff_zero T).1.
exact:integral_current_is_rectifiable_supported hT.
Qed.

(** Source for [integral_flat_current_empty_index_iff_zero]:
    the literal two-term integral-flat definition at
    empty K gives exactly zero, 4.1.24, p. 381.
    A boundary does not create support outside K. *)
Theorem integral_flat_current_empty_index_iff_zero (T:C):
  @is_integral_flat_current_supported_in R h2 n U hU m Empty T<->T=0.
Proof.
split;last by move=>->;exact:integral_flat_current_zero_supported.
move=>hT;apply:(@current_empty_support_iff_zero R h2 n m U hU T).1.
exact:(@flat_current_supported_support R h2 n m U hU Empty T
  (@integral_flat_current_is_flat_supported R h2 n U hU Empty m T hT)).
Qed.

(** Source for [integer_current_classes_above_dimension]:
    all three original integer classes contain every
    actual current in degree above n, since that
    current space is zero, 4.1.24, pp. 380–381,
    reusing 4.1.10, p. 364. No source point
    is selected, even when U or K is empty. *)
Theorem integer_current_classes_above_dimension
    (K:smooth_compact_set hNX U) (T:C):
  (n<m)%N->
  @is_rectifiable_current_supported_in R h2 n m U hU K T /\
  @is_integral_current_supported_in R h2 n U hU m K T /\
  @is_integral_flat_current_supported_in R h2 n U hU m K T.
Proof.
move=>hNM;have->:=@current_above_dimension R h2 n m hNM U hU T.
split;first exact:rectifiable_current_zero.
split;[exact:integral_current_zero_supported|exact:integral_flat_current_zero_supported].
Qed.
End IntegralCurrentBoundaryCases.
