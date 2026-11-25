(** Federer (1969), 4.1.24, pp. 380–381:
    in ambient R^0 the next-degree filling current
    is zero. The three original integer zero-current
    classes therefore agree with the integral
    polyhedral zero-current group. This retains the
    integer restriction. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals.
From Federer Require Import Bilinear Hom RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentSpaces CurrentBoundary CurrentAboveDimension
  PolyhedralCurrentAlgebra RectifiableCurrentApproximationUP RectifiableZeroPolyhedral
  IntegralCurrentClassesUP IntegralCurrentInclusions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [zero_ambient_integral_flat_rectifiable_iff]:
    in R^0 the original integral-flat zero-current
    definition has no nonzero filling, 4.1.24,
    p. 381, by the earlier above-dimension theorem.
    This holds for every original open and compact. *)
Theorem zero_ambient_integral_flat_rectifiable_iff
    (R:realType) (h2:(1+1:R)!=0)
    (U:set (R_n R 0%N))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R 0%N)) U x)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R 0%N)) U)
    (T:@current_space R h2 0%N U hU 0%N):
  @is_integral_flat_current_supported_in R h2 0%N U hU 0%N K T<->
    @is_rectifiable_current_supported_in R h2 0%N 0%N U hU K T.
Proof.
split;last exact:rectifiable_current_is_integral_flat_supported.
move=>[A [S [hA [hS hEqual]]]].
have hSZero:=@current_above_dimension R h2 0%N 1%N (ltn0Sn 0%N) U hU S.
rewrite hSZero (lin0 (hom_linear (@current_boundary R h2 0%N 0%N U hU))) addr0 in hEqual.
by rewrite hEqual.
Qed.

(** Source for [zero_ambient_integral_flat_polyhedral_iff]:
    actual integral-flat zero-currents on R^0 have
    integral coefficients, 4.1.24, pp. 380–381.
    The real polyhedral span is not substituted. *)
Theorem zero_ambient_integral_flat_polyhedral_iff
    (R:realType) (h2:(1+1:R)!=0)
    (U:set (R_n R 0%N))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R 0%N)) U x)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R 0%N)) U)
    (T:@current_space R h2 0%N U hU 0%N):
  @is_integral_flat_current_supported_in R h2 0%N U hU 0%N K T<->
    @integral_polyhedral_current_class R h2 0%N 0%N U hU K T.
Proof.
split.
- move=>hT;apply:(@rectifiable_zero_polyhedral_iff R h2 0%N U hU K T).1.
  exact:(@zero_ambient_integral_flat_rectifiable_iff R h2 U hU K T).1 hT.
- move=>hT;apply:(@zero_ambient_integral_flat_rectifiable_iff R h2 U hU K T).2.
  exact:(@rectifiable_zero_polyhedral_iff R h2 0%N U hU K T).2 hT.
Qed.
