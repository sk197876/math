(** Federer (1969), 4.1.14, p. 371: split the
    flat image error into its three printed terms.
    The original finite-flat triangle inequality is
    used only after all three errors have finite
    proved real upper bounds. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces SmoothCompactSet CurrentFlatNorm CurrentFlatFiniteArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [current_flat_three_error_bound]: the exact
    three-term comparison of Federer 4.1.14, p. 371.
    Finiteness follows from the supplied original bounds,
    without normality or a measure representation. *)
Theorem current_flat_three_error_bound (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (Q P A B:@current_space R h2 n U hU m) (a b c:R):
  (@current_flat_norm R h2 n m U hU K (Q-P)<=a%:E)%E ->
  (@current_flat_norm R h2 n m U hU K (P-A)<=b%:E)%E ->
  (@current_flat_norm R h2 n m U hU K (A-B)<=c%:E)%E ->
  (@current_flat_norm R h2 n m U hU K (Q-B)<=(a+b+c)%:E)%E.
Proof.
move=>hFirst hSecond hThird.
pose F:=@current_flat_norm R h2 n m U hU K.
have hFinite1:(F ((Q-P)%R) < +oo)%E:=le_lt_trans hFirst (ltry a).
have hFinite2:(F ((P-A)%R) < +oo)%E:=le_lt_trans hSecond (ltry b).
have hFinite3:(F ((A-B)%R) < +oo)%E:=le_lt_trans hThird (ltry c).
have hPair:=@current_flat_finite_triangle R h2 n m U hU K
  (Q-P) (P-A) hFinite1 hFinite2.
have hPairCap:=le_trans hPair (leeD hFirst hSecond).
rewrite addrA subrK -EFinD in hPairCap.
have hPairFinite:(F ((Q-A)%R) < +oo)%E:=le_lt_trans hPairCap (ltry (a+b)).
have hTotal:=@current_flat_finite_triangle R h2 n m U hU K
  (Q-A) (A-B) hPairFinite hFinite3.
have hBound:=le_trans hTotal (leeD hPairCap hThird).
by rewrite addrA subrK -EFinD in hBound.
Qed.
