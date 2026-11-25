(** Federer (1969), 4.1.19, p. 377: transfer
    the exact earlier flat boundary estimate to
    its finite real values, as needed for
    the cochain common bound. No normality or
    mass hypothesis is introduced. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces SmoothCompactSet CurrentBoundary CurrentFlatNorm
  CurrentFlatBoundary CurrentFlatDualSeminormBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [current_finite_flat_boundary_fine_bound]:
    the real-valued instance of F_K(boundary T)<=F_K(T)
    from 4.1.12, p. 367, used for
    F(d alpha)<=F(alpha) in Federer 4.1.19,
    p. 377. Only the original finite
    flat value is assumed. *)
Theorem current_finite_flat_boundary_fine_bound
    (R : realType) (h2 : (1+1:R)!=0) n m
    (U : set (R_n R n))
    (hU : forall x, U x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (K : smooth_compact_set
      (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (T : @current_space R h2 n U hU m.+1) :
  (@current_flat_norm R h2 n m.+1 U hU K T < +oo)%E ->
  fine (@current_flat_norm R h2 n m U hU K
    (@current_boundary R h2 n m U hU T)) <=
  fine (@current_flat_norm R h2 n m.+1 U hU K T).
Proof.
move=> hFinite.
have hBoundary := @current_flat_boundary_bound R h2 n m U hU K T.
have hFiniteBoundary := le_lt_trans hBoundary hFinite.
have [a [hA hValueA]] := @current_flat_dual_finite_value R h2 n m U hU K
  (@current_value R h2 n U hU m (@current_boundary R h2 n m U hU T))
  hFiniteBoundary.
have [b [hB hValueB]] := @current_flat_dual_finite_value R h2 n m.+1 U hU K
  (@current_value R h2 n U hU m.+1 T) hFinite.
change (@current_flat_norm R h2 n m U hU K
  (@current_boundary R h2 n m U hU T) = a%:E) in hValueA.
change (@current_flat_norm R h2 n m.+1 U hU K T = b%:E) in hValueB.
rewrite hValueA hValueB lee_fin in hBoundary.
by rewrite hValueA hValueB.
Qed.
