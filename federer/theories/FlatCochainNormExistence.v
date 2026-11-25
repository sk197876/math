(** Federer (1969), 4.1.19, p. 377: the
    least common flat-cochain bound exists. The
    previous nonnegative-multiple infimum law applies
    directly to every original compact-index inequality,
    including zero flat values. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces SmoothCompactSet CurrentFlatNorm CurrentFlatDualSeminormBasic
  FlatCurrentUnionSpace FlatCochainUP ScalarConvexSectionLength.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [flat_cochain_norm_exists]: the norm
    is the least nonnegative common bound in
    Federer 4.1.19, p. 377. The original
    compact-index family stays inside its universal
    quantifier; no single compact support is imposed
    on the cochain. Zero spaces are included. *)
Theorem flat_cochain_norm_exists (R : realType) (h2 : (1+1:R)!=0)
    n m (U : set (R_n R n))
    (hU : forall x, U x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (alpha : Hom (@flat_current_union_space R h2 n m U hU) R^o) :
  @is_flat_cochain R h2 n m U hU alpha ->
  exists a : R, @is_flat_cochain_norm R h2 n m U hU alpha a.
Proof.
move=> [c hC].
pose B := [set b : R | @is_flat_cochain_bound R h2 n m U hU alpha b].
have hNonempty : B !=set0 by exists c.
have hLower : lbound B 0 by move=> b hb; exact: hb.1.
have hHasLower : has_lbound B by exists 0.
exists (inf B); split.
- split; first exact: (lb_le_inf hNonempty hLower).
  move=> K T hFlat.
  pose t := fine (@current_flat_norm R h2 n m U hU K
    (@flat_current_union_inclusion R h2 n m U hU T)).
  have hNonnegative : 0 <= t.
    apply: fine_ge0.
    exact: (@current_flat_dual_nonnegative R h2 n m U hU K
      (@current_value R h2 n U hU m
        (@flat_current_union_inclusion R h2 n m U hU T))).
  have hBound : forall b, B b -> `|alpha T| <= t*b.
    move=> b hb; rewrite mulrC; exact: (hb.2 K T hFlat).
  have hInf := @nonnegative_multiple_infimum_bound R B t `|alpha T|
    hNonempty hNonnegative hBound.
  by rewrite mulrC in hInf.
- move=> b hb; exact: (ge_inf hHasLower hb).
Qed.
