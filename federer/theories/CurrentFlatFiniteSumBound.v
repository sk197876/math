(** Federer (1969), 4.1.23, pp. 379–380:
    the original dual flat supremum respects
    finite sums of displayed finite error
    bounds. The argument acts on each
    original unit test, so it requires
    no extra closure-membership premise. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentPointEvaluation SmoothCompactSet CurrentFlatNorm
  CurrentFlatDualSeminormSealed CurrentFlatDualSeminormBasic ExtendedSupremumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [current_flat_norm_finite_sum_bound]:
    the finite triangle estimate used for
    the transverse cells and step fields
    in Federer 4.1.23, pp. 379–380.
    Each original error bound remains visible,
    including zero errors and empty sums. *)
Theorem current_flat_norm_finite_sum_bound (R : realType)
    (h2 : (1+1:R)!=0) n m (U : set (R_n R n))
    (hU : forall x, U x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (K : smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (I : finType) (T : I -> @current_space R h2 n U hU m) (a : I -> R) :
  (forall i, (@current_flat_norm R h2 n m U hU K (T i)<=(a i)%:E)%E) ->
  (@current_flat_norm R h2 n m U hU K (\sum_i T i)<=(\sum_i a i)%:E)%E.
Proof.
move=> hBound.
apply: (extended_supremum_least (@CurrentFlatDualSeminorm.laws R h2 n m U hU K
  (@current_value R h2 n U hU m (\sum_i T i))))=> z [phi [hPhi <-]].
rewrite current_value_finite_sum lee_fin; apply: ler_sum=> i _.
have hAction := @current_flat_dual_unit_upper R h2 n m U hU K
  (@current_value R h2 n U hU m (T i)) phi hPhi.
have h := le_trans hAction (hBound i).
by move: h; rewrite lee_fin.
Qed.
