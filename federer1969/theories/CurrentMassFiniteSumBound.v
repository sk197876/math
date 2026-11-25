(** Federer (1969), 4.1.23, pp. 379–380:
    the original mass of the finite polyhedral
    sum is bounded by the sum of the
    separate displayed costs. Use the actual unit-test
    supremum, with no representation premise. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentPointEvaluation CurrentMassSealed CurrentMassBasic
  ExtendedSupremumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [current_mass_finite_sum_bound]:
    the finite mass-cost estimate used
    in the finite-cell and simple-vector
    reductions of Federer 4.1.23,
    p. 379, follows from the
    actual original current mass. Empty
    sums and zero costs are retained. *)
Theorem current_mass_finite_sum_bound (R : realType)
    (h2 : (1+1:R)!=0) n m (U : set (R_n R n))
    (hU : forall x, U x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (I : finType) (T : I -> @current_space R h2 n U hU m) (a : I -> R) :
  (forall i, (@CurrentMass.value R h2 n m U hU (T i)<=(a i)%:E)%E) ->
  (@CurrentMass.value R h2 n m U hU (\sum_i T i)<=(\sum_i a i)%:E)%E.
Proof.
move=> hBound.
apply: (extended_supremum_least (@CurrentMass.laws R h2 n m U hU (\sum_i T i)))=>
  z [phi [hPhi <-]].
rewrite current_value_finite_sum lee_fin; apply: ler_sum=> i _.
have hAction := @current_mass_unit_test_upper R h2 n m U hU (T i) phi hPhi.
have h := le_trans hAction (hBound i).
by move: h; rewrite lee_fin.
Qed.
