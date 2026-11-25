(** Federer (1969), 4.1.12, p. 367: the original
    compact flat test seminorm is bounded by every nonnegative
    common pointwise bound for the form and its exterior
    derivative on K. This direct consequence of the sealed
    maximum formula supports the unchanged-index source
    replacement in 4.1.14, pp. 370–371. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentCoefficientNorms SmoothCompactSet SmoothTestSpaces
  CurrentTestExteriorDerivative CurrentCompactZerothBounds CurrentFlatFormSeminormLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [current_flat_test_least_pointwise_bound]: a
    nonnegative common original comass bound on K bounds F_K,
    Federer 4.1.12, p. 367. Empty K and degree zero
    require no extra hypothesis. *)
Theorem current_flat_test_least_pointwise_bound
    (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (K:smooth_compact_set
      (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (phi:@current_test_space R h2 n U hU m) b:
  0<=b->
  (forall x,smooth_compact_carrier K x->
    @current_form_comass R h2 n m (@current_test_value R h2 n U hU m phi x)<=b /\
    @current_form_comass R h2 n m.+1 (@current_test_value R h2 n U hU m.+1
      (@current_test_exterior_derivative R h2 n m U hU phi) x)<=b)->
  @current_flat_test_seminorm R h2 n m U hU K phi<=b.
Proof.
move=>hb hPoint.
rewrite /current_flat_test_seminorm current_flat_form_seminorm_formula
  -(@current_test_exterior_derivative_inclusion R h2 n m U hU phi) ge_max.
apply/andP;split.
- apply:(@current_compact_zeroth_least_bound R h2 n m U hU K
    (smooth_test_inclusion (@current_smooth_space_laws R h2 n U hU m) phi) b hb)
    =>x hx;exact:(hPoint x hx).1.
- apply:(@current_compact_zeroth_least_bound R h2 n m.+1 U hU K
    (smooth_test_inclusion (@current_smooth_space_laws R h2 n U hU m.+1)
      (@current_test_exterior_derivative R h2 n m U hU phi)) b hb)
    =>x hx;exact:(hPoint x hx).2.
Qed.
