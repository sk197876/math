(** Federer (1969), 3.1.1, p. 211: sum the coordinate-segment
    bounds to control the remainder on a Euclidean ball. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm EuclideanCoordinateMetric
  EuclideanCoordinateStaircase NormPartialDerivative NormPartialDerivativeSegment.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_partial_derivative_ball_increment]: the last
    displayed estimate in Federer 3.1.1, p. 211. If every partial
    derivative in the ball has norm at most C, then the increment from
    its centre is at most n C times the Euclidean distance. The proof
    follows the displayed coordinate telescoping sum and 2.2.7. *)
Theorem norm_partial_derivative_ball_increment (R : realType) n
    (Y : lmodType R) (NY : Y -> R) (hNY : is_real_norm NY)
    (f : R_n R n -> Y) (a : R_n R n) (r C : R) :
  0 <= C ->
  (forall x, inner_norm (@euclidean_inner_productP R n) (x-a) < r ->
    forall i, exists v : Y, has_norm_partial_derivative NY f x i v /\ NY v <= C) ->
  forall h, inner_norm (@euclidean_inner_productP R n) h < r ->
    NY (f (a+h)-f a) <= n%:R*C*inner_norm (@euclidean_inner_productP R n) h.
Proof.
move=> hC hf h hh.
have hstep : forall i : 'I_n,
    NY (f (a+coordinate_prefix h i.+1)-f (a+coordinate_prefix h i)) <= C*`|h i|.
  move=> i; rewrite coordinate_prefix_step addrA.
  apply: (@norm_partial_derivative_segment_bound R n Y NY hNY f
    (a+coordinate_prefix h i) i (h i) C hC)=> t ht0 ht1.
  apply: hf.
  have heq : (a+coordinate_prefix h i+(t*h i) *: (@coordinate_basis R n i))-a =
    coordinate_prefix h i+(t*h i) *: (@coordinate_basis R n i).
    by rewrite -(addrA a (coordinate_prefix h i) ((t*h i) *: (@coordinate_basis R n i))) addrAC subrr add0r.
  rewrite heq; exact: le_lt_trans (coordinate_stair_segment_bound h i ht0 ht1) hh.
rewrite (coordinate_staircase_telescope f a h).
apply: le_trans (real_seminorm_sum hNY.1 _) _.
have hs : (\sum_(i<n) NY (f (a+coordinate_prefix h i.+1)-f (a+coordinate_prefix h i)))
    <= \sum_(i<n) C*inner_norm (@euclidean_inner_productP R n) h.
  apply: ler_sum=> i _; apply: le_trans (hstep i) _.
  apply: ler_wpM2l=> //; exact: euclidean_coordinate_norm_bound.
by rewrite sumr_const card_ord -mulr_natl mulrA in hs.
Qed.
