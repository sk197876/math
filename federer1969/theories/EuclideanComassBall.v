(** Federer (1969), 1.8.3, p. 40: the displayed set in the actual covector
    space of R^n. This public interface specialises the intrinsic convexity
    theorem. Source context and the status of the extreme-point question:
    ComassUnitBall.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import AlternatingCoordinates FiniteCoordinates
  GrassmannAbbreviations EuclideanInnerProduct InnerConvex Comass ComassUP
  ComassUnitBall.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Euclidean.
Variable R : realType.
Hypothesis h2 : (1+1 : R) != 0.
Variable n m : nat.
Hypothesis hm : (0 < m)%N.

(** Source for [euclidean_comass_unit_ball]: Federer 1.8.3,
    p. 40, the displayed set Lambda^m(R^n) intersect {phi:||phi||<=1}.
    Positive degree follows the norm convention explained in 1.8.1. *)
Definition euclidean_comass_unit_ball : set (A_m (R_n R n) R^o m) :=
  @comass_unit_ball R (R_n R n) m
    (@comass R h2 (R_n R n) (@euclidean_inner_product R n)
      (@euclidean_inner_productP R n) n (@coordinate_basis R n)
      (@coordinate_basisP R n) m hm).

(** Source for [euclidean_comass_unit_ball_convex]: Federer 1.8.3,
    p. 40, the asserted convexity of the displayed sets, including
    n=0 and degrees exceeding n. *)
Theorem euclidean_comass_unit_ball_convex : is_inner_convex euclidean_comass_unit_ball.
Proof.
exact: (@comass_unit_ball_convex R h2 (R_n R n) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R n) m _
  (@comassP R h2 (R_n R n) (@euclidean_inner_product R n)
    (@euclidean_inner_productP R n) n (@coordinate_basis R n)
    (@coordinate_basisP R n) m hm)).
Qed.

(** Source for [euclidean_comass_unit_ball_nonempty]: Federer 1.8.3,
    p. 40, supporting nonemptiness of every displayed convex set. *)
Theorem euclidean_comass_unit_ball_nonempty : euclidean_comass_unit_ball 0.
Proof.
exact: (@comass_unit_ball_zero R h2 (R_n R n) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R n) m _
  (@comassP R h2 (R_n R n) (@euclidean_inner_product R n)
    (@euclidean_inner_productP R n) n (@coordinate_basis R n)
    (@coordinate_basisP R n) m hm)).
Qed.
End Euclidean.
