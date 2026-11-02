(** Federer (1969), 1.7.7, p. 34, first displayed formula: the norm of a
    simple m-vector in R^n is the supremum of its projected norms over
    O*(n,m). The formula includes m=0; for m>n the projection set can be
    empty, and the real supremum of the empty set is zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  CoordinateProjection OrthogonalEuclidean ExteriorGrading ExteriorMaps
  ExteriorNorm AssociatedSubspace ExteriorProjectionNorm
  SimpleProjectionAttainment NonnegativeSupremum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Supremum.
Variable R : realType.
Hypothesis h2 : (1+1 : R) != 0.
Variables n m : nat.

(** Source for [simple_vector_projection_values]: Federer 1.7.7,
    p. 34, the set in the first displayed supremum formula. *)
Definition simple_vector_projection_values (x : exterior_power (R_n R n) m) : set R :=
  [set r | exists p : {linear R_n R n -> R_n R m}, O_star p /\
    r = exterior_norm h2 (@euclidean_inner_productP R m) (exterior_power_map p m x)].

(** Source for [simple_vector_projection_supremum]: Federer 1.7.7,
    p. 34, first displayed equality, formalised for every realType.
    Simplicity is only used for attainment when x is nonzero. *)
Theorem simple_vector_projection_supremum (x : exterior_power (R_n R n) m)
    (sx : simple x) :
  exterior_norm h2 (@euclidean_inner_productP R n) x =
    sup (simple_vector_projection_values x).
Proof.
apply: nonnegative_supremum_attained_if_nonzero.
- exact: exterior_norm_nonnegative.
- move=> r [p [hp ->]]; split; first exact: exterior_norm_nonnegative.
  exact: (@exterior_projection_norm_bound R h2 (R_n R n) (R_n R m)
    (@euclidean_inner_product R n) (@euclidean_inner_product R m)
    (@euclidean_inner_productP R n) (@euclidean_inner_productP R m)
    p (proj1 (O_star_projection p) hp) m x).
- rewrite exterior_norm_eq0 => hx.
  have [f [p [hf [ha he]]]] := simple_projection_norm_attained h2
    (@euclidean_inner_productP R n) hx sx.
  exists p; split; last exact: esym he.
  by exists f.
Qed.
End Supremum.
