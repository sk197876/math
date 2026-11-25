(** Federer (1969), 3.2.1, p. 241: ordinary and approximate
    k-dimensional Jacobians have exactly the corresponding differential
    domains. Graph specifications do not assign values elsewhere. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  PartialFunctionUP NormDifferentialUP ApproximateDifferentialUP EuclideanLinearJacobian.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section JacobianLaws.
Variable R:realType.
Variables m n k:nat.
Local Notation X:=(R_n R m).
Local Notation Y:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R m)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R n)).
Variables (A:X->Prop) (f:X->Y).

(** Source for [has_euclidean_jacobian]: J_k f(a) in the first
    display of Federer 3.2.1, p. 241. The value is the kth
    exterior operator norm of an actual differential at a. *)
Definition has_euclidean_jacobian a j :=
  exists L:Hom X Y,has_norm_differential NX NY A f a L /\ euclidean_linear_jacobian k L=j.

(** Source for [has_approximate_jacobian]: ap J_k f(a) in the
    second display of Federer 3.2.1, p. 241. It uses the actual
    approximate differential and its original domain conventions. *)
Definition has_approximate_jacobian a j :=
  exists L:Hom X Y,has_approximate_differential NY A f a L /\ euclidean_linear_jacobian k L=j.

(** Source for [is_euclidean_jacobian_graph]: the exact partial
    Jacobian of Federer 3.2.1, p. 241. Existence of this graph
    is a theorem; the specification asserts no project axiom. *)
Definition is_euclidean_jacobian_graph (J:partial_function X R) :=
  forall a j,partial_function_graph J a j <-> has_euclidean_jacobian a j.

(** Source for [is_approximate_jacobian_graph]: the exact partial
    approximate Jacobian in Federer 3.2.1, p. 241, with no
    default value at points where approximate differentiability fails. *)
Definition is_approximate_jacobian_graph (J:partial_function X R) :=
  forall a j,partial_function_graph J a j <-> has_approximate_jacobian a j.
End JacobianLaws.
