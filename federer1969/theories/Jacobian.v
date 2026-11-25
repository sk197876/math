(** Public ordinary and approximate Jacobians, Federer (1969),
    3.2.1, p. 241. All downstream facts use the exact opaque
    graph laws, not the private witness or a default differential. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  PartialFunctionUP NormDifferentialUP ApproximateDifferentialUP EuclideanLinearJacobian JacobianUP JacobianSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_jacobian]: J_k f as defined in Federer
    3.2.1, p. 241. It is a partial numerical function on the
    ordinary differentiability locus, even when k is zero. *)
Definition euclidean_jacobian (R:realType) m n k
    (A:R_n R m->Prop) (f:R_n R m->R_n R n) := @Jacobians.value R m n k A f.

(** Source for [approximate_jacobian]: ap J_k f in Federer
    3.2.1, p. 241, on exactly its approximate differentiability locus. *)
Definition approximate_jacobian (R:realType) m n k
    (A:R_n R m->Prop) (f:R_n R m->R_n R n) := @Jacobians.approximate_value R m n k A f.

(** Source for [euclidean_jacobian_graph]: the first displayed
    definition of Federer 3.2.1, p. 241, as an exact graph law. *)
Theorem euclidean_jacobian_graph (R:realType) m n k
    (A:R_n R m->Prop) (f:R_n R m->R_n R n) a j :
  partial_function_graph (euclidean_jacobian k A f) a j <-> has_euclidean_jacobian k A f a j.
Proof. exact (@Jacobians.laws R m n k A f a j). Qed.

(** Source for [approximate_jacobian_graph]: the second displayed
    definition of Federer 3.2.1, p. 241, as an exact graph law. *)
Theorem approximate_jacobian_graph (R:realType) m n k
    (A:R_n R m->Prop) (f:R_n R m->R_n R n) a j :
  partial_function_graph (approximate_jacobian k A f) a j <-> has_approximate_jacobian k A f a j.
Proof. exact (@Jacobians.approximate_laws R m n k A f a j). Qed.

(** Source for [euclidean_jacobian_domain]: the phrase whenever
    f is differentiable in Federer 3.2.1, p. 241. Undefined
    differential points remain outside the Jacobian domain for every k. *)
Theorem euclidean_jacobian_domain (R:realType) m n k
    (A:R_n R m->Prop) (f:R_n R m->R_n R n) a :
  partial_function_domain (euclidean_jacobian k A f) a <->
  norm_differentiable_at (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) A f a.
Proof.
split.
- move=>[j hj]; have [L [hL _]]:=(euclidean_jacobian_graph k A f a j).1 hj; by exists L.
- move=>[L hL]; exists (euclidean_linear_jacobian k L).
  apply:(euclidean_jacobian_graph k A f a _).2; by exists L.
Qed.

(** Source for [approximate_jacobian_domain]: whenever f is
    approximately differentiable in Federer 3.2.1, p. 241.
    The exact domain convention of 3.1.2 is preserved. *)
Theorem approximate_jacobian_domain (R:realType) m n k
    (A:R_n R m->Prop) (f:R_n R m->R_n R n) a :
  partial_function_domain (approximate_jacobian k A f) a <->
  approximately_differentiable_at (inner_norm (@euclidean_inner_productP R n)) A f a.
Proof.
split.
- move=>[j hj]; have [L [hL _]]:=(approximate_jacobian_graph k A f a j).1 hj; by exists L.
- move=>[L hL]; exists (euclidean_linear_jacobian k L).
  apply:(approximate_jacobian_graph k A f a _).2; by exists L.
Qed.

(** Source for [euclidean_jacobian_nonnegative]: the norm in
    the first definition of Federer 3.2.1, p. 241, is nonnegative.
    Supporting property at every point of the actual partial graph. *)
Lemma euclidean_jacobian_nonnegative (R:realType) m n k
    (A:R_n R m->Prop) (f:R_n R m->R_n R n) a j :
  partial_function_graph (euclidean_jacobian k A f) a j -> 0<=j.
Proof.
move=>/(euclidean_jacobian_graph k A f a j) [L [_ <-]].
exact:euclidean_linear_jacobian_nonnegative.
Qed.

(** Source for [approximate_jacobian_nonnegative]: the norm in
    the second definition of Federer 3.2.1, p. 241, is nonnegative.
    No value is claimed away from the approximate differentiability locus. *)
Lemma approximate_jacobian_nonnegative (R:realType) m n k
    (A:R_n R m->Prop) (f:R_n R m->R_n R n) a j :
  partial_function_graph (approximate_jacobian k A f) a j -> 0<=j.
Proof.
move=>/(approximate_jacobian_graph k A f a j) [L [_ <-]].
exact:euclidean_linear_jacobian_nonnegative.
Qed.

(** Source for [jacobians_agree_on_common_differential]: the two
    definitions in Federer 3.2.1, p. 241, give the same value
    when their actual differential is the same linear map.
    This supports the later approximate area and coarea extensions. *)
Lemma jacobians_agree_on_common_differential (R:realType) m n k
    (A:R_n R m->Prop) (f:R_n R m->R_n R n) a (L:Hom (R_n R m) (R_n R n)) :
  has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) A f a L ->
  has_approximate_differential (inner_norm (@euclidean_inner_productP R n)) A f a L ->
  partial_function_graph (euclidean_jacobian k A f) a (euclidean_linear_jacobian k L) /\
  partial_function_graph (approximate_jacobian k A f) a (euclidean_linear_jacobian k L).
Proof.
move=>hd ha; split.
- apply:(euclidean_jacobian_graph k A f a _).2; by exists L.
- apply:(approximate_jacobian_graph k A f a _).2; by exists L.
Qed.
