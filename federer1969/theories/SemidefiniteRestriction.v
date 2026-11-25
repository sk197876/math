(** Federer (1969), 1.7.3, p. 29: supporting algebra inside a constrained
    subspace in the principal-axis proof. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP Bilinear ModuleQuotient SubspaceCarrier
  PositiveSemidefinite InnerProductRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Restriction.
Variable R : realFieldType.
Variable V : lmodType R.
Variable S : V -> V -> R.
Hypothesis hS : @bilinear R V V R^o S.
Variable W : subspace V.

(** Source for [restricted_bilinearP]: Federer 1.7.3, p. 29,
    supporting preservation of bilinearity under restriction to a
    vector subspace; no positivity or symmetry is needed. *)
Lemma restricted_bilinearP : @bilinear R (subspace_space W)
  (subspace_space W) R^o (@restricted_inner_product R V S W).
Proof.
split=> y a x z; rewrite /restricted_inner_product linearP.
- by rewrite (bilDl hS) (bilZl hS).
- by rewrite (bilDr hS) (bilZr hS).
Qed.

(** Source for [semidefinite_zero_diagonal_in_subspace]: Federer
    1.7.3, p. 29, supporting stationary-point implication within a
    constraint subspace: a zero diagonal value of a symmetric form
    nonnegative on that subspace annihilates every vector in it. *)
Theorem semidefinite_zero_diagonal_in_subspace :
  (forall x y, S x y = S y x) -> (forall x, W x -> 0 <= S x x) ->
  forall x y, W x -> W y -> S x x = 0 -> S x y = 0.
Proof.
move=> hs hp x y hx hy hz.
have hP : is_positive_semidefinite (@restricted_inner_product R V S W).
  constructor; first exact: restricted_bilinearP.
  - by move=> u v; rewrite /restricted_inner_product hs.
  - move=> u; apply: hp; exact: subspace_valP.
exact (@semidefinite_zero_diagonal R (subspace_space W) _ hP
  (subspace_lift hx) (subspace_lift hy) hz).
Qed.
End Restriction.
