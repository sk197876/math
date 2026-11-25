(** Federer (1969), 1.7.7, p. 34: identify the image of the chosen
    orthogonal injection with the associated subspace of a nonzero simple
    vector. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import LinearBasis FiniteDualDimension Hom Annihilator FiniteSpans.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [basis_image_finite_span]: Federer 1.7.7,
    p. 34, supporting range calculation: the image of a linear
    map is the span of the images of a finite basis. *)
Theorem basis_image_finite_span (R : fieldType) (V U : lmodType R)
    m (b : 'I_m -> V) (hb : is_basis b) (e : 'I_m -> U)
    (f : {linear V -> U}) (hf : forall i, f (b i) = e i) y :
  (exists x, f x = y) <-> in_finite_span e y.
Proof.
split.
- move=> [x <-]; exists (fun i => dual_basis hb i x).
  rewrite {1}(basis_vector_expansion hb x) linear_sum.
  apply: eq_bigr => i _; by rewrite linearZ hf.
- move=> [c ->]; exists (\sum_i c i *: b i).
  rewrite linear_sum; apply: eq_bigr => i _; by rewrite linearZ hf.
Qed.
