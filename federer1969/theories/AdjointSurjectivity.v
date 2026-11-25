(** Federer (1969), 1.7.6, p. 34: the target-top positivity assertion uses
    surjectivity iff the adjoint is injective. The image is split
    orthogonally using the finite family of images of a source basis. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerProductLaws AdjointUP AdjointLaws
  LinearBasis Annihilator FiniteDualDimension Hom FiniteSpans FiniteFamilyOrthogonalSplit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [adjoint_injective_iff_surjective]: Federer
    1.7.6, p. 34, supporting equivalence for the epimorphism
    conclusion: f is onto iff its adjoint is one-to-one. Only
    the source of f needs a finite basis for this assertion. *)
Theorem adjoint_injective_iff_surjective (R : rcfType)
    (V U : lmodType R) (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (b : 'I_n -> V) (hb : is_basis b)
    (f : {linear V -> U}) (a : {linear U -> V}) (ha : is_adjoint B C f a) :
  injective a <-> forall y, exists x, f x = y.
Proof.
split.
- move=> hi y.
  have [s [w [hs [hw hy]]]] := finite_family_orthogonal_split hC (fun i => f (b i)) y.
  have hspan v : in_finite_span (fun i => f (b i)) (f v).
    exists (fun i => dual_basis hb i v).
    rewrite {1}(basis_vector_expansion hb v) linear_sum.
    apply: eq_bigr => i _; exact: linearZ.
  have haw : a w = 0.
    apply: (@inner_right_separates R V B hB) => v.
    rewrite ha (inner_symmetric hC); exact: hw (f v) (hspan v).
  have hw0 : w = 0 by apply: hi; rewrite linear0.
  have [c hc] := hs.
  exists (\sum_i c i *: b i).
  rewrite hy hw0 addr0 hc linear_sum.
  apply: eq_bigr => i _; exact: linearZ.
- move=> hs y z hyz; apply: (@inner_vectors_ext R U C hC) => u.
  have [x <-] := hs u; by rewrite -!ha hyz.
Qed.
