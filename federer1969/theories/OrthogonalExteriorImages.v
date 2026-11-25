(** Federer (1969), 1.7.6, p. 34: products of distinct selections from a
    mutually orthogonal family are orthogonal, and squared norms of their
    linear combinations are diagonal sums. Zero members of the family are
    allowed, as required for singular maps. *)
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From Federer Require Import InnerProductUP InnerExterior InnerExteriorProducts
  InnerExteriorTriangular FiniteExteriorPowers ExteriorIndices LambdaPermutation
  SimpleAdaptedBasis BilinearFiniteCoordinates TensorUP Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [orthogonal_exterior_index_family]: Federer
    1.7.6, p. 34, distinct increasing products of mutually
    orthogonal vectors have zero inner product. *)
Theorem orthogonal_exterior_index_family (R : realFieldType)
    (h2 : (1+1 : R) != 0) (U : lmodType R)
    (C : U -> U -> R) (hC : is_inner_product C)
    n (e : 'I_n -> U) (ho : forall i j, i != j -> C (e i) (e j) = 0)
    m (lambda mu : Lambda n m) : lambda != mu ->
  exterior_inner_form h2 hC (e_lambda e (val lambda)) (e_lambda e (val mu)) = 0.
Proof.
move=> hl; rewrite (indexed_productE e (val lambda)) (indexed_productE e (val mu)) exterior_inner_product_permutations.
apply: big1 => sigma _.
have [hs|hs] := boolP [forall i : 'I_m, tnth (val mu) i == tnth (val lambda) (sigma i)].
- have hh i := eqP (forallP hs i).
  have [hm _] := Lambda_permutation_identity hh.
  by rewrite hm eqxx in hl.
- move/forallPn: hs => [i hi].
  have hz : foldr ( *%R) 1
      [seq C (e (tnth (val lambda) (sigma j))) (e (tnth (val mu) j)) | j <- enum 'I_m] = 0.
    apply: scalar_fold_product_zero; apply/mapP; exists i; first exact: mem_enum.
    rewrite ho // eq_sym; exact hi.
  by rewrite hz mulr0.
Qed.

(** Source for [orthogonal_bilinear_diagonal_sum]: Federer
    1.7.6, p. 34, supporting diagonal expansion of the squared
    length of a sum of mutually orthogonal vectors. *)
Lemma orthogonal_bilinear_diagonal_sum (R : fieldType) (U : lmodType R)
    (C : U -> U -> R) (hC : @bilinear R U U R^o C)
    (I : finType) (e : I -> U)
    (ho : forall i j, i != j -> C (e i) (e j) = 0) (c : I -> R) :
  C (\sum_i c i *: e i) (\sum_i c i *: e i) =
    \sum_i (c i)^+2 * C (e i) (e i).
Proof.
rewrite (bilinear_finite_expansion hC); apply: eq_bigr => i _.
rewrite (bigD1 i) //=.
have hz : (\sum_(j | j != i) (c i*c j)*C (e i) (e j)) = 0.
  apply: big1 => j hj; rewrite ho ?mulr0 // eq_sym; exact hj.
by rewrite hz addr0 expr2.
Qed.
