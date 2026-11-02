(** Federer (1969), 1.7.5, p. 32: coordinate expression and positivity of
    the induced inner product. Supporting bilinear algebra for an
    orthonormal family and basis. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP Bilinear BilinearFiniteCoordinates
  InnerProductUP OrthonormalFamilies LinearBasis FiniteDualDimension
  Annihilator Hom FiniteBasisCriterion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Coordinates.
Variable R : realFieldType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : @bilinear R V V R^o B.
Variable I : finType.
Variable e : I -> V.
Hypothesis he : orthonormal_family B e.

(** Source for [orthonormal_bilinear_expansion]: Federer
    1.7.5, p. 32, the inner product of two expansions in an
    orthonormal family is the sum of products of their coordinates.
    Positivity of B is not assumed in this supporting lemma. *)
Lemma orthonormal_bilinear_expansion (c d : I -> R) :
  B (\sum_i c i *: e i) (\sum_i d i *: e i) = \sum_i c i * d i.
Proof.
rewrite (bilinear_finite_expansion hB).
apply: eq_bigr => i _; rewrite (bigD1 i) //= he eqxx mulr1.
have hz : (\sum_(j | j != i) (c i*d j)*B (e i) (e j)) = 0.
  apply: big1 => j hj; by rewrite he eq_sym (negbTE hj) mulr0.
by rewrite hz addr0.
Qed.

Hypothesis hb : is_basis e.

(** Source for [orthonormal_basis_vector_expansion]: Federer
    1.7.5, p. 32, supporting expansion in a basis with any
    finite index set, in particular Lambda(n,m). Orthogonality
    is not needed for this expansion itself. *)
Lemma orthonormal_basis_vector_expansion x :
  x = \sum_i dual_basis hb i x *: e i.
Proof.
rewrite -{1}(basis_coordinatesK hb x) basis_synthesis_finiteE.
apply: eq_bigr => i _; by [].
Qed.

(** Source for [orthonormal_basis_bilinear_coordinates]:
    Federer 1.7.5, p. 32, the coordinate formula for arbitrary
    vectors when the orthonormal family is a basis. *)
Lemma orthonormal_basis_bilinear_coordinates x y :
  B x y = \sum_i dual_basis hb i x * dual_basis hb i y.
Proof.
rewrite {1}(orthonormal_basis_vector_expansion x) {1}(orthonormal_basis_vector_expansion y).
exact: orthonormal_bilinear_expansion.
Qed.

(** Source for [orthonormal_basis_inner_product]: Federer
    1.7.5, p. 32, sums of coordinate squares prove positive
    definiteness. This supporting criterion proves all inner-product
    laws from a bilinear form and an orthonormal basis. *)
Theorem orthonormal_basis_inner_product : is_inner_product B.
Proof.
constructor; first exact hB.
- move=> x y; rewrite !orthonormal_basis_bilinear_coordinates.
  apply: eq_bigr => i _; exact: mulrC.
- move=> x; rewrite orthonormal_basis_bilinear_coordinates.
  have hnon : 0 <= \sum_i dual_basis hb i x * dual_basis hb i x.
    apply: sumr_ge0 => i _; by rewrite -expr2 sqr_ge0.
  have hzero : ((\sum_i dual_basis hb i x * dual_basis hb i x) == 0) = (x == 0).
    apply/eqP/eqP.
    + move=> hz; rewrite (orthonormal_basis_vector_expansion x).
      apply: big1 => i _.
      have hs : (dual_basis hb i x)^+2 = 0.
        have hp j : 0 <= dual_basis hb j x * dual_basis hb j x by rewrite -expr2 sqr_ge0.
        have h := psumr_eq0P (fun j _ => hp j) hz (i:=i) isT.
        by rewrite expr2.
      have hc : dual_basis hb i x = 0 by apply/eqP; rewrite -sqrf_eq0 hs eqxx.
      by rewrite hc scale0r.
    + move=> ->; apply: big1 => i _; by rewrite linear0 mul0r.
  by rewrite lt_def hnon andbT hzero.

Qed.
End Coordinates.
