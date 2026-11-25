(** Federer (1969), 1.7.2, p. 28: the polarity in finite dimension is an
    isomorphism onto the one-covectors. An orthonormal basis supplies a
    witness for surjectivity. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerPolarity OrthonormalFamilies
  OrthonormalisationUP GramSchmidt OneFormLinear Hom LinearBasis
  FiniteDualDimension Annihilator AlternatingCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section PolaritySurjection.
Variable R : rcfType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Local Notation F := (A_m V R^o 1).
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Hypothesis ho : orthonormal_family B e.

(** Source for [inner_polarity_orthonormal_dual]: Federer 1.7.2,
    pp. 28-29, final sentence: the polarity sends an orthonormal basis
    to its dual basis, expressed through the identification of one-forms
    with linear functionals. *)
Theorem inner_polarity_orthonormal_dual i :
  one_hom (inner_polarity hB (e i)) = dual_basis he i.
Proof.
apply: hom_ext => x.
apply: (basis_linear_ext he
  (hom_as_linear (one_hom (inner_polarity hB (e i))))
  (hom_as_linear (dual_basis he i))) x => j.
by rewrite !hom_as_linearE one_homE inner_polarityE dual_basisE ho.
Qed.

(** Source for [inner_polarity_coordinate_preimage]: Federer 1.7.2,
    p. 28, supporting witness: summing alpha(e_i)e_i gives a vector
    whose polarity is alpha when the basis is orthonormal. *)
Lemma inner_polarity_coordinate_preimage (a : F) :
  inner_polarity hB (\sum_i one_hom a (e i) *: e i) = a.
Proof.
apply: one_hom_injective.
rewrite (@linear_sum R V F _ (inner_polarity hB)).
under eq_bigr do rewrite linearZ.
rewrite linear_sum.
under eq_bigr do rewrite linearZ.
change ((\sum_i one_hom a (e i) *: one_hom (inner_polarity hB (e i))) = one_hom a).
under eq_bigr do rewrite inner_polarity_orthonormal_dual.
exact: esym (dual_basis_expansion he (one_hom a)).
Qed.
End PolaritySurjection.

(** Source for [inner_polarity_surjective]: Federer 1.7.2, p. 28,
    the polarity maps onto all one-forms in finite dimension. The basis
    provided in the hypothesis need not be orthonormal. *)
Theorem inner_polarity_surjective (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (u : 'I_n -> V) (hu : is_basis u) :
    forall a : A_m V R^o 1, exists x, inner_polarity hB x = a.
Proof.
move=> a; have [e [he ho]] := orthonormal_basis_exists hB hu.
exists (\sum_i one_hom a (e i) *: e i).
exact (@inner_polarity_coordinate_preimage R V B hB n e he
  (orthonormalisation_orthonormal ho) a).
Qed.
