(** De Philippis, De Rosa and Ghiraldin (2018), Appendix A, (A.3), p. 1143;
    blueprint def:BF. Supporting identities for the inner product
    A • B = trace(A^* ∘ B) of Allard 2.2 on Hom(R^n, R^n), Federer 1.7.9,
    p. 35: A • B = B • A, A^* • B^* = A • B, A^* • B = A • B^*,
    (P ∘ X) • Y = X • (P^* ∘ Y) and (X ∘ Q) • Y = X • (Y ∘ Q^* ). They
    are used to compute B_F in DdgAnisotropicIntegrandConstruction.v. Nothing in
    this file is a new mathematical object. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions
  reals ring lra.
From Federer Require Import InnerProductUP InnerProductLaws InnerNorm InnerNormInequalities
  LinearBasis Bilinear TensorUP Hom HomInner HomInnerCoordinates AdjointUP AdjointLaws Adjoint
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates EuclideanRectangularAdjoint
  OrthonormalBilinearCoordinates OrthonormalParseval.
From Allard Require Import AllardHomInnerProduct AllardOrthogonalProjectors.
From DPDRG Require Import DdgLinearAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section HomInnerIdentities.
Variable R : realType.
Variable n : nat.
Local Notation Rn := (R_n R n).
Local Notation Bn := (@euclidean_inner_product R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation cb := (@coordinate_basis R n).
Local Notation hcb := (@coordinate_basis_orthonormal R n).
Local Notation HI := (hom_inner hBn hBn hbn).
Local Notation adjL L := (euclidean_rectangular_adjoint L).

(** Source for [ddg_parseval]: Federer 1.7.5, p. 32: for the orthonormal
    basis e_1, …, e_n of R^n, x • y = Σ_i (x • e_i) (y • e_i). Supporting
    lemma. *)
Lemma ddg_parseval (x y : Rn) : Bn x y = \sum_i Bn x (cb i) * Bn y (cb i).
Proof.
rewrite (orthonormal_basis_bilinear_coordinates (inner_bilinear hBn) hcb hbn).
apply: eq_bigr=> i _.
by rewrite !(orthonormal_basis_inner_coordinate hBn hcb hbn).
Qed.

(** Source for [ddg_hom_inner_sum]: Federer 1.7.9, p. 35:
    A • B = Σ_i A(e_i) • B(e_i) for the orthonormal basis e_1, …, e_n of
    R^n. Supporting lemma. *)
Lemma ddg_hom_inner_sum (f g : Hom Rn Rn) : HI f g = \sum_i Bn (f (cb i)) (g (cb i)).
Proof. exact: (hom_inner_orthonormal_sum hBn hBn hbn hbn hcb). Qed.

(** Source for [ddg_hom_inner_sym]: Federer 1.7.9, p. 35: A • B = B • A.
    Supporting lemma. *)
Lemma ddg_hom_inner_sym (f g : Hom Rn Rn) : HI f g = HI g f.
Proof. exact: (inner_symmetric (hom_inner_productP hBn hBn hbn)). Qed.

(** Source for [ddg_hom_inner_adjoint]: Federer 1.7.9, p. 35:
    A^* • B^* = A • B. Supporting lemma. *)
Lemma ddg_hom_inner_adjoint (f g : Hom Rn Rn) : HI (adjL f) (adjL g) = HI f g.
Proof.
rewrite !ddg_hom_inner_sum.
under eq_bigr do rewrite ddg_parseval.
under [RHS]eq_bigr do rewrite ddg_parseval.
rewrite exchange_big; apply: eq_bigr=> i _; apply: eq_bigr=> l _.
rewrite [Bn (adjL f _) _](inner_symmetric hBn) [Bn (adjL g _) _](inner_symmetric hBn).
by rewrite !euclidean_rectangular_adjoint_pairing.
Qed.

(** Source for [ddg_hom_inner_adjointl]: Federer 1.7.9, p. 35:
    A^* • B = A • B^*. Supporting lemma. *)
Lemma ddg_hom_inner_adjointl (f g : Hom Rn Rn) : HI (adjL f) g = HI f (adjL g).
Proof. by rewrite -ddg_hom_inner_adjoint ddg_adjointK. Qed.

(** Source for [ddg_hom_inner_compl]: Federer 1.7.4 and 1.7.9, p. 35:
    (P ∘ X) • Y = X • (P^* ∘ Y). Supporting lemma. *)
Lemma ddg_hom_inner_compl (P X Y : Hom Rn Rn) :
  HI (hom_comp P X) Y = HI X (hom_comp (adjL P) Y).
Proof.
rewrite !ddg_hom_inner_sum; apply: eq_bigr=> i _.
by rewrite !hom_compE euclidean_rectangular_adjoint_pairing.
Qed.

(** Source for [ddg_hom_inner_compr]: Federer 1.7.4 and 1.7.9, p. 35:
    (X ∘ Q) • Y = X • (Y ∘ Q^* ). Supporting lemma. *)
Lemma ddg_hom_inner_compr (X Q Y : Hom Rn Rn) :
  HI (hom_comp X Q) Y = HI X (hom_comp Y (adjL Q)).
Proof.
rewrite -ddg_hom_inner_adjoint ddg_adjoint_comp ddg_hom_inner_compl ddg_adjointK.
by rewrite -[RHS]ddg_hom_inner_adjoint ddg_adjoint_comp ddg_adjointK.
Qed.

End HomInnerIdentities.
