(** Federer (1969), 1.7.4, p. 30: existence of the adjoint, used for the
    final factorisation in 1.7.3 on the same page. This private coordinate
    witness is used only by its seal and the audit. Only the source needs
    finite dimension for existence of its adjoint. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP OrthonormalFamilies
  GramSchmidt OrthonormalisationUP LinearBasis TensorUP Bilinear AdjointUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Coordinates.
Variable R : rcfType.
Variables V U : lmodType R.
Variable B : V -> V -> R.
Variable C : U -> U -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hC : is_inner_product C.
Variable f : {linear V -> U}.
Variable n : nat.
Variable e : 'I_n -> V.

(** Source for [adjoint_coordinate_witness]: Federer 1.7.4,
    p. 30, supporting existence witness in an orthonormal source
    basis: the i-th coordinate of f*(y) is f(e_i).y. *)
Definition adjoint_coordinate_witness y := let _ := hC in \sum_i C (f (e i)) y *: e i.

(** Source for [adjoint_coordinate_linear]: Federer 1.7.4,
    p. 30, supporting linearity of the coordinate witness. *)
Lemma adjoint_coordinate_linear : linear adjoint_coordinate_witness.
Proof.
move=> a x y; rewrite /adjoint_coordinate_witness.
under eq_bigr do rewrite (bilDr (inner_bilinear hC))
  (bilZr (inner_bilinear hC)) scalerDl -scalerA.
by rewrite big_split scaler_sumr.
Qed.
HB.instance Definition _ := GRing.isLinear.Build R U V *:%R
  adjoint_coordinate_witness adjoint_coordinate_linear.

(** Source for [adjoint_coordinate_specification]: Federer
    1.7.4, p. 30, verification of the defining adjoint equation
    for the coordinate witness. *)
Lemma adjoint_coordinate_specification (he : is_basis e)
    (ho : orthonormal_family B e) :
  is_adjoint B C f adjoint_coordinate_witness.
Proof.
move=> x y.
have hh : inner_coordinate hB (adjoint_coordinate_witness y) x =
    (linear_comp (inner_coordinate hC y) f) x.
  apply: (basis_linear_ext he (inner_coordinate hB (adjoint_coordinate_witness y))
    (linear_comp (inner_coordinate hC y) f)) => i.
  rewrite inner_coordinateE (inner_symmetric hB).
  rewrite -(inner_coordinateE hB).
  change (inner_coordinate hB (e i) (adjoint_coordinate_witness y) =
    inner_coordinate hC y (f (e i))).
  rewrite [RHS]inner_coordinateE.
  exact (@orthonormal_coefficient R V B hB (Finite.clone 'I_n _) e ho
    (fun j => C (f (e j)) y) i).
change (inner_coordinate hB (adjoint_coordinate_witness y) x =
  inner_coordinate hC y (f x)) in hh.
by rewrite !inner_coordinateE in hh.
Qed.
End Coordinates.

(** Source for [adjoint_witness_exists]: Federer 1.7.4,
    p. 30, existence of an adjoint from the finite-dimensional
    source; supporting the factorisation in 1.7.3. *)
Theorem adjoint_witness_exists (R : rcfType) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (b : 'I_n -> V) (hb : is_basis b) (f : {linear V -> U}) :
  exists g : {linear U -> V}, is_adjoint B C f g.
Proof.
have [e [he ho]] := @orthonormal_basis_exists R V B hB n b hb.
exists (GRing.Linear.clone _ _ _ _ (@adjoint_coordinate_witness R V U C hC f n e) _).
exact (@adjoint_coordinate_specification R V U B C hB hC f n e he
  (orthonormalisation_orthonormal ho)).
Qed.
