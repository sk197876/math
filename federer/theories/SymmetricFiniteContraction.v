(** Federer (1969), 1.10.4, p. 46: the finite contraction sum defining
    Taylor coefficients. This supporting module extends right contraction
    from one homogeneous form to a finite sum of forms. Contraction itself
    works over any field, without finite dimension. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From Federer Require Import TensorUP Bilinear Graded GradedSums GradedComponents
  Hom HomogeneousHom BoundedHom HomogeneousSum SymmetricAlgebra
  SymmetricGrading SymmetricForms SymmetricFormSum SymmetricRightInteriorHom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section FiniteContraction.
Variable K : fieldType.
Variables V W : lmodType K.
Local Notation E := (symmetric_space V).
Local Notation G := (symmetric_grading V).
Local Notation A := (S_star V W).
Variable r : nat.
Variable eta : symmetric_power V r.

(** Source for [symmetric_contraction_bounded]: Federer 1.10.4,
    p. 46, supporting finiteness of the Taylor coefficient sums.
    Precomposition with a homogeneous multiplication preserves any
    upper bound for the degrees of a functional. *)
Lemma symmetric_contraction_bounded (f : A) N : hom_bounded G f N ->
  hom_bounded G (symmetric_right_interior_hom (component_val eta) f) N.
Proof.
move=> hf n xi hn hxi; rewrite symmetric_right_interior_homE.
apply: hf (symmetric_product_graded hxi (component_homogeneous eta)).
exact: leq_trans hn (leq_addr _ _).
Qed.

(** Source for [symmetric_contraction_finite]: Federer 1.10.4,
    p. 46, supporting existence of a finite homogeneous bound for
    each contraction in the Taylor coefficient construction. *)
Lemma symmetric_contraction_finite (f : A) :
  exists N, hom_bounded G (symmetric_right_interior_hom (component_val eta) f) N.
Proof.
have [N hN] := hom_finite_bound f; exists N.
exact: symmetric_contraction_bounded hN.
Qed.

(** Source for [symmetric_finite_contraction]: Federer 1.10.4,
    p. 46, contraction with a homogeneous symmetric vector applied
    to a finite sum of symmetric forms. Its defining map is the
    characteristic multiplication composite from 1.10.3, p. 45. *)
Definition symmetric_finite_contraction (f : A) : A :=
  @FiniteHom K E W G (symmetric_right_interior_hom (component_val eta) f)
    (introT (asboolP _) (symmetric_contraction_finite f)).

(** Source for [symmetric_finite_contractionE]: Federer 1.10.4,
    p. 46, the characteristic pairing for a term of the Taylor
    coefficient sum: evaluation is multiplication before applying f. *)
Lemma symmetric_finite_contractionE f xi :
  symmetric_finite_contraction f xi = f (symmetric_product xi (component_val eta)).
Proof. by []. Qed.

(** Source for [symmetric_finite_contraction_linear]: Federer
    1.10.4, p. 46, supporting linearity in the original coefficient
    forms for the Taylor construction. *)
Lemma symmetric_finite_contraction_linear : linear symmetric_finite_contraction.
Proof.
move=> a f g; apply: hom_finite_ext=> xi.
by rewrite !symmetric_finite_contractionE !hom_finite_addE !hom_finite_scaleE.
Qed.
HB.instance Definition _ := GRing.isLinear.Build K A A *:%R
  symmetric_finite_contraction symmetric_finite_contraction_linear.
End FiniteContraction.

(** Source for [symmetric_finite_contraction_parameter_linear]:
    Federer 1.10.4, p. 46, supporting linearity of each Taylor
    coefficient in the symmetric vector being contracted. *)
Lemma symmetric_finite_contraction_parameter_linear (K : fieldType)
    (V W : lmodType K) r (f : S_star V W) :
  linear (fun eta : symmetric_power V r => symmetric_finite_contraction eta f).
Proof.
move=> a eta theta; apply: hom_finite_ext=> xi.
rewrite !symmetric_finite_contractionE hom_finite_addE hom_finite_scaleE.
rewrite (linearP (@component_val K (symmetric_space V) (symmetric_grading V) r)).
rewrite (proj2 (symmetric_product_bilinear V)); exact: linearP.
Qed.
