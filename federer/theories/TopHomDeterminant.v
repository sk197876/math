(** Federer (1969), 1.7.9, p. 35, the top-degree determinant and
    squared-difference formulas. The top degree is the dimension of the
    source, and the target is arbitrary. Empty determinants and degree-zero
    maps are included. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerProductLaws InnerNorm
  InnerExterior InnerExteriorPositivity HomInner ExteriorHomInner
  LinearBasis FiniteExteriorPowers FiniteOrdinalBasis ExteriorMaps ExteriorGrading
  Hom Adjoint AdjointUP TensorUP TracePower ExteriorDeterminant Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Top.
Variable R : rcfType.
Hypothesis h2 : (1+1 : R) != 0.
Variables V W : lmodType R.
Variable B : V -> V -> R.
Variable C : W -> W -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hC : is_inner_product C.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.

(** Source for [top_hom_inner_determinant]: Federer 1.7.9,
    p. 35, the first top-degree display: the inner product of
    the top exterior maps is det(adjoint f composed with g). *)
Theorem top_hom_inner_determinant (f g : {linear V -> W}) :
  exterior_hom_inner h2 hB hC hb n
    (hom_of_linear (exterior_power_map f n))
    (hom_of_linear (exterior_power_map g n)) =
  det h2 hb (linear_comp (inner_adjoint hB hC hb f) g).
Proof. by rewrite exterior_hom_inner_trace trace_top_power. Qed.

(** Source for [top_hom_difference_square]: Federer 1.7.9,
    p. 35, the second top-degree display: the squared norm of
    the difference of top exterior maps is the sum of the two
    self-adjoint-composite determinants minus twice the mixed one.
    Via Gamma this is exactly the printed tensor norm identity. *)
Theorem top_hom_difference_square (f g : {linear V -> W}) :
  hom_norm (@exterior_inner_productP R h2 V B hB n)
    (@exterior_inner_productP R h2 W C hC n)
    (finite_ordinal_basis (@finite_e_lambda_basis R n V b hb h2 n))
    (hom_of_linear (exterior_power_map f n) - hom_of_linear (exterior_power_map g n)) ^+2 =
  det h2 hb (linear_comp (inner_adjoint hB hC hb f) f) +
  det h2 hb (linear_comp (inner_adjoint hB hC hb g) g) -
  2 * det h2 hb (linear_comp (inner_adjoint hB hC hb f) g).
Proof.
rewrite inner_norm_sqr.
have hd := inner_bilinear (hom_inner_productP
  (@exterior_inner_productP R h2 V B hB n)
  (@exterior_inner_productP R h2 W C hC n)
  (finite_ordinal_basis (@finite_e_lambda_basis R n V b hb h2 n))).
rewrite (bilBl hd) !(bilBr hd).
rewrite (inner_symmetric (hom_inner_productP _ _ _)
  (hom_of_linear (exterior_power_map g n)) (hom_of_linear (exterior_power_map f n))).
rewrite opprB addrACA -opprD -mulr2n.
change (exterior_hom_inner h2 hB hC hb n
  (hom_of_linear (exterior_power_map f n)) (hom_of_linear (exterior_power_map f n)) +
  exterior_hom_inner h2 hB hC hb n
  (hom_of_linear (exterior_power_map g n)) (hom_of_linear (exterior_power_map g n)) -
  (exterior_hom_inner h2 hB hC hb n
  (hom_of_linear (exterior_power_map f n)) (hom_of_linear (exterior_power_map g n))) *+ 2 =
  det h2 hb (linear_comp (inner_adjoint hB hC hb f) f) +
  det h2 hb (linear_comp (inner_adjoint hB hC hb g) g) -
  2 * det h2 hb (linear_comp (inner_adjoint hB hC hb f) g)).
by rewrite !top_hom_inner_determinant mulr_natl.
Qed.
End Top.
