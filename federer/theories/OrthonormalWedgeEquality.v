(** Federer (1969), 1.7.5, p. 32: equality for the wedge of two orthonormal
    products. The corrected product equality criterion applies because every
    factor here is a unit vector. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm ExteriorNorm
  OrthonormalFamilies OrthonormalConcatenation ExteriorHadamardEquality
  ConcatenatedFamilies ConcatenatedProducts ExteriorHomogeneousProducts
  ExteriorGrading FiniteExteriorPowers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [orthonormal_products_wedge_equality]: Federer
    1.7.5, p. 32, two unit simple products have wedge norm
    one exactly when every factor of one is orthogonal to every
    factor of the other. *)
Theorem orthonormal_products_wedge_equality (R : rcfType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    p q (e : 'I_p -> V) (f : 'I_q -> V)
    (he : orthonormal_family B e) (hf : orthonormal_family B f) :
  exterior_norm h2 hB (exterior_product (e_lambda e (ord_tuple p))
    (e_lambda f (ord_tuple q))) = 1 <-> forall i j, B (e i) (f j) = 0.
Proof.
rewrite concatenated_product.
have hn i := @orthonormal_concatenation_unit R V B hB p q e f he hf i.
have hnz i : concatenate_family e f i != 0.
  rewrite -(inner_norm_eq0 hB) hn oner_eq0; by [].
have hp : (\prod_i inner_norm hB (concatenate_family e f i)) = 1.
  apply: big1 => i _; exact: hn.
split.
- move=> hh.
  have ho := @exterior_product_norm_equality_nonzero R h2 V B hB (p+q)
    (concatenate_family e f) hnz (eq_trans hh (esym hp)).
  move=> i j.
  have hneq : lshift q i != rshift p j by rewrite eq_lrshift.
  have h := ho (lshift q i) (rshift p j) hneq.
  by rewrite concatenate_family_l concatenate_family_r in h.
- move=> ho; exact (@orthonormal_product_unit_norm R h2 V B hB (p+q)
    (concatenate_family e f) (@orthonormal_concatenation R V B hB p q e f he hf ho)).
Qed.
