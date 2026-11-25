(** Federer (1969), 3.2.46, pp. 281–282: local
    inner-product and coordinate membership proofs do not
    change the specified norms or Jacobians. These supporting
    facts follow from the independent norm and isometry laws;
    no proof-irrelevance axiom or private construction is used. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  EuclideanLinearMaps InnerProductUP InnerNorm PositiveSymmetricNormFactor
  RiemannianLinearJacobian EuclideanLinearJacobian.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [inner_norm_inner_proof_independent]: the
    nonnegative root specified by 1.7.1, p. 28, depends
    on the actual form, not the proof of its laws.
    Supporting local coordinate changes in 3.2.46, p. 282. *)
Lemma inner_norm_inner_proof_independent (R : rcfType) (V : lmodType R) B
    (hB hB' : @is_inner_product R V B) v : inner_norm hB v=inner_norm hB' v.
Proof.
apply: inner_norm_value; first exact: inner_norm_nonnegative.
exact: inner_norm_sqr.
Qed.

(** Source for [positive_norm_factor_inner_proof_independent]:
    the same actual positive factor satisfies the same norm
    and axis laws under another proof of the same inner
    product, supporting 3.2.46, p. 281. No different
    frame or factor is selected. *)
Lemma positive_norm_factor_inner_proof_independent (R : realType) n B
    (hB hB' : @is_inner_product R (R_n R n) B) L :
  is_positive_symmetric_norm_factor hB L -> is_positive_symmetric_norm_factor hB' L.
Proof.
move=> hL; constructor.
- exact: positive_norm_factor_symmetric hL.
- exact: positive_norm_factor_injective hL.
- exact: positive_norm_factor_surjective hL.
- move=> v; rewrite (positive_norm_factor_norm hL).
  exact: inner_norm_inner_proof_independent.
- have [e [he [ho hAxes]]] := positive_norm_factor_axes hL.
  exists e; split; first exact he; split; first exact ho.
  move=> i; have hA := hAxes i.
  by rewrite (@inner_norm_inner_proof_independent R (R_n R n) B hB hB' (e i)) in hA.
Qed.

(** Source for [riemannian_linear_jacobian_inner_proof_independent]:
    actual Riemannian Jacobians depend only on the original
    linear map and the actual two inner products, supporting
    3.2.46, p. 282. Local positive factors and their
    unique inverses compare both values with the same actual
    Euclidean coordinate map. No extra proof-irrelevance or
    differential field premise is introduced. *)
Theorem riemannian_linear_jacobian_inner_proof_independent (R : realType) m n B C
    (hB hB' : @is_inner_product R (R_n R m) B)
    (hC hC' : @is_inner_product R (R_n R n) C) k
    (F : Hom (R_n R m) (R_n R n)) :
  riemannian_linear_jacobian hB hC k F=riemannian_linear_jacobian hB' hC' k F.
Proof.
have [L hL] := positive_symmetric_norm_factor_exists hB.
have [M hM] := positive_symmetric_norm_factor_exists hC.
have hL' := @positive_norm_factor_inner_proof_independent R m B hB hB' L hL.
have hM' := @positive_norm_factor_inner_proof_independent R n C hC hC' M hM.
have [I [hLI [hIL hCoordinates]]] := riemannian_linear_jacobian_coordinates hL hM.
have [I' [hLI' [hIL' hCoordinates']]] := riemannian_linear_jacobian_coordinates hL' hM'.
have hInverse v : I v=I' v.
  have hValue := hLI' (I v); rewrite hIL in hValue; exact: esym hValue.
have hMap : hom_comp (hom_of_linear M) (hom_comp F (hom_of_linear I))=
    hom_comp (hom_of_linear M) (hom_comp F (hom_of_linear I')).
  apply: hom_ext=> v; change (M (F (I v))=M (F (I' v))); by rewrite hInverse.
by rewrite hCoordinates hCoordinates' hMap.
Qed.
