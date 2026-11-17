(** Supporting Federer (1969), 3.4.8(5), p. 328:
    original polynomial germs behind the exact representative law.
    The existence proof and representative choice stay opaque. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP InnerProductUP InnerNorm HilbertFormCompactness LinearBasis
  PolynomialFunctions AnalyticGermRing AnalyticPolynomialGermUP AnalyticPolynomialGermExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type AnalyticPolynomialGermsSignature.
(** Source for [map]: the original polynomial's actual germ,
    supporting Federer 3.4.8(5), p. 328. *)
Parameter map:forall (R:realType) (X:lmodType R) (B:X->X->R) (hB:is_inner_product B)
  n (e:'I_n->X) (he:is_basis e) a,PolynomialFunction X R^o->
    @analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) a.
(** Source for [laws]: the exact original representative equation,
    supporting Federer 3.4.8(5), p. 328, before any derivative law. *)
Parameter laws:forall (R:realType) (X:lmodType R) (B:X->X->R) (hB:is_inner_product B)
  n (e:'I_n->X) (he:is_basis e) a,is_analytic_polynomial_germ_map (@map R X B hB n e he a).
End AnalyticPolynomialGermsSignature.
Module AnalyticPolynomialGerms:AnalyticPolynomialGermsSignature.
(** Source for [map]: private choice from proved original polynomial
    germ existence, supporting Federer 3.4.8(5), p. 328. *)
Definition map (R:realType) (X:lmodType R) (B:X->X->R) (hB:is_inner_product B)
    n (e:'I_n->X) (he:is_basis e) a:=
  projT1 (cid (@analytic_polynomial_germ_map_exists R X B hB n e he a)).
(** Source for [laws]: the chosen map satisfies the independent
    representative law, supporting Federer 3.4.8(5), p. 328. *)
Lemma laws (R:realType) (X:lmodType R) (B:X->X->R) (hB:is_inner_product B)
    n (e:'I_n->X) (he:is_basis e) a:
  is_analytic_polynomial_germ_map (@map R X B hB n e he a).
Proof. exact:(projT2 (cid (@analytic_polynomial_germ_map_exists R X B hB n e he a))). Qed.
End AnalyticPolynomialGerms.
