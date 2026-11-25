(** Federer (1969), 1.7.5, pp. 32-33: the general exterior product estimate,
    with binomial square-root constant. No finite-dimensional ambient
    hypothesis is imposed. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerProductRestriction OrthogonalMaps
  ExteriorNorm ExteriorNormNaturality FiniteWedgeNormBound ExteriorPairReduction
  ModuleQuotient SubspaceCarrier FiniteSpanSpace ExteriorGrading
  ExteriorMaps ExteriorHomogeneousProducts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Bound.
Variable R : rcfType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.

(** Source for [exterior_wedge_squared_bound]: Federer
    1.7.5, pp. 32-33, the general bound before taking
    square roots; the proof reduces both factors to one finite
    subspace and transports its estimate isometrically. *)
Theorem exterior_wedge_squared_bound p q (x : exterior_power V p) (y : exterior_power V q) :
  exterior_norm h2 hB (exterior_product x y)^+2 <=
    ('C(p+q,p))%:R * (exterior_norm h2 hB x)^+2 * (exterior_norm h2 hB y)^+2.
Proof.
have [n [e [he [a [b [ha hb]]]]]] := exterior_pair_finite_reduction x y.
pose S := finite_span_subspace e.
pose C := @restricted_inner_product R V B S.
have hC := @restricted_inner_productP R V B hB S.
have hi : is_orthogonal_map C B (subspace_inclusion S) by [].
have hh := @finite_wedge_squared_bound R h2 (finite_span_vect he)
  C hC n (finite_span_basis e) (finite_span_basisP he) p q a b.
rewrite -ha -hb -exterior_power_map_product.
by rewrite !(@exterior_norm_orthogonal_natural R h2 (finite_span_vect he) V C B hC hB
  (subspace_inclusion S) hi).
Qed.

(** Source for [exterior_wedge_norm_bound]: Federer 1.7.5,
    pp. 32-33, always |xi wedge eta| is bounded by
    sqrt(binomial(p+q,p)) times |xi| times |eta|, including
    degree-zero and zero-vector cases. *)
Theorem exterior_wedge_norm_bound p q (x : exterior_power V p) (y : exterior_power V q) :
  exterior_norm h2 hB (exterior_product x y) <=
    Num.sqrt (('C(p+q,p))%:R) * exterior_norm h2 hB x * exterior_norm h2 hB y.
Proof.
have hp : 0 <= Num.sqrt (('C(p+q,p))%:R) * exterior_norm h2 hB x * exterior_norm h2 hB y.
  apply: mulr_ge0; last exact: exterior_norm_nonnegative.
  exact: mulr_ge0 (sqrtr_ge0 _) (exterior_norm_nonnegative h2 hB x).
rewrite -(ler_sqr (exterior_norm_nonnegative h2 hB _) hp) !exprMn sqr_sqrtr ?ler0n //.
exact: exterior_wedge_squared_bound.
Qed.
End Bound.
