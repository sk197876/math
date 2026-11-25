(** Federer (1969), 1.7.2, pp. 28-29: public interface for the dual inner
    product and norm. Only the sealed specification is used. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerPolarity InnerNorm
  LinearBasis AlternatingCoordinates.
From Federer Require Import InnerDualUP InnerDualSealed InnerPolaritySurjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Dual.
Variable R : rcfType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Local Notation F := (A_m V R^o 1).

(** Source for [inner_dual_product]: Federer 1.7.2, p. 28,
    the inner product making polarity orthogonal, provided by the
    sealed existence witness. Its characterising laws are exposed below. *)
Definition inner_dual_product : F -> F -> R := @InnerDual.product R V B hB n e he.

(** Source for [inner_dual_specification]: Federer 1.7.2,
    p. 28, the induced inner product satisfies its defining laws. *)
Theorem inner_dual_specification : is_dual_inner_product hB inner_dual_product.
Proof. exact: InnerDual.laws. Qed.

(** Source for [inner_dual_productP]: Federer 1.7.2, p. 28,
    the specified product on the dual is an inner product. *)
Theorem inner_dual_productP : is_inner_product inner_dual_product.
Proof. exact: dual_inner_product_laws inner_dual_specification. Qed.

(** Source for [inner_dual_polarityE]: Federer 1.7.2, p. 28,
    the inner-product polarity is orthogonal for the dual product. *)
Lemma inner_dual_polarityE x y :
  inner_dual_product (inner_polarity hB x) (inner_polarity hB y) = B x y.
Proof. exact (@dual_inner_product_polarity R V B hB inner_dual_product
  inner_dual_specification x y). Qed.

(** Source for [inner_dual_norm]: Federer 1.7.2, p. 28,
    the norm associated with the induced dual inner product. *)
Definition inner_dual_norm := inner_norm inner_dual_productP.

(** Source for [inner_dual_norm_polarity]: Federer 1.7.2,
    pp. 28-29, the polarity preserves norms for the induced dual metric. *)
Lemma inner_dual_norm_polarity x : inner_dual_norm (inner_polarity hB x) = inner_norm hB x.
Proof.
apply: inner_norm_value; first exact: inner_norm_nonnegative.
by rewrite inner_norm_sqr inner_dual_polarityE.
Qed.
End Dual.

(** Source for [inner_dual_product_basis_independent]: Federer
    1.7.2, p. 28, supporting intrinsicness: the specified dual inner
    product is independent of the finite basis used to prove existence. *)
Theorem inner_dual_product_basis_independent (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e)
    m (f : 'I_m -> V) (hf : is_basis f) a b :
    inner_dual_product hB he a b = inner_dual_product hB hf a b.
Proof.
apply: (@dual_inner_product_unique R V B hB).
- exact (@inner_polarity_surjective R V B hB n e he).
- exact: inner_dual_specification.
- exact: inner_dual_specification.
Qed.
