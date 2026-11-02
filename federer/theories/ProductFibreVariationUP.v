(** Federer (1969), 2.5.20, p. 114: the measure is obtained from the
    variation lambda of T=mu o S. Under S the norm-bound condition in
    2.5.12(5), p. 103, becomes |u(x,y)|<=f(x). This specification keeps that
    least-upper-bound law independent of a chosen realization of E=K(Y).
    Source context: CompactFunctionSpaceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import CompactSupportFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_product_fibre_variation]: equivalent
    variation specification under the isomorphism S in Federer
    2.5.20, p. 114, using 2.5.12(5), p. 103.
    Existence is proved for nonnegative f in K(X). *)
Record is_product_fibre_variation (R : realType) (X Y : topologicalType)
    (mu : ((X*Y) -> R) -> R) (f : X -> R) (a : R) : Prop := {
  (** Source for [product_fibre_variation_upper]: the upper-bound
      law for lambda(f), 2.5.12(5), p. 103, applied
      in Federer 2.5.20, p. 114. *)
  product_fibre_variation_upper : forall u,
    compactly_supported_continuous_functions u ->
    (forall x y, `|u (x,y)|<=f x) -> mu u<=a;
  (** Source for [product_fibre_variation_least]: the least-bound
      law for lambda(f), 2.5.12(5), p. 103, applied
      in Federer 2.5.20, p. 114. *)
  product_fibre_variation_least : forall b,
    (forall u, compactly_supported_continuous_functions u ->
      (forall x y, `|u (x,y)|<=f x) -> mu u<=b) -> a<=b
}.

(** Source for [product_fibre_variation_unique]: uniqueness
    of the variation value from its supremum laws, supporting
    identification of the measure in Federer 2.5.20, p. 114. *)
Lemma product_fibre_variation_unique (R : realType) (X Y : topologicalType)
    (mu : ((X*Y) -> R) -> R) (f : X -> R) a b :
  is_product_fibre_variation mu f a -> is_product_fibre_variation mu f b -> a=b.
Proof.
move=> ha hb; apply/eqP; rewrite eq_le; apply/andP; split.
- exact: (@product_fibre_variation_least R X Y mu f a ha b
    (@product_fibre_variation_upper R X Y mu f b hb)).
- exact: (@product_fibre_variation_least R X Y mu f b hb a
    (@product_fibre_variation_upper R X Y mu f a ha)).
Qed.
