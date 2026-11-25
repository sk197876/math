(** Federer (1969), 1.7.11, p. 36, opening definition: f:S times T -> V
    sends (x,y) to x-y. Its source carries the product of the two restricted
    inner products. These maps use the actual subspace carriers, not ambient
    pairs satisfying an informal membership condition. Source context and
    ingredients: ProductInnerUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerProductRestriction ProductInner
  ModuleQuotient SubspaceCarrier.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Difference.
Variable R : realFieldType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variables S T : subspace V.

(** Source for [subspace_product_inner]: Federer 1.7.11,
    p. 36, the inner product on S times T used by the
    displayed orthonormal family. *)
Definition subspace_product_inner := product_inner
  (@restricted_inner_productP R V B hB S)
  (@restricted_inner_productP R V B hB T).

(** Source for [subspace_product_innerP]: Federer 1.7.11,
    p. 36, the induced metric on S times T is an inner product. *)
Theorem subspace_product_innerP : is_inner_product subspace_product_inner.
Proof. exact: product_inner_productP. Defined.

(** Source for [subspace_difference]: Federer 1.7.11,
    p. 36, first display: the difference map on S times T. *)
Definition subspace_difference (x : (subspace_space S * subspace_space T)%type) : V :=
  subspace_val x.1 - subspace_val x.2.

(** Source for [subspace_difference_linear]: Federer 1.7.11,
    p. 36, the opening sentence identifies the difference map as linear. *)
Lemma subspace_difference_linear : linear subspace_difference.
Proof.
move=> a x y; rewrite /subspace_difference /= !linearP scalerBr.
change (a *: subspace_val x.1 + subspace_val y.1 +
  (a *: (-subspace_val x.2) - subspace_val y.2) =
  a *: subspace_val x.1 - a *: subspace_val x.2 +
  (subspace_val y.1 - subspace_val y.2)).
by rewrite scalerN addrACA.
Qed.
HB.instance Definition _ := GRing.isLinear.Build R
  (GRing.Lmodule.clone R (subspace_space S * subspace_space T)%type _) V *:%R
  subspace_difference subspace_difference_linear.

(** Source for [subspace_difference_diagonal]: Federer 1.7.11,
    p. 36, the vectors (e_i,e_i) in the displayed family lie
    in the kernel of the difference map. *)
Lemma subspace_difference_diagonal x (hs : S x) (ht : T x) :
  subspace_difference (subspace_lift hs, subspace_lift ht) = 0.
Proof. by rewrite /subspace_difference !subspace_liftE subrr. Qed.
End Difference.

Arguments subspace_product_inner {R V B} hB S T _ _.
Arguments subspace_product_innerP {R V B} hB S T.
Arguments subspace_difference {R V} S T _.
