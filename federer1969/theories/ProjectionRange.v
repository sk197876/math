(** Federer (1969), 1.7.4, p. 31, final paragraph: recover a vector in the
    image of an adjoint injection by projecting and then injecting it.
    Supporting consequence of the identity in 1.7.4, p. 30. editions:
    InnerProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ModuleQuotient SubspaceSums InnerProductUP
  AdjointUP ProjectionCriteria OrthogonalMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [projection_inverse_on_adjoint_range]: Federer
    1.7.4, p. 31, supporting step for the common-factor argument:
    the adjoint followed after projection is identity on its image. *)
Lemma projection_inverse_on_adjoint_range (R : realFieldType)
    (V U : lmodType R) (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    (p : {linear V -> U}) (a : {linear U -> V})
    (ha : is_adjoint B C p a) (hp : is_orthogonal_projection B C p)
    x : range_subspace a x -> a (p x) = x.
Proof.
move=> [y ->].
have hk := proj1 (@projection_iff_adjoint_right_inverse R V U B C hB hC p a ha) hp.
by rewrite hk.
Qed.
