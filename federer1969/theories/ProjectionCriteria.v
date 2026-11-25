(** Federer (1969), 1.7.4, pp. 30-31: orthogonal projections and their
    adjoint characterisation. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP AdjointUP AdjointLaws
  AdjointCriteria OrthogonalMaps TensorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [projection_iff_adjoint_orthogonal]: Federer
    1.7.4, p. 30, the adjoint of an orthogonal injection is an
    orthogonal projection, and conversely. *)
Theorem projection_iff_adjoint_orthogonal (R : realFieldType)
    (V U : lmodType R) (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    (p : {linear V -> U}) (a : {linear U -> V})
    (ha : is_adjoint B C p a) :
  is_orthogonal_projection B C p <-> is_orthogonal_map C B a.
Proof.
split.
- move=> [h [ho hh]].
  have hr := @adjoint_reverse R U V C B hC hB h p hh.
  have he := @adjoint_unique R V U B C hB p a h ha hr.
  move=> x y; by rewrite !he ho.
- move=> ho; exists a; split; first exact ho.
  exact: adjoint_reverse ha.
Qed.

(** Source for [projection_iff_adjoint_right_inverse]: Federer
    1.7.4, p. 30, g is an orthogonal projection exactly when
    g composed with g* is the identity of its target. *)
Theorem projection_iff_adjoint_right_inverse (R : realFieldType)
    (V U : lmodType R) (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    (p : {linear V -> U}) (a : {linear U -> V})
    (ha : is_adjoint B C p a) :
  is_orthogonal_projection B C p <-> cancel a p.
Proof.
rewrite (@projection_iff_adjoint_orthogonal R V U B C hB hC p a ha).
exact: (@orthogonal_iff_adjoint_left_inverse R U V C B hC a p
  (@adjoint_reverse R V U B C hB hC p a ha)).
Qed.

(** Source for [orthogonal_projection_composition]: Federer
    1.7.4, p. 31, supporting closure of projections under
    composition, by composing their orthogonal adjoints. *)
Theorem orthogonal_projection_composition (R : realFieldType)
    (V U W : lmodType R) (B : V -> V -> R)
    (C : U -> U -> R) (D : W -> W -> R)
    (p : {linear V -> U}) (q : {linear U -> W}) :
  is_orthogonal_projection B C p -> is_orthogonal_projection C D q ->
  is_orthogonal_projection B D (linear_comp q p).
Proof.
move=> [a [ha hpa]] [b [hb hqb]].
exists (linear_comp a b); split.
- exact: orthogonal_composition hb ha.
- exact: adjoint_composition hqb hpa.
Qed.
