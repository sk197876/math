(** Federer (1969), 1.7.4, p. 30: symmetry and orthogonality characterised
    by the adjoint. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerProductLaws AdjointUP
  AdjointLaws SymmetricEndomorphisms OrthogonalMaps BilinearNegation Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [symmetric_iff_adjoint_equal]: Federer 1.7.4,
    p. 30, f is symmetric exactly when f*=f. *)
Theorem symmetric_iff_adjoint_equal (R : realFieldType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (f a : {linear V -> V}) (ha : is_adjoint B B f a) :
  is_symmetric_endomorphism B f <-> a =1 f.
Proof.
split.
- move=> hf; exact: (@adjoint_unique R V V B B hB f a f ha (symmetric_self_adjoint hf)).
- move=> he x y; by rewrite -ha he.
Qed.

(** Source for [skewsymmetric_iff_adjoint_negative]: Federer
    1.7.4, p. 30, f is skewsymmetric exactly when f*=-f. *)
Theorem skewsymmetric_iff_adjoint_negative (R : realFieldType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (f a : {linear V -> V}) (ha : is_adjoint B B f a) :
  is_skewsymmetric_endomorphism B f <-> forall x, a x = -f x.
Proof.
split.
- move=> hf x; apply: (@inner_vectors_ext R V B hB) => z.
  by rewrite ha hf (bilNr (inner_bilinear hB)).
- move=> he x y; by rewrite -ha he (bilNr (inner_bilinear hB)).
Qed.

(** Source for [orthogonal_iff_adjoint_left_inverse]: Federer
    1.7.4, p. 30, f is an orthogonal injection exactly when
    f* composed with f is the identity. *)
Theorem orthogonal_iff_adjoint_left_inverse (R : realFieldType)
    (V U : lmodType R) (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (f : {linear V -> U}) (a : {linear U -> V})
    (ha : is_adjoint B C f a) :
  is_orthogonal_map B C f <-> cancel f a.
Proof.
split.
- move=> hf x; apply: (@inner_vectors_ext R V B hB) => z; by rewrite ha hf.
- move=> hi x y; by rewrite -ha hi.
Qed.

(** Source for [adjoint_source_square_symmetric]: Federer
    1.7.4, p. 30, f* composed with f is symmetric. *)
Theorem adjoint_source_square_symmetric (R : realFieldType)
    (V U : lmodType R) (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    (f : {linear V -> U}) (a : {linear U -> V})
    (ha : is_adjoint B C f a) :
  forall x y, B (a (f x)) y = B x (a (f y)).
Proof.
move=> x y; rewrite (inner_symmetric hB) !ha; exact (@inner_symmetric R U C hC (f y) (f x)).
Qed.

(** Source for [adjoint_target_square_symmetric]: Federer
    1.7.4, p. 30, f composed with f* is symmetric. *)
Theorem adjoint_target_square_symmetric (R : realFieldType)
    (V U : lmodType R) (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    (f : {linear V -> U}) (a : {linear U -> V})
    (ha : is_adjoint B C f a) :
  forall x y, C (f (a x)) y = C x (f (a y)).
Proof.
exact: (@adjoint_source_square_symmetric R U V C B hC hB a f
  (@adjoint_reverse R V U B C hB hC f a ha)).
Qed.
