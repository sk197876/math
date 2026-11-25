(** Federer (1969), 1.7.2, p. 28: orthogonal injections. The defining
    property is abstract; injectivity follows from it and positive
    definiteness. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerProductLaws InnerNorm
  OrthonormalFamilies EuclideanInnerProduct Bilinear TensorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_orthogonal_map]: Federer 1.7.2, p. 28,
    definition: a linear map preserves the inner products of all pairs. *)
Definition is_orthogonal_map (R : fieldType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R) (f : {linear V -> W}) :=
  forall x y, C (f x) (f y) = B x y.

(** Source for [orthogonal_map_injective]: Federer 1.7.2, p. 28,
    supporting justification of the word injection in the definition. *)
Lemma orthogonal_map_injective (R : realFieldType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    (f : {linear V -> W}) : is_orthogonal_map B C f -> injective f.
Proof.
move=> hf x y h; apply/eqP; rewrite -subr_eq0 -(inner_self_eq0 hB).
have hz : f (x-y) = 0 by rewrite linearB h subrr.
by rewrite -hf hz (bil0l (inner_bilinear hC)) eqxx.
Qed.

(** Source for [orthogonal_map_norm]: Federer 1.7.2, p. 28,
    supporting consequence: an orthogonal map preserves the norm. *)
Lemma orthogonal_map_norm (R : rcfType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    (f : {linear V -> W}) : is_orthogonal_map B C f ->
    forall x, inner_norm hC (f x) = inner_norm hB x.
Proof.
move=> hf x; apply: inner_norm_value; first exact: inner_norm_nonnegative.
by rewrite inner_norm_sqr hf.
Qed.

(** Source for [orthogonal_map_orthonormal]: Federer 1.7.2, p. 28,
    supporting preservation of orthonormal families. *)
Lemma orthogonal_map_orthonormal (R : fieldType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R) (f : {linear V -> W})
    (I : finType) (e : I -> V) : is_orthogonal_map B C f ->
    orthonormal_family B e -> orthonormal_family C (fun i => f (e i)).
Proof. move=> hf he i j; by rewrite hf he. Qed.

(** Source for [orthogonal_identity]: Federer 1.7.2, p. 28,
    supporting identity law for the orthogonal group. *)
Lemma orthogonal_identity (R : fieldType) (V : lmodType R)
    (B : V -> V -> R) : is_orthogonal_map B B (linear_id V).
Proof. by move=> x y. Qed.

(** Source for [orthogonal_composition]: Federer 1.7.2, p. 28,
    supporting closure under composition for the orthogonal group. *)
Lemma orthogonal_composition (R : fieldType) (U V W : lmodType R)
    (A : U -> U -> R) (B : V -> V -> R) (C : W -> W -> R)
    (f : {linear U -> V}) (g : {linear V -> W}) :
    is_orthogonal_map A B f -> is_orthogonal_map B C g ->
    is_orthogonal_map A C (linear_comp g f).
Proof. move=> hf hg x y; by rewrite /linear_comp /= hg hf. Qed.

(** Source for [orthogonal_inverse]: Federer 1.7.2, p. 28,
    supporting closure under inverses: a linear inverse to an orthogonal
    isomorphism preserves the inner products in the reverse direction. *)
Lemma orthogonal_inverse (R : fieldType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (f : {linear V -> W}) (g : {linear W -> V}) :
    is_orthogonal_map B C f -> cancel g f -> is_orthogonal_map C B g.
Proof. move=> hf hg x y; by rewrite -hf !hg. Qed.
