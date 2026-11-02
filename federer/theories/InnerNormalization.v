(** Federer (1969), 1.7.1, p. 28: normalise a nonzero orthogonal residual to
    extend an orthonormal sequence. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerProductLaws InnerNorm
  OrthonormalFamilies Bilinear InfiniteSequence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Normalisation.
Variable R : rcfType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Local Notation N := (inner_norm hB).

(** Source for [inner_normalize]: Federer 1.7.1, p. 28,
    supporting Gram-Schmidt construction: divide a vector by its norm. *)
Definition inner_normalize v := (N v)^-1 *: v.

(** Source for [inner_normalize_square]: Federer 1.7.1,
    p. 28, normalising a nonzero vector gives diagonal inner product one. *)
Lemma inner_normalize_square v : v != 0 -> B (inner_normalize v) (inner_normalize v) = 1.
Proof.
move=> hv; rewrite /inner_normalize (inner_scale_square hB) -(inner_norm_sqr hB v).
by rewrite -exprMn mulVf ?expr1n // (inner_norm_eq0 hB).
Qed.

(** Source for [inner_normalizeK]: Federer 1.7.1, p. 28,
    multiplying the normalised vector by its norm recovers a nonzero input. *)
Lemma inner_normalizeK v : v != 0 -> N v *: inner_normalize v = v.
Proof.
move=> hv; by rewrite /inner_normalize scalerA mulfV ?scale1r // (inner_norm_eq0 hB).
Qed.

(** Source for [inner_normalize_orthogonal]: Federer 1.7.1,
    p. 28, normalisation preserves orthogonality to previous vectors. *)
Lemma inner_normalize_orthogonal v w : B v w = 0 -> B (inner_normalize v) w = 0.
Proof. move=> h; by rewrite /inner_normalize (bilZl (inner_bilinear hB)) h scaler0. Qed.

(** Source for [inner_normalize_norm]: Federer 1.7.1,
    p. 28, a normalised nonzero vector has norm one. *)
Lemma inner_normalize_norm v : v != 0 -> N (inner_normalize v) = 1.
Proof.
move=> hv; apply: inner_norm_value => //.
by rewrite expr1n inner_normalize_square.
Qed.

(** Source for [orthonormal_norm1]: Federer 1.7.1,
    p. 28, each vector of an orthonormal family has norm one. *)
Lemma orthonormal_norm1 (I : finType) (e : I -> V) :
  orthonormal_family B e -> forall i, N (e i) = 1.
Proof.
move=> he i; apply: inner_norm_value => //.
by rewrite expr1n he eqxx.
Qed.
End Normalisation.

Section Adjoin.
Variable R : realFieldType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable e : 'I_n -> V.
Variable v : V.

(** Source for [orthonormal_snoc]: Federer 1.7.1, p. 28,
    supporting induction step: adjoining a unit vector orthogonal to
    a preceding orthonormal sequence gives an orthonormal sequence. *)
Lemma orthonormal_snoc : orthonormal_family B e ->
  B v v = 1 -> (forall i, B v (e i) = 0) ->
  orthonormal_family B (ordinal_snoc e v).
Proof.
move=> he hv ho i j.
case: (unliftP ord_max i) => [a ->|->];
case: (unliftP ord_max j) => [b ->|->].
- by rewrite !ordinal_snoc_lift he (inj_eq (@lift_inj _ ord_max)).
- by rewrite ordinal_snoc_lift ordinal_snoc_last lift_eqF (inner_symmetric hB) ho.
- by rewrite ordinal_snoc_lift ordinal_snoc_last eq_liftF ho.
- by rewrite !ordinal_snoc_last eqxx.
Qed.
End Adjoin.
