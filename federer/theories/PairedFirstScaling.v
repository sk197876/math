(** Federer (1969), 1.8.2, p. 40: extending the unit-vector
    equality case to arbitrary lengths requires absorbing a positive
    scalar into one complex pair. Scaling both members of the first
    real pair by t multiplies the paired vector by t squared. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SimpleVectors PairedRealVectors Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Scaling.
Variable K : fieldType.
Variable V : lmodType K.
Variable k : nat.

(** Source for [scale_first_family]: Federer 1.8.2,
    p. 40, supporting replacement of the first vector by its scalar multiple. *)
Definition scale_first_family (t : K) (a : 'I_k.+1 -> V) j :=
  if j == ord0 then t *: a j else a j.

(** Source for [scale_first_family_zero]: Federer 1.8.2,
    p. 40, the first member is multiplied by t. *)
Lemma scale_first_family_zero t a : scale_first_family t a ord0 = t *: a ord0.
Proof. by rewrite /scale_first_family eqxx. Qed.

(** Source for [scale_first_family_lift]: Federer 1.8.2,
    p. 40, the remaining family members are unchanged. *)
Lemma scale_first_family_lift t a i :
  scale_first_family t a (lift ord0 i) = a (lift ord0 i).
Proof. by rewrite /scale_first_family lift_eqF. Qed.

(** Source for [paired_real_vector_first_word]: Federer 1.8.2,
    p. 40, separating the first pair from the remaining interleaved product. *)
Lemma paired_real_vector_first_word (a b : 'I_k.+1 -> V) :
  component_val (paired_real_vector a b) =
  wedge (exterior_generator (a ord0))
    (wedge (exterior_generator (b ord0))
      (exterior_word (flatten [seq [:: a (lift ord0 i); b (lift ord0 i)] | i <- enum 'I_k]))).
Proof.
by rewrite paired_real_vector_word enum_ordSl map_cons -map_comp /= !exterior_word_cons.
Qed.

(** Source for [paired_real_vector_scale_first]: Federer 1.8.2,
    p. 40, multiplying both members of one pair by t multiplies
    the entire paired product by t squared. No independence is required. *)
Theorem paired_real_vector_scale_first t (a b : 'I_k.+1 -> V) :
  paired_real_vector (scale_first_family t a) (scale_first_family t b) =
    t^+2 *: paired_real_vector a b.
Proof.
apply: val_inj; rewrite linearZ.
change (component_val (paired_real_vector (scale_first_family t a) (scale_first_family t b)) =
  t^+2 *: component_val (paired_real_vector a b)).
rewrite !paired_real_vector_first_word !scale_first_family_zero.
have ht : flatten [seq [:: scale_first_family t a (lift ord0 i);
      scale_first_family t b (lift ord0 i)] | i <- enum 'I_k] =
    flatten [seq [:: a (lift ord0 i); b (lift ord0 i)] | i <- enum 'I_k].
  congr (flatten _); apply: eq_map => i; by rewrite !scale_first_family_lift.
by rewrite ht !linearZ !(bilZl (wedge_bilinear V)) (bilZr (wedge_bilinear V)) scalerA expr2.
Qed.
End Scaling.
