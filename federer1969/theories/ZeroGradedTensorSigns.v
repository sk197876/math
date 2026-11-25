(** Supporting connections for Federer 1.4.5, p. 20. If a factor has
    only degree zero, the sign in 1.2.2(2), p. 12, is always one on
    nonzero homogeneous tensors. Reuse the original signed tensor law. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Graded GradedTensor GradedTensorProduct
  GradedTensorLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Signs.
Variable K : fieldType.
Variables A B : graded_algebra K.
Local Notation GA := (algebra_grading A).
Local Notation GB := (algebra_grading B).

(** Source for [zero_left_grade_tensor_signs_agree]: supporting connection
    for Federer 1.4.5, p. 20, using 1.2.2(1)-(2), pp. 11-12. If the
    left factor vanishes in positive degrees, the ordinary and signed
    products agree on every tensor. Use homogeneous tensor induction. *)
Lemma zero_left_grade_tensor_signs_agree :
    (forall p x, (0<p)%N -> homogeneous GA p x -> x=0) ->
    forall x y, @graded_tensor_mul K A B false x y =
      @graded_tensor_mul K A B true x y.
Proof.
move=> hz.
apply: (tensor_homogeneous_bilinear_ext (GA:=GA) (GB:=GB)
  (GC:=GA) (GD:=GB) (graded_tensor_bilinear A B false)
  (graded_tensor_bilinear A B true)) => p q r t a b c d ha hb hc hd.
rewrite (@graded_tensor_mulE K A B false q r a b c d hb hc)
  (@graded_tensor_mulE K A B true q r a b c d hb hc).
case: r hc => [|r] hc.
- by rewrite /koszul muln0 expr0 !scale1r.
- have hc0 := hz r.+1 c (ltn0Sn r) hc.
  by rewrite hc0 (bil0r (@graded_bilinear K A)) tensor_inj0l !scaler0.
Qed.

(** Source for [zero_right_grade_tensor_signs_agree]: supporting
    connection for Federer 1.4.5, p. 20, using 1.2.2(1)-(2), pp. 11-12.
    If the right factor vanishes in positive degrees, the ordinary and
    signed products agree, including zero and arbitrary tensor sums. *)
Lemma zero_right_grade_tensor_signs_agree :
    (forall p x, (0<p)%N -> homogeneous GB p x -> x=0) ->
    forall x y, @graded_tensor_mul K A B false x y =
      @graded_tensor_mul K A B true x y.
Proof.
move=> hz.
apply: (tensor_homogeneous_bilinear_ext (GA:=GA) (GB:=GB)
  (GC:=GA) (GD:=GB) (graded_tensor_bilinear A B false)
  (graded_tensor_bilinear A B true)) => p q r t a b c d ha hb hc hd.
rewrite (@graded_tensor_mulE K A B false q r a b c d hb hc)
  (@graded_tensor_mulE K A B true q r a b c d hb hc).
case: q hb => [|q] hb.
- by rewrite /koszul mul0n expr0 !scale1r.
- have hb0 := hz q.+1 b (ltn0Sn q) hb.
  by rewrite hb0 (bil0l (@graded_bilinear K B)) tensor_inj0r !scaler0.
Qed.
End Signs.
