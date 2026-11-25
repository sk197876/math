(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import Tensor Bilinear AlgebraUP GradedAlgebra GradedSums
  TensorBilinear Koszul GradedTensor GradedTensorProduct.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Associativity.
Variable K : fieldType.
Variables A B : graded_algebra K.
Variable s : bool.
Local Notation GA := (algebra_grading A).
Local Notation GB := (algebra_grading B).
Local Notation ma := (@graded_mul K A).
Local Notation mb := (@graded_mul K B).
Local Notation mu := (@graded_tensor_mul K A B s).
Local Notation bil := (graded_tensor_bilinear A B s).
Hypotheses (hA : associative ma) (hB : associative mb).
(** Source for [graded_tensor_associative]: Federer (1969), 1.2.2, p. 12,
    item (2) and the following explanation. In words: The signed
    tensor-product multiplication inserts (-1)^(qr) when the middle factors
    have degrees q and r; signed tensor products of anticommutative algebras
    are anticommutative. Formalises the indicated part of the passage under
    the hypotheses in the statement below. *)
Lemma graded_tensor_associative : associative mu.
Proof.
apply: (tensor_homogeneous_induction (GA := GA) (GB := GB))
  => [y z|x x' hx hx' y z|k x hx y z|p q a b ha hb].
- by rewrite ?(bil0l bil) ?(bil0r bil) ?(bil0l bil).
- by rewrite ?(bilDl bil) ?(bilDr bil) ?(bilDl bil) hx hx'.
- by rewrite ?(bilZl bil) ?(bilZr bil) ?(bilZl bil) hx.
apply: (tensor_homogeneous_induction (GA := GA) (GB := GB))
  => [z|y y' hy hy' z|k y hy z|r t c d hc hd].
- by rewrite ?(bil0l bil) ?(bil0r bil) ?(bil0l bil).
- by rewrite ?(bilDl bil) ?(bilDr bil) ?(bilDl bil) hy hy'.
- by rewrite ?(bilZl bil) ?(bilZr bil) ?(bilZl bil) hy.
apply: (tensor_homogeneous_induction (GA := GA) (GB := GB))
  => [|z z' hz hz'|k z hz|u v e f he hf].
- by rewrite ?(bil0l bil) ?(bil0r bil) ?(bil0l bil).
- by rewrite ?(bilDl bil) ?(bilDr bil) ?(bilDl bil) hz hz'.
- by rewrite ?(bilZl bil) ?(bilZr bil) ?(bilZl bil) hz.
rewrite (@graded_tensor_mulE K A B s t u c d e f hd he) (bilZr bil)
  (@graded_tensor_mulE K A B s q (r+u) a b (ma c e) (mb d f) hb (graded_mul_degree hc he))
  (@graded_tensor_mulE K A B s q r a b c d hb hc) (bilZl bil)
  (@graded_tensor_mulE K A B s (q+t) u (ma a c) (mb b d) e f (graded_mul_degree hb hd) he)
  !scalerA hA hB koszul_cocycle.
by [].
Qed.
End Associativity.

Section Commutativity.
Variable K : fieldType.
Variables A B : graded_algebra K.
Local Notation GA := (algebra_grading A).
Local Notation GB := (algebra_grading B).
Local Notation ma := (@graded_mul K A).
Local Notation mb := (@graded_mul K B).
(** Source for [ordinary_tensor_commutative]: Federer (1969), 1.2.2, p. 12,
    explanation after the two product formulae. In words: The ordinary
    tensor product of two commutative algebras is commutative, whereas the
    signed tensor product of two anticommutative algebras is
    anticommutative. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Lemma ordinary_tensor_commutative : commutative ma -> commutative mb ->
  commutative (@graded_tensor_mul K A B false).
Proof.
move=> hA hB; have hb := graded_tensor_bilinear A B false.
have hflip : bilinear (fun x y => @graded_tensor_mul K A B false y x).
  by have [h1 h2] := hb; split.
apply: (tensor_homogeneous_bilinear_ext (GA:=GA) (GB:=GB) (GC:=GA) (GD:=GB) hb hflip)
  => p q r t a b c d ha hb' hc hd.
by rewrite (@graded_tensor_mulE K A B false q r a b c d hb' hc)
  (@graded_tensor_mulE K A B false t p c d a b hd ha) /koszul !scale1r hA hB.
Qed.

(** Source for [signed_tensor_anticommutative]: Federer (1969), 1.2.2, p.
    12, explanation after the two product formulae. In words: The ordinary
    tensor product of two commutative algebras is commutative, whereas the
    signed tensor product of two anticommutative algebras is
    anticommutative. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Lemma signed_tensor_anticommutative : graded_anticommutative GA ma ->
  graded_anticommutative GB mb ->
  graded_anticommutative (tensor_grading_product GA GB) (@graded_tensor_mul K A B true).
Proof.
move=> hA hB m n x y hx hy.
have bil := graded_tensor_bilinear A B true.
move: x hx; apply: tensor_component_induction
  => [|x x' hx hx'|k x hx|p q a b hpq ha hb].
- by rewrite (bil0l bil) (bil0r bil) scaler0.
- by rewrite (bilDl bil) (bilDr bil) hx hx' scalerDr.
- by rewrite (bilZl bil) (bilZr bil) hx !scalerA mulrC.
move: y hy; apply: tensor_component_induction
  => [|y y' hy hy'|k y hy|r t c d hrt hc hd].
- by rewrite (bil0l bil) (bil0r bil) scaler0.
- by rewrite (bilDl bil) (bilDr bil) hy hy' scalerDr.
- by rewrite (bilZl bil) (bilZr bil) hy !scalerA mulrC.
rewrite (@graded_tensor_mulE K A B true q r a b c d hb hc)
  (@graded_tensor_mulE K A B true t p c d a b hd ha)
  (hA _ _ _ _ ha hc) (hB _ _ _ _ hb hd)
  tensor_inj_scalel tensor_inj_scaler !scalerA -hpq -hrt.
rewrite -?mulrA.
change ((koszul K true q r * (koszul K true p r * koszul K true q t)) *:
  tensor_inj (ma c a) (mb d b) =
  (koszul K true (p+q) (r+t) * koszul K true t p) *: tensor_inj (ma c a) (mb d b)).
by rewrite koszul_anticomm.
Qed.
End Commutativity.
