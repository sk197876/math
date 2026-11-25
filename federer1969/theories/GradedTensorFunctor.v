(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import Tensor Bilinear GradedAlgebra GradedSums Koszul
  GradedTensor GradedTensorProduct GradedTensorLaws GradedTensorMaps GradedUnit.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section GradedTensorMap.
Variable K : fieldType.
Variables A B C D : lmodType K.
Variables (GA : grading A) (GB : grading B) (GC : grading C) (GD : grading D).
Variables (f : {linear A -> C}) (g : {linear B -> D}).
Hypotheses (hf : preserves_grading GA GC f) (hg : preserves_grading GB GD g).
(** Source for [tensor_map_graded]: Federer (1969), 1.2.2, pp. 11-12, the
    two tensor-product structures. In words: The ordinary and signed
    products extend multiplication on homogeneous pure tensors; tensor
    products of compatible graded algebra maps preserve these structures.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Lemma tensor_map_graded : preserves_grading (tensor_grading_product GA GB)
  (tensor_grading_product GC GD) (tensor_map f g).
Proof.
move=> n x hx; move: x hx; apply: tensor_component_induction
  => [|x y hx hy|k x hx|p q a b hpq ha hb].
- rewrite linear0; exact: homogeneous0.
- rewrite linearD; exact: homogeneousD hx hy.
- rewrite linearZ; exact: homogeneousZ hx.
rewrite tensor_mapE -hpq; exact: tensor_homogeneous_pure (hf ha) (hg hb).
Qed.
End GradedTensorMap.

Section MultiplicativeTensorMap.
Variable K : fieldType.
Variables A B C D : graded_algebra K.
Variables (f : {linear A -> C}) (g : {linear B -> D}).
Hypotheses (hf : preserves_grading (algebra_grading A) (algebra_grading C) f)
  (hg : preserves_grading (algebra_grading B) (algebra_grading D) g)
  (hfM : forall a b, f (@graded_mul K A a b) = @graded_mul K C (f a) (f b))
  (hgM : forall a b, g (@graded_mul K B a b) = @graded_mul K D (g a) (g b)).
(** Source for [tensor_map_multiplicative]: Federer (1969), 1.2.2, pp.
    11-12, the two tensor-product structures. In words: The ordinary and
    signed products extend multiplication on homogeneous pure tensors;
    tensor products of compatible graded algebra maps preserve these
    structures. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Lemma tensor_map_multiplicative s x y :
  tensor_map f g (graded_tensor_mul s x y) =
  graded_tensor_mul s (tensor_map f g x) (tensor_map f g y).
Proof.
apply: (tensor_homogeneous_bilinear_ext
  (GA:=algebra_grading A) (GB:=algebra_grading B)
  (GC:=algebra_grading A) (GD:=algebra_grading B)
  (bilinear_post (tensor_map f g) (graded_tensor_bilinear A B s))
  (bilinear_pre (tensor_map f g) (tensor_map f g) (graded_tensor_bilinear C D s))) x y.
move=> p q r t a b c d ha hb hc hd.
by rewrite (graded_tensor_mulE s a d hb hc) linearZ /= !tensor_mapE
  (graded_tensor_mulE s (f a) (g d) (hg hb) (hf hc)) hfM hgM.
Qed.
End MultiplicativeTensorMap.

Section TensorUnits.
Variable K : fieldType.
Variables A B : graded_algebra K.
Variable s : bool.
Local Notation GA := (algebra_grading A).
Local Notation GB := (algebra_grading B).
Local Notation ma := (@graded_mul K A).
Local Notation mb := (@graded_mul K B).
Local Notation mu := (@graded_tensor_mul K A B s).
Local Notation bil := (graded_tensor_bilinear A B s).
Variables (u : A) (v : B).
Hypotheses (hAl : left_id u ma) (hAr : right_id u ma)
  (hBl : left_id v mb) (hBr : right_id v mb).
(** Source for [tensor_unit_left]: Federer (1969), 1.2.2, p. 12, item (2)
    and the following explanation. In words: The signed tensor-product
    multiplication inserts (-1)^(qr) when the middle factors have degrees q
    and r; signed tensor products of anticommutative algebras are
    anticommutative. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Lemma tensor_unit_left : left_id (tensor_inj u v) mu.
Proof.
have hv := @graded_unit_degree_zero K B GB mb (graded_bilinear B)
  (@graded_mul_degree K B) v hBl hBr.
apply: (tensor_homogeneous_induction (GA:=GA) (GB:=GB))
  => [|x y hx hy|k x hx|p q a b ha hb].
- exact: bil0r bil _.
- by rewrite (bilDr bil) hx hy.
- by rewrite (bilZr bil) hx.
by rewrite (graded_tensor_mulE s u b hv ha) koszul0l scale1r hAl hBl.
Qed.
(** Source for [tensor_unit_right]: Federer (1969), 1.2.2, p. 12, item (2)
    and the following explanation. In words: The signed tensor-product
    multiplication inserts (-1)^(qr) when the middle factors have degrees q
    and r; signed tensor products of anticommutative algebras are
    anticommutative. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Lemma tensor_unit_right : right_id (tensor_inj u v) mu.
Proof.
have hu := @graded_unit_degree_zero K A GA ma (graded_bilinear A)
  (@graded_mul_degree K A) u hAl hAr.
apply: (tensor_homogeneous_induction (GA:=GA) (GB:=GB))
  => [|x y hx hy|k x hx|p q a b ha hb].
- exact: bil0l bil _.
- by rewrite (bilDl bil) hx hy.
- by rewrite (bilZl bil) hx.
by rewrite (graded_tensor_mulE s a v hb hu) koszul0r scale1r hAr hBr.
Qed.
End TensorUnits.
