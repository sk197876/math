(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import Alternating.
From Federer Require Import Convolution.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.2: naturality of Psi makes the dual map multiplicative. *)
Section Naturality.
Variable K : fieldType.
Variables X Y W : lmodType K.
Variable mu : W -> W -> W.
Hypothesis hmu : bilinear mu.
Variable f : {linear X -> Y}.
(** Source for [paired_tensor_natural]: Federer (1969), 1.4.2, p. 18, fourth
    consequence of the diagonal properties. In words: Pullback along a
    linear map is multiplicative for the alternating product. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma paired_tensor_natural (a b : Hom Y W) x :
  paired_tensor hmu a b (tensor_map f f x) =
    paired_tensor hmu (hom_comp a (hom_of_linear f)) (hom_comp b (hom_of_linear f)) x.
Proof.
apply: (tensor_ext (tensor_exists X X)
  (linear_comp (paired_tensor hmu a b) (tensor_map f f))
  (paired_tensor hmu (hom_comp a (hom_of_linear f)) (hom_comp b (hom_of_linear f)))) x => u v.
change (paired_tensor hmu a b (tensor_map f f (tensor_inj u v)) =
  paired_tensor hmu (hom_comp a (hom_of_linear f)) (hom_comp b (hom_of_linear f)) (tensor_inj u v)).
by rewrite tensor_mapE !paired_tensorE !hom_compE.
Qed.
Variables (DX : {linear X -> tensor_space X X}) (DY : {linear Y -> tensor_space Y Y}).
Hypothesis hD : forall x, DY (f x) = tensor_map f f (DX x).
(** Source for [convolution_natural]: Federer (1969), 1.4.2, p. 18, fourth
    consequence of the diagonal properties. In words: Pullback along a
    linear map is multiplicative for the alternating product. Supporting
    lemma for this passage; not separately stated in the book. *)
Theorem convolution_natural (a b : Hom Y W) :
  hom_comp (convolution hmu DY a b) (hom_of_linear f) =
    convolution hmu DX (hom_comp a (hom_of_linear f)) (hom_comp b (hom_of_linear f)).
Proof.
apply: hom_ext => x; rewrite hom_compE hom_of_linearE !convolutionE hD.
exact: paired_tensor_natural.
Qed.
End Naturality.
