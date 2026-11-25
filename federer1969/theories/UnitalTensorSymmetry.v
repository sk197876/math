(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import Graded UnitalGradedTensor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.2.2 and 1.3.3: interchange, packaged as a unit-preserving
    algebra homomorphism for use in the diagonal-map identities. *)
Section Interchange.
Variable K : fieldType.
Variables A B : unital_graded_algebra K.
Variable s : bool.
Local Notation AG := (unital_graded_view A).
Local Notation BG := (unital_graded_view B).
Local Notation f := (graded_swap (unital_grading A) (unital_grading B) s).

(** Source for [unital_tensor_swap]: Federer (1969), 1.2.2, p. 12, paragraph
    on the standard interchange isomorphism. In words: Interchange of
    homogeneous tensor factors of degrees p and q carries the sign (-1)^(pq)
    for the signed product and no sign for the ordinary product. Definition
    or construction used to formalise this passage. *)
Definition unital_tensor_swap : algebra_map
    (unital_tensor_algebra A B s) (unital_tensor_algebra B A s).
Proof.
apply: (@AlgebraMap K (unital_tensor_algebra A B s) (unital_tensor_algebra B A s) f).
- change (f (tensor_inj (alg_one A) (alg_one B)) = tensor_inj (alg_one B) (alg_one A)).
  by rewrite (graded_swapE s (unital_one_homogeneous A) (unital_one_homogeneous B))
    koszul0l scale1r.
- exact: (@graded_swap_mul K AG BG s).
Defined.
(** Source for [unital_tensor_swap_graded]: Federer (1969), 1.2.2, p. 12,
    paragraph on the standard interchange isomorphism. In words: Interchange
    of homogeneous tensor factors of degrees p and q carries the sign
    (-1)^(pq) for the signed product and no sign for the ordinary product.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma unital_tensor_swap_graded : preserves_grading
  (unital_grading (unital_graded_tensor A B s))
  (unital_grading (unital_graded_tensor B A s)) unital_tensor_swap.
Proof. exact: graded_swap_graded. Qed.
End Interchange.

Section InducedMap.
Variable K : fieldType.
Variables A B C D : unital_graded_algebra K.
Variables (f : algebra_map A C) (g : algebra_map B D).
Hypotheses (hf : preserves_grading (unital_grading A) (unital_grading C) f)
  (hg : preserves_grading (unital_grading B) (unital_grading D) g).
Variable s : bool.
(** Source for [unital_tensor_map_graded]: Federer (1969), 1.2.2, p. 12,
    paragraph on the standard interchange isomorphism. In words: Interchange
    of homogeneous tensor factors of degrees p and q carries the sign
    (-1)^(pq) for the signed product and no sign for the ordinary product.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma unital_tensor_map_graded : preserves_grading
  (unital_grading (unital_graded_tensor A B s))
  (unital_grading (unital_graded_tensor C D s)) (unital_tensor_map hf hg s).
Proof. exact: tensor_map_graded hf hg. Qed.
End InducedMap.
