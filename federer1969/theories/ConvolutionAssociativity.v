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

(** Federer 1.4.2: associativity follows from the coassociativity diagram
    in 1.3.3 and associativity of the coefficient multiplication. *)
Section Associativity.
Variable K : fieldType.
Variables X W : lmodType K.
Variable mu : W -> W -> W.
Hypothesis hmu : bilinear mu.
Hypothesis hA : associative mu.
Local Notation T := (tensor_space X X).
Local Notation L := (tensor_space T X).
Local Notation R := (tensor_space X T).
(** Source for [paired_triple_left]: Federer (1969), 1.4.2, p. 18, first
    consequence of the diagonal properties. In words: Associative
    coefficient multiplication gives associative alternating multiplication.
    Definition or construction used to formalise this passage. *)
Definition paired_triple_left (a b c : Hom X W) : {linear L -> W} :=
  paired_tensor hmu (hom_of_linear (paired_tensor hmu a b)) c.
(** Source for [paired_triple_right]: Federer (1969), 1.4.2, p. 18, first
    consequence of the diagonal properties. In words: Associative
    coefficient multiplication gives associative alternating multiplication.
    Definition or construction used to formalise this passage. *)
Definition paired_triple_right (a b c : Hom X W) : {linear R -> W} :=
  paired_tensor hmu a (hom_of_linear (paired_tensor hmu b c)).
(** Source for [paired_triple_leftE]: Federer (1969), 1.4.2, p. 18, first
    consequence of the diagonal properties. In words: Associative
    coefficient multiplication gives associative alternating multiplication.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma paired_triple_leftE a b c x y z :
  paired_triple_left a b c (tensor_inj (tensor_inj x y) z) = mu (mu (a x) (b y)) (c z).
Proof. by rewrite /paired_triple_left !paired_tensorE. Qed.
(** Source for [paired_triple_rightE]: Federer (1969), 1.4.2, p. 18, first
    consequence of the diagonal properties. In words: Associative
    coefficient multiplication gives associative alternating multiplication.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma paired_triple_rightE a b c x y z :
  paired_triple_right a b c (tensor_inj x (tensor_inj y z)) = mu (a x) (mu (b y) (c z)).
Proof. by rewrite /paired_triple_right !paired_tensorE. Qed.
(** Source for [paired_triple_associator]: Federer (1969), 1.4.2, p. 18,
    first consequence of the diagonal properties. In words: Associative
    coefficient multiplication gives associative alternating multiplication.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma paired_triple_associator a b c x :
  paired_triple_right a b c (tensor_associator X X X x) = paired_triple_left a b c x.
Proof.
apply: (tensor_triple_ext_l (linear_comp (paired_triple_right a b c)
  (tensor_associator X X X)) (paired_triple_left a b c)) x => u v w.
change (paired_triple_right a b c (tensor_associator X X X (tensor_inj (tensor_inj u v) w)) =
  paired_triple_left a b c (tensor_inj (tensor_inj u v) w)).
by rewrite tensor_associatorE paired_triple_rightE paired_triple_leftE hA.
Qed.

Variable D : {linear X -> T}.
Hypothesis hD : forall x,
  tensor_associator X X X (tensor_map D (linear_id X) (D x)) =
    tensor_map (linear_id X) D (D x).
(** Source for [convolution_left_factorisation]: Federer (1969), 1.4.2, p.
    18, first consequence of the diagonal properties. In words: Associative
    coefficient multiplication gives associative alternating multiplication.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma convolution_left_factorisation a b c x :
  paired_tensor hmu (convolution hmu D a b) c x =
    paired_triple_left a b c (tensor_map D (linear_id X) x).
Proof.
apply: (tensor_ext (tensor_exists X X)
  (paired_tensor hmu (convolution hmu D a b) c)
  (linear_comp (paired_triple_left a b c) (tensor_map D (linear_id X)))) x => u v.
change (paired_tensor hmu (convolution hmu D a b) c (tensor_inj u v) =
  paired_triple_left a b c (tensor_map D (linear_id X) (tensor_inj u v))).
by rewrite tensor_mapE /paired_triple_left !paired_tensorE convolutionE.
Qed.
(** Source for [convolution_right_factorisation]: Federer (1969), 1.4.2, p.
    18, first consequence of the diagonal properties. In words: Associative
    coefficient multiplication gives associative alternating multiplication.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma convolution_right_factorisation a b c x :
  paired_tensor hmu a (convolution hmu D b c) x =
    paired_triple_right a b c (tensor_map (linear_id X) D x).
Proof.
apply: (tensor_ext (tensor_exists X X)
  (paired_tensor hmu a (convolution hmu D b c))
  (linear_comp (paired_triple_right a b c) (tensor_map (linear_id X) D))) x => u v.
change (paired_tensor hmu a (convolution hmu D b c) (tensor_inj u v) =
  paired_triple_right a b c (tensor_map (linear_id X) D (tensor_inj u v))).
by rewrite tensor_mapE /paired_triple_right !paired_tensorE convolutionE.
Qed.
(** Source for [convolution_associative]: Federer (1969), 1.4.2, p. 18,
    first consequence of the diagonal properties. In words: Associative
    coefficient multiplication gives associative alternating multiplication.
    Supporting lemma for this passage; not separately stated in the book. *)
Theorem convolution_associative : associative (convolution hmu D).
Proof.
move=> a b c; apply: hom_ext => x.
rewrite !convolutionE convolution_left_factorisation convolution_right_factorisation.
by rewrite -hD paired_triple_associator.
Qed.
End Associativity.
