(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg fingroup perm.
From Federer Require Import Alternating.
From Federer Require Import AlternatingProduct AlternatingFamily NonemptyProduct
  MultipleShuffles OneDegreeShuffles OneFormFormula TriangularPermutation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.2, final sentence: if alpha_i(v_j)=0 whenever j<i,
    only the identity term of the permutation formula survives. The
    product of diagonal entries keeps its original order. *)
Section TriangularForms.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variables V W : lmodType K.
Variable mu : W -> W -> W.
Hypothesis hmu : bilinear mu.
Variable degrees : seq nat.
Hypothesis hone : all (pred1 1%N) degrees.
Variable alpha : form_family V W degrees.
Variable t : (sumn degrees).-tuple V.
Local Notation cast_i := (cast_ord (one_degrees_sum hone)).
Hypothesis htri : forall i j : 'I_(size degrees), (j < i)%N ->
  form_words (alpha i) [:: tnth t (cast_i j)] = 0.
(** Source for [triangular_product_term]: Federer (1969), 1.4.2, p. 19, last
    sentence, the triangular special case. In words: If the i-th one-form
    vanishes on every earlier vector, the product evaluates to the ordered
    product of the diagonal values. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma triangular_product_term (sigma : 'S_(sumn degrees)) : sigma != 1%g ->
  nonempty_product mu 0 (one_family_values hone alpha t sigma) = 0.
Proof.
move=> /permutation_lower [i hi]; apply: (@nonempty_product_zero K W mu hmu).
pose k := cast_ord (esym (one_degrees_sum hone)) i.
pose j := cast_ord (esym (one_degrees_sum hone)) (sigma i).
have hk : cast_i k = i := cast_ordKV (one_degrees_sum hone) i.
have hj : cast_i j = sigma i := cast_ordKV (one_degrees_sum hone) (sigma i).
apply/mapP; exists k; first exact: mem_enum.
rewrite hk -hj; symmetry; exact (@htri k j hi).
Qed.
(** Source for [triangular_one_form_product]: Federer (1969), 1.4.2, p. 19,
    last sentence, the triangular special case. In words: If the i-th
    one-form vanishes on every earlier vector, the product evaluates to the
    ordered product of the diagonal values. Formalises the indicated part of
    the passage under the hypotheses in the statement below. *)
Theorem triangular_one_form_product : degrees != [::] ->
  iterated_form h2 hmu alpha t =
    nonempty_product mu 0 [seq form_words (alpha i) [:: tnth t (cast_i i)]
      | i <- enum 'I_(size degrees)].
Proof.
move=> hd; rewrite (one_form_permutation_formula h2 hmu hone alpha t hd) (bigD1 1%g) //=.
have hz : (\sum_(sigma : 'S_(sumn degrees) | sigma != 1%g)
    FedererPermutation.index K sigma *: nonempty_product mu 0 (one_family_values hone alpha t sigma)) = 0.
  apply: big1 => sigma hs; by rewrite (triangular_product_term hs) scaler0.
rewrite hz addr0 (index_one h2) scale1r /one_family_values.
congr (nonempty_product _ _ _); apply: eq_map => i; by rewrite perm1.
Qed.
End TriangularForms.
