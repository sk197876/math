(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorDecomposition.
From Federer Require Import SingleIndexContraction.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.6.1, first corollary: a nonzero exterior product has
    independent factors. For each coefficient of a linear relation,
    multiply by the complementary product, so that every other term
    has a repeated factor. *)
Section Independence.
Variable K : fieldType.
Variable V : lmodType K.
Variable m : nat.
Variable e : 'I_m -> V.
Local Notation X := (exterior_word [seq e i | i <- enum 'I_m]).
(** Source for [nonzero_word_independent]: Federer (1969), 1.6.1, p. 24,
    first of the four corollaries. In words: The printed corollary
    identifies nonzero simple m-vectors with those whose associated space
    has dimension m, and represents them as products of a suitable basis.
    Supporting lemma for this passage; not separately stated in the book.
    For the literal empty-product definition the reverse implication
    requires m>0. *)
Theorem nonzero_word_independent : X != 0 -> finite_independent e.
Proof.
move=> hX c hc i.
pose lambda := Lambda_single i.
pose nu := top_complement lambda.
pose w (v : V) := wedge (exterior_generator v) (component_val (e_lambda e (val nu))).
have hw : linear w.
  move=> a x y; rewrite /w linearP (bilDl (wedge_bilinear V)) (bilZl (wedge_bilinear V)); by [].
have hz j : j != i -> w (e j) = 0.
  move=> hji; have hj' : j \in Lambda_set nu.
    by rewrite /nu /top_complement nu_image Lambda_top_set /lambda Lambda_single_set in_setD in_set1 in_setT hji.
  have hj : j \in val nu by move: hj'; rewrite /Lambda_set inE.
  rewrite /w e_lambdaE -exterior_word_cons.
  change (exterior_word [seq e a | a <- j :: val nu] = 0).
  apply: exterior_word_map_nonuniq; by rewrite /= hj.
have hs : sorted leq (map val (val (Lambda_top m))).
  have := valP (Lambda_top m); by rewrite ltn_sorted_uniq_leq => /andP [].
have hp := top_complement_permutation lambda.
have hi := @exterior_index_word_order K V m e (val lambda ++ val nu)
  (val (Lambda_top m)) hs hp.
have hi' : w (e i) = (-1 : K)^+(inversions (map val (val lambda ++ val nu))) *: X.
  rewrite /w e_lambdaE -exterior_word_cons; exact: hi.
have hwi : w (e i) != 0.
  by rewrite hi' scaler_eq0 negb_or expf_neq0 ?oppr_eq0 ?oner_eq0 // hX.
have hsum : w (\sum_j c j *: e j) = c i *: w (e i).
  rewrite (big_morph w (linD hw) (lin0 hw)).
  under eq_bigr do rewrite (linZ hw).
  rewrite (bigD1 i) //=.
  have hzero : (\sum_(j | j != i) c j *: w (e j)) = 0.
    apply: big1 => j hj; by rewrite hz // scaler0.
  by rewrite hzero addr0.
rewrite hc (lin0 hw) in hsum.
have heq : c i *: w (e i) == 0 by apply/eqP; exact: esym hsum.
by move: heq; rewrite scaler_eq0 (negbTE hwi) orbF => /eqP.
Qed.
End Independence.
