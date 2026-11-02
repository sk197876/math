(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorDuality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.5.3: the two summands of Psi(xi wedge v), in the order
    fixed by right interior multiplication in 1.5.1. *)
Section Actions.
Variable K : fieldType.
Variable V : lmodType K.
Local Notation E := (exterior_unital V).
Local Notation EG := (unital_graded_view E).
Local Notation T := (unital_graded_tensor E E true).
Local Notation u := (exterior_unit V).
Local Notation ev := (@exterior_generator K V).
(** Source for [Psi_right_first]: Federer (1969), 1.5.3, p. 23, first
    display and auxiliary decomposition in its proof. In words: If a
    one-covector alpha takes value one on v, every positive-degree form is v
    contracted into its product with alpha plus its contraction by v
    multiplied by alpha. Definition or construction used to formalise this
    passage. *)
Definition Psi_right_first v (t : T) := alg_mul T t (tensor_inj (ev v) u).
(** Source for [Psi_right_second]: Federer (1969), 1.5.3, p. 23, first
    display and auxiliary decomposition in its proof. In words: If a
    one-covector alpha takes value one on v, every positive-degree form is v
    contracted into its product with alpha plus its contraction by v
    multiplied by alpha. Definition or construction used to formalise this
    passage. *)
Definition Psi_right_second v (t : T) := alg_mul T t (tensor_inj u (ev v)).
(** Source for [Psi_right_first_linear]: Federer (1969), 1.5.3, p. 23, first
    display and auxiliary decomposition in its proof. In words: If a
    one-covector alpha takes value one on v, every positive-degree form is v
    contracted into its product with alpha plus its contraction by v
    multiplied by alpha. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma Psi_right_first_linear v : linear (Psi_right_first v).
Proof. exact: (proj1 (alg_bilinear T)). Qed.
(** Source for [Psi_right_second_linear]: Federer (1969), 1.5.3, p. 23,
    first display and auxiliary decomposition in its proof. In words: If a
    one-covector alpha takes value one on v, every positive-degree form is v
    contracted into its product with alpha plus its contraction by v
    multiplied by alpha. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma Psi_right_second_linear v : linear (Psi_right_second v).
Proof. exact: (proj1 (alg_bilinear T)). Qed.
HB.instance Definition _ v := GRing.isLinear.Build K T T *:%R
  (Psi_right_first v) (Psi_right_first_linear v).
HB.instance Definition _ v := GRing.isLinear.Build K T T *:%R
  (Psi_right_second v) (Psi_right_second_linear v).
(** Source for [Psi_right_firstE]: Federer (1969), 1.5.3, p. 23, first
    display and auxiliary decomposition in its proof. In words: If a
    one-covector alpha takes value one on v, every positive-degree form is v
    contracted into its product with alpha plus its contraction by v
    multiplied by alpha. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma Psi_right_firstE v q x y : homogeneous (exterior_grading V) q y ->
  Psi_right_first v (tensor_inj x y) =
    (-1 : K)^+q *: tensor_inj (wedge x (ev v)) y.
Proof.
move=> hy; apply: eq_trans (@graded_tensor_mulE K EG EG true q 1 x y
  (ev v) u hy (exterior_generator_homogeneous v)) _.
change (koszul K true q 1 *: tensor_inj (wedge x (ev v)) (wedge y u) =
  (-1 : K)^+q *: tensor_inj (wedge x (ev v)) y).
by rewrite /koszul muln1 wedge_unitr.
Qed.
(** Source for [Psi_right_secondE]: Federer (1969), 1.5.3, p. 23, first
    display and auxiliary decomposition in its proof. In words: If a
    one-covector alpha takes value one on v, every positive-degree form is v
    contracted into its product with alpha plus its contraction by v
    multiplied by alpha. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma Psi_right_secondE v q x y : homogeneous (exterior_grading V) q y ->
  Psi_right_second v (tensor_inj x y) = tensor_inj x (wedge y (ev v)).
Proof.
move=> hy; apply: eq_trans (@graded_tensor_mulE K EG EG true q 0 x y
  u (ev v) hy (exterior_unit_homogeneous V)) _.
change (koszul K true q 0 *: tensor_inj (wedge x u) (wedge y (ev v)) =
  tensor_inj x (wedge y (ev v))).
by rewrite koszul0r scale1r wedge_unitr.
Qed.
(** Source for [Psi_right_product]: Federer (1969), 1.5.3, p. 23, first
    display and auxiliary decomposition in its proof. In words: If a
    one-covector alpha takes value one on v, every positive-degree form is v
    contracted into its product with alpha plus its contraction by v
    multiplied by alpha. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma Psi_right_product (h2 : (1+1 : K) != 0) v (x : E) :
  Psi h2 V (wedge x (ev v)) =
    Psi_right_first v (Psi h2 V x) + Psi_right_second v (Psi h2 V x).
Proof.
apply: eq_trans (@algebra_map_mul K (exterior_algebra V) T (Psi h2 V) x (ev v)) _.
rewrite PsiE; exact: (bilDr (alg_bilinear T)).
Qed.
End Actions.
