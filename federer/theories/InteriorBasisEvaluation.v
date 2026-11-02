(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorMultiplication.
From Federer Require Import OrderedBasisWords CovectorWords.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.5.2: evaluate both interior products using exactly the
    characteristic conditions of 1.5.1. *)
Section Evaluation.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable n : nat.
Variable e : 'I_n -> V.
Variable omega : 'I_n -> A_m V K^o 1.
Hypothesis hdual : forall i j, omega i [tuple e j] = if i == j then 1 else 0.
(** Source for [basis_word_pairing_seq]: Federer (1969), 1.5.2, p. 22, the
    two inclusion cases and the definitions of M and N. In words: A basis
    interior product vanishes unless the contracted index set is contained
    in the other; otherwise it is the complementary basis product with the
    appropriate crossing-count sign. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma basis_word_pairing_seq m (s : seq 'I_n) (mu : Lambda n m) : size s = m ->
  form_include (omega_lambda h2 omega mu) (exterior_word [seq e i | i <- s]) =
    if perm_eq s (val mu) then (-1 : K)^+(inversions (map val s)) else 0.
Proof.
move=> hs; have ht : size s == m by apply/eqP.
exact: (@basis_word_pairing K h2 V n m e omega hdual (Tuple ht) mu).
Qed.
(** Source for [covector_word_pairing_seq]: Federer (1969), 1.5.2, p. 22,
    the two inclusion cases and the definitions of M and N. In words: A
    basis interior product vanishes unless the contracted index set is
    contained in the other; otherwise it is the complementary basis product
    with the appropriate crossing-count sign. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma covector_word_pairing_seq m (s : seq 'I_n) (mu : Lambda n m) : size s = m ->
  covector_word h2 omega s (exterior_word [seq e i | i <- val mu]) =
    if perm_eq s (val mu) then (-1 : K)^+(inversions (map val s)) else 0.
Proof.
move=> hs; have ht : size s == m by apply/eqP.
exact: (@covector_word_pairing K h2 V n omega e hdual m (Tuple ht) mu).
Qed.
Variables p q : nat.
Variable hpq : (p <= q)%N.
Variables (lambda : Lambda n p) (mu : Lambda n q) (kappa : Lambda n (q-p)).
(** Source for [right_interior_basis_evaluation]: Federer (1969), 1.5.2, p.
    22, the two inclusion cases and the definitions of M and N. In words: A
    basis interior product vanishes unless the contracted index set is
    contained in the other; otherwise it is the complementary basis product
    with the appropriate crossing-count sign. Formalises the indicated part
    of the passage under the hypotheses in the statement below. *)
Theorem right_interior_basis_evaluation :
  pairing (e_lambda e (val kappa))
    (right_interior hpq (e_lambda e (val lambda)) (omega_lambda h2 omega mu)) =
  if perm_eq (val kappa ++ val lambda) (val mu)
    then (-1 : K)^+(inversions (map val (val kappa ++ val lambda))) else 0.
Proof.
rewrite right_interior_characteristic !e_lambdaE exterior_word_cat -map_cat.
change (form_include (omega_lambda h2 omega mu)
  (exterior_word [seq e i | i <- val kappa ++ val lambda]) =
  if perm_eq (val kappa ++ val lambda) (val mu)
    then (-1 : K)^+(inversions (map val (val kappa ++ val lambda))) else 0).
apply: basis_word_pairing_seq; by rewrite size_cat !size_tuple subnK.
Qed.
(** Source for [left_interior_basis_evaluation]: Federer (1969), 1.5.2, p.
    22, the two inclusion cases and the definitions of M and N. In words: A
    basis interior product vanishes unless the contracted index set is
    contained in the other; otherwise it is the complementary basis product
    with the appropriate crossing-count sign. Formalises the indicated part
    of the passage under the hypotheses in the statement below. *)
Theorem left_interior_basis_evaluation :
  pairing (left_interior h2 hpq (e_lambda e (val mu)) (omega_lambda h2 omega lambda))
    (omega_lambda h2 omega kappa) =
  if perm_eq (val lambda ++ val kappa) (val mu)
    then (-1 : K)^+(inversions (map val (val lambda ++ val kappa))) else 0.
Proof.
rewrite left_interior_characteristic.
change (form_homogeneous
  (form_reindex (subnKC hpq)
    (form_wedge h2 (scalar_bilinear K) (omega_lambda h2 omega lambda) (omega_lambda h2 omega kappa)))
  (exterior_word [seq e i | i <- val mu]) =
  if perm_eq (val lambda ++ val kappa) (val mu)
    then (-1 : K)^+(inversions (map val (val lambda ++ val kappa))) else 0).
rewrite form_reindexE.
change (form_include (form_wedge h2 (scalar_bilinear K)
  (omega_lambda h2 omega lambda) (omega_lambda h2 omega kappa))
  (exterior_word [seq e i | i <- val mu]) =
  if perm_eq (val lambda ++ val kappa) (val mu)
    then (-1 : K)^+(inversions (map val (val lambda ++ val kappa))) else 0).
rewrite form_wedge_include -!covector_word_Lambda covector_word_product.
apply: covector_word_pairing_seq; by rewrite size_cat !size_tuple subnKC.
Qed.
End Evaluation.
