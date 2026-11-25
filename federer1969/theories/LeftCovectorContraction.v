(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorDuality.
From Federer Require Import OneCovectorFactors.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.5.3, the dual equation: contraction of the two terms of
    Psi(v wedge xi). The counit identifies the first term with xi. *)
Section Contraction.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable alpha : A_m V K^o 1.
Local Notation E := (exterior_space V).
Local Notation G := (exterior_grading V).
Local Notation T := (tensor_space E E).
Local Notation ev := (@exterior_generator K V).
Local Notation a := (form_homogeneous alpha).
Local Notation C := (@contract_tensor K E E a).

(** Source for [contraction_left_action]: Federer (1969), 1.5.3, p. 23,
    final displayed dual equation. In words: A multivector splits as the
    contraction of v wedge xi by alpha plus v wedged with the contraction of
    xi by alpha. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma contraction_left_action v (t : T) :
  C (Psi_left_action v t) = one_hom alpha v *: counit_left V t.
Proof.
elim/(tensor_homogeneous_induction (GA:=G) (GB:=G)): t =>
  [|s t hs ht|c t ht|p q x y hx hy].
- by rewrite !linear0 ?scaler0.
- rewrite !linearD.
  change (C (Psi_left_action v s) + C (Psi_left_action v t) =
    one_hom alpha v *: counit_left V s + one_hom alpha v *: counit_left V t).
  by rewrite hs ht.
- rewrite (linZ (Psi_left_action_linear v)) (linZ (linearP C)) (linZ (linearP (counit_left V))).
  change (c *: C (Psi_left_action v t) = one_hom alpha v *: (c *: counit_left V t)).
  rewrite ht !scalerA; congr (_ *: _); exact: mulrC.
- rewrite (Psi_left_factor v y hx) contract_tensorE one_covector_left_factor counit_leftE.
  by rewrite scalerA.
Qed.
(** Source for [contraction_right_action]: Federer (1969), 1.5.3, p. 23,
    final displayed dual equation. In words: A multivector splits as the
    contraction of v wedge xi by alpha plus v wedged with the contraction of
    xi by alpha. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma contraction_right_action v (t : T) :
  C (Psi_right_action v t) = - wedge (ev v) (C t).
Proof.
elim/(tensor_homogeneous_induction (GA:=G) (GB:=G)): t =>
  [|s t hs ht|c t ht|p q x y hx hy].
- by rewrite !linear0 (bil0r (wedge_bilinear V)) oppr0.
- rewrite (linD (Psi_right_action_linear v)) (linD (linearP C)) (linD (linearP C)).
  change (C (Psi_right_action v s) + C (Psi_right_action v t) =
    - wedge (ev v) (C s + C t)).
  by rewrite hs ht (bilDr (wedge_bilinear V)) opprD.
- rewrite (linZ (Psi_right_action_linear v)) (linZ (linearP C)) (linZ (linearP C)).
  change (c *: C (Psi_right_action v t) = - wedge (ev v) (c *: C t)).
  by rewrite ht (bilZr (wedge_bilinear V)) scalerN.
- rewrite (Psi_right_factor v y hx) linearZ !contract_tensorE (bilZr (wedge_bilinear V)).
  change (((-1 : K)^+p) *: ((a x : K) *: wedge (ev v) y) = - ((a x : K) *: wedge (ev v) y)).
  case hp: (p == 1).
  + move/eqP: hp => ->; by rewrite expr1 scaleN1r.
  + rewrite (hom_m_degree a (negbT hp) hx) !scale0r scaler0 oppr0; by [].
Qed.
(** Source for [Psi_left_product]: Federer (1969), 1.5.3, p. 23, final
    displayed dual equation. In words: A multivector splits as the
    contraction of v wedge xi by alpha plus v wedged with the contraction of
    xi by alpha. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma Psi_left_product v (x : E) :
  Psi h2 V (wedge (ev v) x) =
    Psi_left_action v (Psi h2 V x) + Psi_right_action v (Psi h2 V x).
Proof.
apply: eq_trans (@algebra_map_mul K (exterior_algebra V)
  (unital_graded_tensor (exterior_unital V) (exterior_unital V) true)
  (Psi h2 V) (ev v) x) _.
rewrite PsiE; exact: (bilDl (alg_bilinear (unital_graded_tensor (exterior_unital V) (exterior_unital V) true))).
Qed.
(** Source for [left_covector_product]: Federer (1969), 1.5.3, p. 23, final
    displayed dual equation. In words: A multivector splits as the
    contraction of v wedge xi by alpha plus v wedged with the contraction of
    xi by alpha. Supporting lemma for this passage; not separately stated in
    the book. *)
Theorem left_covector_product v (x : E) :
  left_interior_hom h2 (wedge (ev v) x) a =
    (one_hom alpha v : K) *: x - wedge (ev v) (left_interior_hom h2 x a).
Proof.
rewrite /left_interior_hom Psi_left_product linearD.
change (C (Psi_left_action v (Psi h2 V x)) + C (Psi_right_action v (Psi h2 V x)) =
  (one_hom alpha v : K) *: x - wedge (ev v) (C (Psi h2 V x))).
apply: eq_trans (congr2 (+%R) (@contraction_left_action v (Psi h2 V x))
  (@contraction_right_action v (Psi h2 V x))) _.
by rewrite (@counit_left_Psi K V h2 x).
Qed.
End Contraction.
