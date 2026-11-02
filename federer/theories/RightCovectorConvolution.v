(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorDuality.
From Federer Require Import OneCovectorFactors RightPsiActions.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.5.3: the covector identity, before restriction to degree j.
    The two tensor calculations preserve the order phi wedge alpha. *)
Section Convolution.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable alpha : A_m V K^o 1.
Local Notation E := (exterior_space V).
Local Notation G := (exterior_grading V).
Local Notation T := (tensor_space E E).
Local Notation ev := (@exterior_generator K V).
Local Notation a := (form_homogeneous alpha).
Local Notation P := (paired_tensor (scalar_bilinear K)).
Variable phi : Hom E K^o.

(** Source for [paired_right_first]: Federer (1969), 1.5.3, p. 23, first
    display and auxiliary decomposition in its proof. In words: If a
    one-covector alpha takes value one on v, every positive-degree form is v
    contracted into its product with alpha plus its contraction by v
    multiplied by alpha. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma paired_right_first v (t : T) :
  P phi a (Psi_right_first v t) = - P (right_interior_hom (ev v) phi) a t.
Proof.
elim/(tensor_homogeneous_induction (GA:=G) (GB:=G)): t =>
  [|s t hs ht|c t ht|p q x y hx hy].
- by rewrite !linear0 ?oppr0.
- rewrite (linD (Psi_right_first_linear v)) (linD (linearP (P phi a)))
    (linD (linearP (P (right_interior_hom (ev v) phi) a))); change
    (P phi a (Psi_right_first v s) + P phi a (Psi_right_first v t) =
      - (P (right_interior_hom (ev v) phi) a s + P (right_interior_hom (ev v) phi) a t)).
  by rewrite hs ht opprD.
- rewrite (linZ (Psi_right_first_linear v)) (linZ (linearP (P phi a)))
    (linZ (linearP (P (right_interior_hom (ev v) phi) a))); change
    (c *: P phi a (Psi_right_first v t) = - (c *: P (right_interior_hom (ev v) phi) a t)).
  by rewrite ht scalerN.
- rewrite (Psi_right_firstE v x hy) linearZ !paired_tensorE right_interior_homE.
  change (((-1 : K)^+q) *: (phi (wedge x (ev v)) * a y) = - (phi (wedge x (ev v)) * a y)).
  case hq: (q == 1).
  + move/eqP: hq => ->; by rewrite expr1 scaleN1r.
  + rewrite (hom_m_degree a (negbT hq) hy) !mulr0 scaler0 oppr0; by [].
Qed.
(** Source for [paired_right_second]: Federer (1969), 1.5.3, p. 23, first
    display and auxiliary decomposition in its proof. In words: If a
    one-covector alpha takes value one on v, every positive-degree form is v
    contracted into its product with alpha plus its contraction by v
    multiplied by alpha. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma paired_right_second v (t : T) :
  P phi a (Psi_right_second v t) = one_hom alpha v * phi (counit_right V t).
Proof.
elim/(tensor_homogeneous_induction (GA:=G) (GB:=G)): t =>
  [|s t hs ht|c t ht|p q x y hx hy].
- by rewrite !linear0 ?mulr0.
- rewrite !linearD; change
    (P phi a (Psi_right_second v s) + P phi a (Psi_right_second v t) =
      one_hom alpha v * (phi (counit_right V s) + phi (counit_right V t))).
  by rewrite hs ht mulrDr.
- rewrite !linearZ; change
    (c * P phi a (Psi_right_second v t) = one_hom alpha v * (c * phi (counit_right V t))).
  by rewrite ht mulrCA.
- rewrite (Psi_right_secondE v x hy) paired_tensorE one_covector_right_factor counit_rightE linearZ.
  change (phi x * (exterior_augmentation V y * one_hom alpha v) =
    one_hom alpha v * (exterior_augmentation V y * phi x)).
  by rewrite mulrCA [phi x * one_hom alpha v]mulrC -mulrCA.
Qed.
(** Source for [right_covector_product]: Federer (1969), 1.5.3, p. 23, first
    display and auxiliary decomposition in its proof. In words: If a
    one-covector alpha takes value one on v, every positive-degree form is v
    contracted into its product with alpha plus its contraction by v
    multiplied by alpha. Supporting lemma for this passage; not separately
    stated in the book. *)
Theorem right_covector_product v (x : E) :
  convolution (scalar_bilinear K) (Psi h2 V) phi a (wedge x (ev v)) =
    one_hom alpha v * phi x -
      convolution (scalar_bilinear K) (Psi h2 V) (right_interior_hom (ev v) phi) a x.
Proof.
rewrite !convolutionE.
rewrite Psi_right_product linearD.
change (P phi a (Psi_right_first v (Psi h2 V x)) +
  P phi a (Psi_right_second v (Psi h2 V x)) =
  one_hom alpha v * phi x - P (right_interior_hom (ev v) phi) a (Psi h2 V x)).
apply: eq_trans (congr2 (+%R) (@paired_right_first v (Psi h2 V x))
  (@paired_right_second v (Psi h2 V x))) _.
rewrite (@counit_right_Psi K V h2 x); exact: addrC.
Qed.
End Convolution.
