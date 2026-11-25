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

(** Federer 1.5.3: the two square-zero operations underlying the
    auxiliary decomposition and the two kernel-image equivalences. *)
Section Nilpotency.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable v : V.
Variable alpha : A_m V K^o 1.
Local Notation E := (exterior_space V).
Local Notation ev := (exterior_generator v).
Local Notation a := (form_homogeneous alpha).
Local Notation conv := (convolution (scalar_bilinear K) (Psi h2 V)).
(** Source for [right_interior_square]: Federer (1969), 1.5.3, p. 23, first
    display and auxiliary decomposition in its proof. In words: If a
    one-covector alpha takes value one on v, every positive-degree form is v
    contracted into its product with alpha plus its contraction by v
    multiplied by alpha. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma right_interior_square (phi : Hom E K^o) :
  right_interior_hom ev (right_interior_hom ev phi) = 0.
Proof.
apply: hom_ext => x; rewrite !right_interior_homE hom_zeroE -wedge_assoc
  exterior_generator_square (bil0r (wedge_bilinear V)); exact: linear0.
Qed.
(** Source for [one_covector_square]: Federer (1969), 1.5.3, p. 23, first
    display and auxiliary decomposition in its proof. In words: If a
    one-covector alpha takes value one on v, every positive-degree form is v
    contracted into its product with alpha plus its contraction by v
    multiplied by alpha. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma one_covector_square : conv a a = 0.
Proof.
have hz := @one_generator_square_zero K h2 V (scalar_algebra K)
  (@mulrC K) (one_hom alpha).
change (alternating_wedge h2 (scalar_bilinear K)
  (form_include (one_form (one_hom alpha)))
  (form_include (one_form (one_hom alpha))) = 0) in hz.
rewrite one_homK in hz.
apply: hom_ext => x.
exact (congr1 (fun f : A_star V K^o => f x) hz).
Qed.
(** Source for [wedge_alpha_square_hom]: Federer (1969), 1.5.3, p. 23, first
    display and auxiliary decomposition in its proof. In words: If a
    one-covector alpha takes value one on v, every positive-degree form is v
    contracted into its product with alpha plus its contraction by v
    multiplied by alpha. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma wedge_alpha_square_hom (phi : Hom E K^o) : conv (conv phi a) a = 0.
Proof.
have hA := @convolution_associative K E K^o (fun x y : K^o => x*y)
  (scalar_bilinear K) (@mulrA K) (Psi h2 V) (@Psi_coassociative K h2 V) phi a a.
rewrite -hA one_covector_square; exact: (bil0r (@convolution_bilinear K E K^o _ (scalar_bilinear K) (Psi h2 V))).
Qed.
End Nilpotency.
