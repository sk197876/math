(** Federer (1969), 1.8.2, p. 40: the paired one-form products
    in the orthogonal normal form commute and each has square zero.
    These are supporting consequences of graded anticommutativity,
    Federer 1.4.2, p. 19. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import BoundedHom HomogeneousHom AlgebraUP Bilinear BilinearNegation GradedAlgebra AlternatingForms
  AlternatingSum AlternatingProduct AlternatingUnit ScalarCoefficients.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Blocks.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Local Notation A := (alternating_unital_algebra h2 V (scalar_algebra K)).
Local Notation G := (A_star_grading V K^o).
Local Notation mul := (alg_mul A).
Local Notation hb := (alg_bilinear A).

(** Source for [included_forms_commute]: Federer 1.8.2,
    p. 40, supporting signed commutation of homogeneous forms from
    1.4.2, p. 19, expressed in the full unital alternating algebra. *)
Lemma included_forms_commute p q (a : A_m V K^o p) (b : A_m V K^o q) :
  mul (form_include a) (form_include b) =
    (-1 : K)^+(p*q) *: mul (form_include b) (form_include a).
Proof.
exact (@alternating_wedge_anticommutative K h2 V K^o (fun x y : K^o => x*y)
  (scalar_bilinear K) (@mulrC K) p q (form_include a) (form_include b)
  (form_include_homogeneous a) (form_include_homogeneous b)).
Qed.

(** Source for [included_one_form_square]: Federer 1.8.2,
    p. 40, supporting square-zero relation for the individual factors
    in each paired block, by graded anticommutativity and 2 nonzero. *)
Lemma included_one_form_square (a : A_m V K^o 1) :
  mul (form_include a) (form_include a) = 0.
Proof.
exact (@degree_one_square_zero K A G mul
  (@alternating_wedge_anticommutative K h2 V K^o (fun x y : K^o => x*y)
    (scalar_bilinear K) (@mulrC K)) h2 (form_include a)
  (form_include_homogeneous a)).
Qed.

(** Source for [paired_two_form_square]: Federer 1.8.2,
    p. 40, each two-form block alpha wedge beta has square zero. *)
Lemma paired_two_form_square (a b : A_m V K^o 1) :
  mul (form_include (form_wedge h2 (scalar_bilinear K) a b))
    (form_include (form_wedge h2 (scalar_bilinear K) a b)) = 0.
Proof.
rewrite !form_wedge_include.
change (mul (mul (form_include a) (form_include b))
  (mul (form_include a) (form_include b)) = 0).
rewrite -alg_assoc (@alg_assoc K A (form_include b) (form_include a) (form_include b)).
have hc : mul (form_include b) (form_include a) = - mul (form_include a) (form_include b).
  by rewrite (included_forms_commute b a) muln1 expr1 scaleN1r.
rewrite hc (bilNl hb) (bilNr hb).
by rewrite -alg_assoc alg_assoc included_one_form_square !(bil0l hb) oppr0.
Qed.

(** Source for [included_two_forms_commute]: Federer 1.8.2,
    p. 40, every pair of degree-two forms commutes. *)
Lemma included_two_forms_commute (a b : A_m V K^o 2) :
  mul (form_include a) (form_include b) = mul (form_include b) (form_include a).
Proof.
have h := included_forms_commute a b.
have hs : (-1 : K)^+(2*2) = 1 by rewrite !exprS expr0 !mulN1r !opprK.
by rewrite hs scale1r in h.
Qed.

(** Source for [scaled_two_form_block_square]: Federer 1.8.2,
    p. 40, multiplying a paired block by its nonnegative normal-form
    coefficient preserves the square-zero relation (for any scalar). *)
Lemma scaled_two_form_block_square c (a b : A_m V K^o 1) :
  mul (c *: form_include (form_wedge h2 (scalar_bilinear K) a b))
    (c *: form_include (form_wedge h2 (scalar_bilinear K) a b)) = 0.
Proof. by rewrite (bilZl hb) (bilZr hb) paired_two_form_square !scaler0. Qed.
End Blocks.
