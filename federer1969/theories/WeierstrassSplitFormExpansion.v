(** Federer (1969), 3.4.6, pp. 322–323: the
    original split Taylor coefficients are recovered uniquely
    from finite homogeneous polynomial expansions on each line. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom SymmetricAlgebra SymmetricForms PolynomialTaylorTerms
  HomogeneousPolynomialFunctions FiniteHornerCoefficientEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [weierstrass_split_contraction_transpose]:
    the two divided-power factors in the original mixed
    coefficient commute, supporting the binomial computation
    in 3.4.6, p. 322. *)
Lemma weierstrass_split_contraction_transpose (R:realType) (X:lmodType R)
    m i (F:S_m X R^o m) v z:
  (i<=m)%N ->
  sform_polynomial_value (symmetric_taylor_term i F z) v=
    sform_polynomial_value (symmetric_taylor_term (m-i)%N F v) z.
Proof.
move=>hi.
rewrite !symmetric_taylor_term_value subKn //.
by rewrite symmetric_product_commute.
Qed.

(** Source for [weierstrass_split_form_line_expansion]: the
    actual mixed homogeneous coefficients give the finite
    line polynomial of the original Taylor term,
    3.4.6, pp. 322–323. Factorial normalization
    and degree-zero terms are retained. *)
Lemma weierstrass_split_form_line_expansion (R:realType) (X:lmodType R)
    m (F:S_m X R^o m) v z (t:R):
  sform_polynomial_value F (t*:v+z)=
    \sum_(i<m.+1) t^+i*sform_polynomial_value (symmetric_taylor_term (m-i)%N F v) z.
Proof.
rewrite addrC (homogeneous_polynomial_taylor (@pchar_num R)).
apply:eq_bigr=>i _.
rewrite sform_polynomial_scale_argument.
change (t^+i*sform_polynomial_value (symmetric_taylor_term i F z) v=
  t^+i*sform_polynomial_value (symmetric_taylor_term (m-i)%N F v) z).
have hi:(i<=m)%N by have:=ltn_ord i;rewrite ltnS.
by rewrite (weierstrass_split_contraction_transpose F v z hi).
Qed.

(** Source for [weierstrass_split_form_coefficient_unique]:
    the actual line values uniquely determine every original
    mixed coefficient, supporting the double-sequence uniqueness
    assertion in 3.4.6, p. 323. The
    proof uses the project's finite root-count theorem. *)
Theorem weierstrass_split_form_coefficient_unique (R:realType) (X:lmodType R)
    m (F:S_m X R^o m) v z (c:nat->R):
  (forall t:R,sform_polynomial_value F (t*:v+z)=\sum_(i<m.+1) t^+i*c i) ->
  forall i,(i<=m)%N ->c i=
    sform_polynomial_value (symmetric_taylor_term (m-i)%N F v) z.
Proof.
move=>hValues i hi.
have hPolynomials (t:R):(\sum_(s<m.+1) t^+s*:(c s:R^o))=
    \sum_(s<m.+1) t^+s*:
      sform_polynomial_value (symmetric_taylor_term (m-s)%N F v) z.
  transitivity (sform_polynomial_value F (t*:v+z));first exact:esym (hValues t).
  exact:weierstrass_split_form_line_expansion.
exact:(@finite_power_coefficients_equal R (@pchar_num R) R^o m.+1 c
  (fun s=>sform_polynomial_value (symmetric_taylor_term (m-s)%N F v) z)
  hPolynomials i hi).
Qed.
