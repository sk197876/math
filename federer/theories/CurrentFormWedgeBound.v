(** Federer (1969), 4.1.7, pp. 355–356, 359:
    the original finite covector product has
    a finite comass bound. This supporting
    coefficient estimate reuses the proved finite
    bilinear bound and original alternating product.
    No constant-one estimate is asserted. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP ScalarCoefficients RealNormUP GrassmannAbbreviations
  AlternatingForms AlternatingProduct CurrentCoefficientNorms CurrentCoefficientCompleteness
  NormFiniteBilinearBound NormBoundedBilinearUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_form_wedge_bounded]: a
    finite bound for the actual covector
    wedge supports measurable products in Federer
    4.1.7, pp. 355–356, 359. Both
    degrees may be zero. *)
Theorem current_form_wedge_bounded (R:realType) (h2:(1+1:R)!=0) n k p:
  norm_bounded_bilinear (@current_form_comass R h2 n k) (@current_form_comass R h2 n p)
    (@current_form_comass R h2 n (k+p))
    (@form_wedge R h2 (R_n R n) R^o (fun a b=>a*b) (scalar_bilinear R) k p).
Proof.
have [d [a ha]]:=@current_form_finite_basis R h2 n k.
have [e [b hb]]:=@current_form_finite_basis R h2 n p.
exact:(@norm_finite_bilinear_bounded R (A_m (R_n R n) R^o k) (A_m (R_n R n) R^o p)
  (A_m (R_n R n) R^o (k+p))
  (@current_form_comass R h2 n k) (@current_form_comass R h2 n p) (@current_form_comass R h2 n (k+p))
  (@current_form_comass_real_norm R h2 n k) (@current_form_comass_real_norm R h2 n p)
  (@current_form_comass_real_norm R h2 n (k+p)) d e a b ha hb _
  (@form_wedge_bilinear R h2 (R_n R n) R^o (fun a b=>a*b) (scalar_bilinear R) k p)).
Qed.
