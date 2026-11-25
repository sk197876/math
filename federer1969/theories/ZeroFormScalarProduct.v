(** Federer (1969), 4.1.6, pp. 351–355:
    the degree-zero real product is ordinary scalar
    multiplication. This uses the original unit of
    the alternating algebra, including degree zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions.
From Federer Require Import Hom Bilinear Alternating AlternatingProduct AlternatingUnit ScalarCoefficients.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [original_zero_form_scalar]: the original
    scalar identification A^0(V,R)=R,
    supporting Federer 4.1.6, pp. 351–355. *)
Lemma original_zero_form_scalar (K:fieldType) (V:lmodType K) (c:K):
  @zero_form K V K^o c=c*:@zero_form K V K^o 1.
Proof. apply:form_ext=>t; rewrite form_scaleE !zero_formE.
change (c=c*1); exact:esym (mulr1 c). Qed.

(** Source for [original_zero_form_wedge_scalar]: the
    original degree-zero coefficient product acts
    by scalar multiplication, as used for the
    coordinate coefficients in Federer 4.1.6,
    pp. 352–355. *)
Theorem original_zero_form_wedge_scalar (K:fieldType) (h2:(1+1:K)!=0)
    (V:lmodType K) m (c:K) (a:A_m V K^o m):
  form_wedge h2 (scalar_bilinear K) (@zero_form K V K^o c) a=c*:a.
Proof.
rewrite original_zero_form_scalar (bilZl (@form_wedge_bilinear K h2 V K^o _ (scalar_bilinear K) 0 m)).
congr (_*: _); apply:(can_inj (@form_includeK K V K^o m)).
rewrite (@form_wedge_include K h2 V K^o _ (scalar_bilinear K) 0 m (@zero_form K V K^o 1) a).
exact:(@alternating_unit_left K h2 V K^o _ (scalar_bilinear K) 1 (@mul1r K) (form_include a)).
Qed.
