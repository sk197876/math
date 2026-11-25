(** Federer (1969), 4.1.6, pp. 352–355:
    the original coefficient-times-coordinate-form
    operation is bounded bilinear in the actual
    induced norms. It also commutes with the
    original coefficient maps and pullbacks. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom Bilinear RealNormUP Alternating CoefficientCoordinates
  FormCoefficients AlternatingFormNormUP AlternatingFormUnitBounds ContinuousMultilinearUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [form_with_coefficient_tuple]: the original
    vector coefficient multiplies the scalar tuple
    value, Federer 4.1.6, p. 352. *)
Lemma form_with_coefficient_tuple (K:fieldType) (V W:lmodType K) m
    (w:W) (a:A_m V K^o m) (t:m.-tuple V):
  form_with_coefficient w a t=(a t)*:w.
Proof.
by rewrite /form_with_coefficient hom_to_formE hom_with_coefficientE form_to_hom_tuple.
Qed.

(** Source for [form_with_coefficient_bilinear]: the
    original coefficient expansion is bilinear in
    the coefficient and coordinate form,
    Federer 4.1.6, p. 352. *)
Lemma form_with_coefficient_bilinear (K:fieldType) (V W:lmodType K) m:
  bilinear (@form_with_coefficient K V W m).
Proof.
split.
- move=>a c w z; apply:form_ext=>t.
  rewrite form_addE form_scaleE !form_with_coefficient_tuple.
  by rewrite scalerDr !scalerA mulrC.
- move=>w c a b; apply:form_ext=>t.
  rewrite form_addE form_scaleE !form_with_coefficient_tuple form_addE form_scaleE.
  by rewrite scalerDl scalerA.
Qed.

(** Source for [form_with_coefficient_norm_bound]: the
    coefficient-times-form operation has the product
    bound in the actual induced norms,
    supporting Federer 4.1.6, pp. 352–355. *)
Lemma form_with_coefficient_norm_bound (R:realType) (V W:lmodType R)
    (NV:V->R) (NW:W->R) (hNV:is_real_norm NV) (hNW:is_real_norm NW) m
    (P:A_m V R^o m->R) (Q:A_m V W m->R)
    (hP:is_alternating_form_norm NV (fun c:R^o=>`|c|) P)
    (hQ:is_alternating_form_norm NV NW Q) w a:
  Q (form_with_coefficient w a)<=NW w*P a.
Proof.
have hNonnegative:=mulr_ge0 (real_seminorm_nonnegative hNW.1 w) (multilinear_operator_nonnegative (hP a)).
apply:(alternating_form_unit_tuple_least hNV hNW
  (hQ (form_with_coefficient w a)) hNonnegative)=>t hUnit.
rewrite form_with_coefficient_tuple (real_seminorm_scale hNW.1) mulrC.
exact:(ler_wpM2l (real_seminorm_nonnegative hNW.1 w)
  (alternating_form_unit_tuple_bound hNV (hP a) hUnit)).
Qed.

(** Source for [coefficient_form_pullback]: the fixed
    vector coefficient is unchanged when the original
    pullback acts on the arguments,
    Federer 4.1.6, pp. 354–355. *)
Lemma coefficient_form_pullback (K:fieldType) (X Y W:lmodType K)
    (f:Hom X Y) m (w:W) (a:A_m Y K^o m):
  A_m_dual (hom_as_linear f) (form_with_coefficient w a)=
    form_with_coefficient w (A_m_dual (hom_as_linear f) a).
Proof. apply:form_ext=>t; by rewrite A_m_dualE !form_with_coefficient_tuple A_m_dualE. Qed.

(** Source for [coefficient_form_change_values]: a linear
    coefficient map acts on the original vector
    coefficient alone, Federer 4.1.6,
    pp. 352–355. *)
Lemma coefficient_form_change_values (K:fieldType) (V W Z:lmodType K)
    (M:Hom W Z) m (w:W) (a:A_m V K^o m):
  form_coefficients (hom_as_linear M) (form_with_coefficient w a)=
    form_with_coefficient (M w) a.
Proof. apply:form_ext=>t; by rewrite form_coefficientsE !form_with_coefficient_tuple linearZ. Qed.
