(** Federer (1969), 4.1.6, pp. 352–355:
    bounded linear changes of the coefficient space
    commute with the original exterior derivative
    and pullback. These public laws retain arbitrary
    normed coefficients without separability or completeness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP NormDifferentialFiniteCalculus
  Alternating FormCoefficients FormEvaluation
  ContinuousMultilinearUP AlternatingFormNormUP AlternatingFormUnitBounds ExteriorDifferentialUP
  ExteriorDifferentialNormBound ExteriorDerivativeUP DifferentialFormPullbackUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [form_coefficient_change_bound]: changing
    coefficients by a bounded linear map has the
    same bound on the original induced form norms,
    supporting Federer 4.1.6, pp. 352–355. *)
Lemma form_coefficient_change_bound (R:realType) (V W Z:lmodType R)
    (NV:V->R) (NW:W->R) (NZ:Z->R) (hNV:is_real_norm NV) (hNZ:is_real_norm NZ)
    m (P:A_m V W m->R) (Q:A_m V Z m->R)
    (hP:is_alternating_form_norm NV NW P) (hQ:is_alternating_form_norm NV NZ Q)
    (M:Hom W Z) C:
  0<=C->(forall w,NZ (M w)<=C*NW w)->
  forall phi,Q (form_coefficients (hom_as_linear M) phi)<=C*P phi.
Proof.
move=>hC hBound phi.
have hNonnegative:=mulr_ge0 hC (multilinear_operator_nonnegative (hP phi)).
apply:(alternating_form_unit_tuple_least hNV hNZ
  (hQ (form_coefficients (hom_as_linear M) phi)) hNonnegative)=>t hUnit.
rewrite form_coefficientsE.
apply:le_trans (hBound (phi t)) _.
exact:(ler_wpM2l hC (alternating_form_unit_tuple_bound hNV (hP phi) hUnit)).
Qed.

(** Source for [exterior_differential_coefficient_values]:
    the original signed formula commutes with a
    linear coefficient map, supporting Federer
    4.1.6, pp. 352–355, with every degree. *)
Lemma exterior_differential_coefficient_values (K:fieldType) (V W Z:lmodType K) m
    (M:Hom W Z) (L:Hom V (A_m V W m)) (a:A_m V W m.+1):
  is_exterior_differential_value L a->
  is_exterior_differential_value
    (hom_comp (hom_of_linear (@form_coefficients K V W Z (hom_as_linear M) m)) L)
    (form_coefficients (hom_as_linear M) a).
Proof.
move=>hA t; rewrite form_coefficientsE hA !exterior_differential_trace_tuple_values linear_sum.
apply:eq_bigr=>i _.
rewrite linearZ.
change ((-1:K)^+(val i)*:M ((L (tnth t i)) (exterior_omitted_tuple t i))=
  (-1:K)^+(val i)*:(form_coefficients (hom_as_linear M) (L (tnth t i))) (exterior_omitted_tuple t i)).
by rewrite form_coefficientsE.
Qed.

(** Source for [exterior_derivative_change_coefficients]:
    applying a bounded coefficient map to the original
    derivative gives the derivative of the changed
    form, supporting Federer 4.1.6,
    pp. 352–355, on the actual original domain. *)
Theorem exterior_derivative_change_coefficients (R:realType) (V W Z:lmodType R)
    (NV:V->R) (NW:W->R) (NZ:Z->R) (hNV:is_real_norm NV) (hNZ:is_real_norm NZ)
    m (P:A_m V W m->R) (Q:A_m V Z m->R)
    (hP:is_alternating_form_norm NV NW P) (hQ:is_alternating_form_norm NV NZ Q)
    (M:Hom W Z) (U:V->Prop) (phi:V->A_m V W m) a b:
  norm_bounded_linear NW NZ M->has_exterior_derivative NV P U phi a b->
  has_exterior_derivative NV Q U (fun x=>form_coefficients (hom_as_linear M) (phi x)) a
    (form_coefficients (hom_as_linear M) b).
Proof.
move=>[C [hC hBound]] [L [hL hB]].
pose F:=hom_of_linear (@form_coefficients R V W Z (hom_as_linear M) m).
have hF:norm_bounded_linear P Q F.
  exists C; split=>//; exact:(form_coefficient_change_bound hNV hNZ hP hQ hC hBound).
exists (hom_comp F L); split.
- exact:(norm_differential_postcompose hNV hL hF).
- exact:exterior_differential_coefficient_values.
Qed.

(** Source for [original_pullback_change_coefficients]:
    the original A^m Df(a) acts on arguments,
    while the coefficient map acts on values,
    supporting Federer 4.1.6, pp. 354–355. *)
Lemma original_pullback_change_coefficients (K:fieldType) (X Y W Z:lmodType K)
    (f:Hom X Y) (M:Hom W Z) m (phi:A_m Y W m):
  form_coefficients (hom_as_linear M) (A_m_dual (hom_as_linear f) phi)=
    A_m_dual (hom_as_linear f) (form_coefficients (hom_as_linear M) phi).
Proof. apply:form_ext=>t; by rewrite !form_coefficientsE !A_m_dualE ?form_coefficientsE. Qed.
