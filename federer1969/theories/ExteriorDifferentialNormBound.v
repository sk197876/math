(** Federer (1969), 4.1.6, pp. 352–353: the
    original signed exterior-differential formula has
    a finite bound in the exact induced form norms.
    This supplies continuity of the linear alternation
    used in the later differential and pullback laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom Bilinear RealNormUP NormOperatorNormUP ContinuousMultilinearUP
  AlternatingForms AlternatingPairing ExteriorDifferentialUP AlternatingFormNormBound
  AlternatingFormNormUP AlternatingFormUnitBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [exterior_differential_trace_tuple_values]:
    the original v^(i) pairing is the signed value
    on the omitted tuple, Federer 4.1.6,
    p. 352, using the earlier exterior pairing laws. *)
Lemma exterior_differential_trace_tuple_values (K:fieldType) (V W:lmodType K) m
    (L:Hom V (A_m V W m)) (t:m.+1.-tuple V):
  exterior_differential_trace L t=\sum_(i:'I_m.+1)
    (-1:K)^+(val i) *: (L (tnth t i)) (exterior_omitted_tuple t i).
Proof.
apply:eq_bigr=>i _.
by rewrite /exterior_signed_omission (bilZl (@pairing_bilinear K V W m)) pairing_tuple.
Qed.

(** Source for [exterior_differential_value_norm_bound]:
    continuity of the original Hom-to-form map used
    in Federer 4.1.6, pp. 352–353. Each of
    the m+1 actual summands is bounded by the first
    differential norm on unit tuples. No coefficient
    completeness or finite dimension is assumed. *)
Theorem exterior_differential_value_norm_bound (R:realType) (V W:lmodType R)
    (NV:V->R) (NW:W->R) (hNV:is_real_norm NV) (hNW:is_real_norm NW) m
    (P:A_m V W m->R) (Q:A_m V W m.+1->R)
    (hP:is_alternating_form_norm NV NW P) (hQ:is_alternating_form_norm NV NW Q)
    (L:Hom V (A_m V W m)) (a:A_m V W m.+1) c:
  is_exterior_differential_value L a ->is_norm_operator_norm NV P L c ->
  Q a<=(m.+1)%:R*c.
Proof.
move=>hA hL.
have hC:=norm_operator_nonnegative hL.
have hBoundNonnegative:0<=(m.+1)%:R*c:=mulr_ge0 (ler0n _ _) hC.
apply:(alternating_form_unit_tuple_least hNV hNW (hQ a) hBoundNonnegative)=>t hUnit.
rewrite hA exterior_differential_trace_tuple_values.
apply:le_trans (real_seminorm_sum hNW.1 _) _.
have hTerm (i:'I_m.+1):NW ((-1:R)^+(val i) *:
    (L (tnth t i)) (exterior_omitted_tuple t i))<=c.
  rewrite (real_seminorm_scale hNW.1) normrX normrN normr1 expr1n mul1r.
  have hOmitted:forall j,NV (tnth (exterior_omitted_tuple t i) j)<=1.
    by move=>j; rewrite /exterior_omitted_tuple tnth_mktuple; exact:hUnit.
  have hEvaluation:=alternating_form_unit_tuple_bound hNV (hP (L (tnth t i))) hOmitted.
  have hLinear:=norm_operator_bound hL (tnth t i).
  have hScale:=ler_wpM2l hC (hUnit i); rewrite mulr1 in hScale.
  exact:(le_trans hEvaluation (le_trans hLinear hScale)).
have hConstant:(\sum_(i:'I_m.+1) c)=(m.+1)%:R*c.
  by rewrite sumr_const card_ord mulr_natl.
rewrite -hConstant; apply:ler_sum=>i _; exact:hTerm.
Qed.
