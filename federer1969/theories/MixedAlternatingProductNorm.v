(** Federer (1969), 4.1.6, pp. 352–353: alternating
    products through a bounded coefficient pairing are
    bounded bilinear operations for the actual induced
    norms. This proves the continuity needed for the
    original product and exterior-derivative rules. The
    earlier shuffle count and unit-factor laws are reused. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals fingroup perm.
From Federer Require Import Hom TensorUP Bilinear RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  NormBoundedBilinearUP ContinuousMultilinearUP AlternatingForms AlternatingFormNormBound AlternatingFormNormUP
  AlternatingFormUnitBounds MixedAlternatingProduct MixedAlternatingShuffle
  AlternatingShuffle Shuffles InversionCount ComassTupleBounds ShuffleCardinalityBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section MixedAlternatingProductNorm.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables V W1 W2 W3:lmodType R.
Variable BV:V->V->R.
Hypothesis hV:is_inner_product BV.
Variables (N1:W1->R) (N2:W2->R) (N3:W3->R).
Hypothesis hN1:is_real_norm N1.
Hypothesis hN2:is_real_norm N2.
Hypothesis hN3:is_real_norm N3.
Variable B:W1->W2->W3.
Hypothesis hB:bilinear B.
Variable C:R.
Hypothesis hC:0<=C.
Hypothesis hBound:forall u v,N3 (B u v)<=C*(N1 u*N2 v).
Variables p q:nat.
Variables (P:A_m V W1 p->R) (Q:A_m V W2 q->R) (T:A_m V W3 (p+q)->R).
Hypothesis hP:is_alternating_form_norm (inner_norm hV) N1 P.
Hypothesis hQ:is_alternating_form_norm (inner_norm hV) N2 Q.
Hypothesis hT:is_alternating_form_norm (inner_norm hV) N3 T.

(** Source for [mixed_alternating_product_norm_bound]: the
    finite coefficient-product bound underlying the
    differentiable alternating multiplication in Federer
    4.1.6, p. 353. Its binomial coefficient comes
    from the earlier 1.8.1 shuffle estimate. *)
Theorem mixed_alternating_product_norm_bound (phi:A_m V W1 p) (psi:A_m V W2 q):
  T (mixed_form_product h2 hB phi psi)<='C(p+q,p)%:R*C*(P phi*Q psi).
Proof.
have hPN:=multilinear_operator_nonnegative (hP phi).
have hQN:=multilinear_operator_nonnegative (hQ psi).
have hCoefficient:0<='C(p+q,p)%:R*C*(P phi*Q psi).
  exact:mulr_ge0 (mulr_ge0 (ler0n _ _) hC) (mulr_ge0 hPN hQN).
apply:(alternating_form_unit_tuple_least (inner_norm_real_norm hV) hN3
  (hT (mixed_form_product h2 hB phi psi)) hCoefficient)=>t hUnit.
rewrite mixed_form_product_shuffle.
apply:le_trans (real_seminorm_sum hN3.1 _) _.
have hTerm (s:Sh p q):N3 (FedererPermutation.index R (val s) *:
    B (phi (shuffle_left_tuple t (val s))) (psi (shuffle_right_tuple t (val s))))<=C*(P phi*Q psi).
  rewrite (real_seminorm_scale hN3.1) /FedererPermutation.index normrX normrN normr1 expr1n mul1r.
  have hLeft:N1 (phi (shuffle_left_tuple t (val s)))<=P phi.
    exact:(alternating_form_unit_tuple_bound (inner_norm_real_norm hV) (hP phi)
      (@shuffle_left_unit_factors R V BV hV p q t (val s) hUnit)).
  have hRight:N2 (psi (shuffle_right_tuple t (val s)))<=Q psi.
    exact:(alternating_form_unit_tuple_bound (inner_norm_real_norm hV) (hQ psi)
      (@shuffle_right_unit_factors R V BV hV p q t (val s) hUnit)).
  have hProduct:=ler_pM
    (real_seminorm_nonnegative hN1.1 (phi (shuffle_left_tuple t (val s))))
    (real_seminorm_nonnegative hN2.1 (psi (shuffle_right_tuple t (val s)))) hLeft hRight.
  exact:(le_trans (hBound _ _) (ler_wpM2l hC hProduct)).

have hSum:(\sum_(s:Sh p q) N3 (FedererPermutation.index R (val s) *:
    B (phi (shuffle_left_tuple t (val s))) (psi (shuffle_right_tuple t (val s)))))<=
    #|{:Sh p q}|%:R*(C*(P phi*Q psi)).
  have hConstant:(\sum_(s:Sh p q) C*(P phi*Q psi))=#|{:Sh p q}|%:R*(C*(P phi*Q psi)).
    by rewrite sumr_const mulr_natl.
  rewrite -hConstant; apply:ler_sum=>s _; exact:hTerm.
have hCard:(#|{:Sh p q}|%:R:R)<='C(p+q,p)%:R.
  by rewrite ler_nat; exact:shuffle_cardinality_bound.
have hEnd:#|{:Sh p q}|%:R*(C*(P phi*Q psi))<='C(p+q,p)%:R*C*(P phi*Q psi).
  rewrite -mulrA; exact:(ler_wpM2r (mulr_ge0 hC (mulr_ge0 hPN hQN)) hCard).
exact:(le_trans hSum hEnd).
Qed.

(** Source for [mixed_alternating_product_bounded_bilinear]:
    the actual form product is continuous bilinear,
    supporting the original Leibniz rule in Federer
    4.1.6, p. 353, without a finite-dimensional
    coefficient-space hypothesis. *)
Theorem mixed_alternating_product_bounded_bilinear:
  norm_bounded_bilinear P Q T (@mixed_form_product R h2 V W1 W2 W3 B hB p q).
Proof.
split; first exact:mixed_form_product_bilinear.
exists ('C(p+q,p)%:R*C); split; first exact:mulr_ge0 (ler0n _ _) hC.
exact:mixed_alternating_product_norm_bound.
Qed.
End MixedAlternatingProductNorm.
