(** Federer (1969), 4.1.14, p. 372: pullbacks of a
    continuous form converge under uniform convergence of the
    original maps and their actual first differentials on K.
    The finite multilinear increment formula of 3.1.1(4),
    p. 210, bounds the differential contribution. Every
    degree, including zero, uses the actual induced comass. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import Hom RealNormUP TensorFamilyUP FamilyUpdate
  MultilinearFamilyAlgebra NormMultilinearRemainder ContinuousMultilinearUP
  ContinuousOperatorUP NormOperatorNormUP EuclideanHomOperator
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingForms AlternatingDual AlternatingFormNormBound
  AlternatingFormUnitBounds CurrentCoefficientNorms CurrentFormInducedNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section CurrentFormPullbackDifferenceBound.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation PN := (@current_form_comass R h2 n m).
Local Notation QN := (@current_form_comass R h2 nu m).
Local Notation hPN := (@current_form_comass_real_norm R h2 n m).
Local Notation hQN := (@current_form_comass_real_norm R h2 nu m).
Local Notation Op := (@euclidean_operator_norm R n nu).
Local Notation pull F := (@A_m_dual R X Y R^o (hom_as_linear F) m).

(** Source for [current_form_linear_pullback_bound]: a
    linear map of operator norm at most c pulls back the
    original comass by at most c^m, as in 1.8.1,
    p. 39, supporting Federer 4.1.14, p. 372.
    The original degree-zero norm and c=0 remain valid. *)
Theorem current_form_linear_pullback_bound (F:Hom X Y) c
    (phi:A_m Y R^o m):
  0<=c->Op F<=c->PN (pull F phi)<=QN phi*c^+m.
Proof.
move=>hc hF.
have hQ:=real_seminorm_nonnegative hQN.1 phi.
apply:(alternating_form_unit_tuple_least hNX (@scalar_absolute_value_norm R)
  (@current_form_comass_is_induced R h2 n m _)
  (mulr_ge0 hQ (exprn_ge0 m hc)))=>t hUnit.
rewrite A_m_dualE.
have hBound:=multilinear_operator_bound
  (@current_form_comass_is_induced R h2 nu m phi)
  [ffun i=>tnth (map_tuple (hom_as_linear F) t) i].
rewrite form_ordered_value_tuple in hBound.
apply:le_trans hBound _;apply:ler_wpM2l;first exact:hQ.
have hProduct:(\prod_(i<m) NY (tnth (map_tuple (hom_as_linear F) t) i))<=c^+m.
  have hConstant:(\prod_(i<m) c)=c^+m by rewrite prodr_const card_ord.
  rewrite -hConstant.
  apply:ler_prod=>i _;apply/andP;split.
  - exact:real_seminorm_nonnegative hNY.1 _.
  - rewrite tnth_map hom_as_linearE.
    have hPoint:=norm_operator_bound
      (continuous_operator_norm_laws (@euclidean_hom_operator_space R n nu) F)
      (tnth t i).
    apply:le_trans hPoint _.
    apply:le_trans (ler_wpM2r
      (real_seminorm_nonnegative hNX.1 (tnth t i)) hF) _.
    have h:=ler_wpM2l hc (hUnit i);by rewrite mulr1 in h.
by under eq_bigr do rewrite ffunE;exact:hProduct.
Qed.

(** Source for [current_form_fixed_pullback_difference_bound]:
    the original multilinear telescoping formula bounds a
    change of first differential, supporting the last sentence
    of Federer 4.1.14, p. 372. The bound has
    no negative exponent and vanishes in degree zero. *)
Theorem current_form_fixed_pullback_difference_bound
    (F G:Hom X Y) c error (phi:A_m Y R^o m):
  1<=c->0<=error->Op F<=c->Op G<=c->Op (F-G)<=error->
  PN (pull F phi-pull G phi)<=m%:R*(QN phi*(error*c^+m)).
Proof.
move=>hc hError hF hG hDifference.
have hQ:=real_seminorm_nonnegative hQN.1 phi.
have hC:0<=c:=le_trans ler01 hc.
have hB:0<=m%:R*(QN phi*(error*c^+m)).
  apply:mulr_ge0;first exact:ler0n.
  exact:mulr_ge0 hQ (mulr_ge0 hError (exprn_ge0 m hC)).
apply:(alternating_form_unit_tuple_least hNX (@scalar_absolute_value_norm R)
  (@current_form_comass_is_induced R h2 n m _) hB)=>t hUnit.
pose aa:=[ffun i=>G (tnth t i)].
pose bb:=[ffun i=>F (tnth t i)].
have hAA:form_ordered_value phi aa=phi (map_tuple (hom_as_linear G) t).
  have hSame:aa=[ffun i=>tnth (map_tuple (hom_as_linear G) t) i].
    by apply/ffunP=>i;rewrite /aa !ffunE tnth_map hom_as_linearE.
  by rewrite hSame form_ordered_value_tuple.
have hBB:form_ordered_value phi bb=phi (map_tuple (hom_as_linear F) t).
  have hSame:bb=[ffun i=>tnth (map_tuple (hom_as_linear F) t) i].
    by apply/ffunP=>i;rewrite /bb !ffunE tnth_map hom_as_linearE.
  by rewrite hSame form_ordered_value_tuple.
change (is_true (`|(pull F phi) t-(pull G phi) t|<=m%:R*(QN phi*(error*c^+m)))).
rewrite !A_m_dualE -hBB -hAA
  (multilinear_family_difference (form_ordered_value_multilinear phi)).
have hCap (A:Hom X Y):Op A<=c->forall i,NY (A (tnth t i))<=c.
  move=>hA i.
  have hPoint:=norm_operator_bound
    (continuous_operator_norm_laws (@euclidean_hom_operator_space R n nu) A)
    (tnth t i).
  apply:le_trans hPoint _.
  apply:le_trans (ler_wpM2r
    (real_seminorm_nonnegative hNX.1 (tnth t i)) hA) _.
  have h:=ler_wpM2l hC (hUnit i);by rewrite mulr1 in h.
have hDiff i:NY (bb i-aa i)<=error.
  rewrite /aa /bb !ffunE.
  have hPoint:=norm_operator_bound
    (continuous_operator_norm_laws (@euclidean_hom_operator_space R n nu) (F-G))
    (tnth t i).
  change (is_true (NY (F (tnth t i)-G (tnth t i))<=
    Op (F-G)*NX (tnth t i))) in hPoint.
  apply:le_trans hPoint _.
  apply:le_trans (ler_wpM2r
    (real_seminorm_nonnegative hNX.1 (tnth t i)) hDifference) _.
  have h:=ler_wpM2l hError (hUnit i);by rewrite mulr1 in h.
have hTerm (i:'I_m):
    `|form_ordered_value phi (family_with (i:=i) (family_prefix_mix aa bb i) (bb i-aa i))|
      <=QN phi*(error*c^+m).
  apply:(@norm_multilinear_single_slot_bound R m (fun _=>Y) R^o
    (fun _=>NY) (fun a:R^o=>`|a|) (fun _=>hNY)
    (form_ordered_value phi)
    (QN phi) hQ (multilinear_operator_bound
      (@current_form_comass_is_induced R h2 nu m phi))
    (family_prefix_mix aa bb i) i (bb i-aa i) c error hc hError (hDiff i)).
  move=>j _;rewrite /family_prefix_mix ffunE.
  case:ifP=>_;rewrite /aa /bb ffunE.
  - exact:(@hCap F hF j).
  - exact:(@hCap G hG j).
apply:le_trans (real_seminorm_sum (@scalar_absolute_value_norm R).1 _) _.
have hSum:(\sum_(i<m)
    `|form_ordered_value phi (family_with (i:=i) (family_prefix_mix aa bb i) (bb i-aa i))|)
      <=\sum_(i<m) QN phi*(error*c^+m).
  apply:ler_sum=>i _;exact:hTerm.
by rewrite sumr_const card_ord -mulr_natl in hSum.
Qed.

(** Source for [current_form_pullback_difference_bound]:
    separate the change of form value from the change
    of first differential, supporting the continuous pullback
    limit in Federer 4.1.14, p. 372. Both
    coefficients have the actual original comass norm. *)
Theorem current_form_pullback_difference_bound
    (F G:Hom X Y) c error (phi psi:A_m Y R^o m):
  1<=c->0<=error->Op F<=c->Op G<=c->Op (F-G)<=error->
  PN (pull F phi-pull G psi)<=QN (phi-psi)*c^+m+
    m%:R*(QN psi*(error*c^+m)).
Proof.
move=>hc hError hF hG hDifference.
have hSplit:pull F phi-pull G psi=
    pull F (phi-psi)+(pull F psi-pull G psi).
  by rewrite linearB addrA subrK.
rewrite hSplit;apply:le_trans (real_seminorm_triangle hPN.1 _ _) _.
apply:lerD.
- exact:current_form_linear_pullback_bound (le_trans ler01 hc) hF.
- exact:current_form_fixed_pullback_difference_bound hc hError hF hG hDifference.
Qed.
End CurrentFormPullbackDifferenceBound.
