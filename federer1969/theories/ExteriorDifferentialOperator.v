(** Federer (1969), 4.1.6, pp. 352–353: the
    original exterior alternation is a bounded linear
    map on the actual first-operator space. The
    estimate uses exactly the multilinear norms of
    3.1.11 and retains every degree and dimension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom TensorUP RealNormUP NormOperatorNormUP
  ContinuousMultilinearUP ContinuousMultilinearOne
  GrassmannAbbreviations AlternatingForms AlternatingFormNormUP
  ExteriorDifferentialUP ExteriorDifferentialSealed ExteriorDifferentialNormBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section ExteriorDifferentialOperator.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Variable W:lmodType R.
Variables (NV:R_n R n->R) (NW:W->R).
Hypothesis hNV:is_real_norm NV.
Hypothesis hNW:is_real_norm NW.
Variable m:nat.
Variables (P:A_m (R_n R n) W m->R) (Q:A_m (R_n R n) W m.+1->R).
Hypothesis hP:is_alternating_form_norm NV NW P.
Hypothesis hQ:is_alternating_form_norm NV NW Q.
Variable Z:lmodType R.
Variable evaluation:{ffun 'I_1->R_n R n}->Hom Z (A_m (R_n R n) W m).
Variable ZN:Z->R.
Hypothesis hZ:is_continuous_multilinear_space NV P evaluation ZN.
Local Notation J:=(@continuous_multilinear_one_evaluation R (R_n R n)
  (A_m (R_n R n) W m) Z NV P evaluation ZN hZ).

(** Source for [exterior_differential_operator]: apply the
    original exterior alternation to the actual first
    differential, Federer 4.1.6,
    pp. 352–353. *)
Definition exterior_differential_operator:Hom Z (A_m (R_n R n) W m.+1):=
  hom_comp (@exterior_differential_map R h2 n W m) J.

(** Source for [exterior_differential_operator_values]:
    every tuple value is the original signed sum,
    Federer 4.1.6, p. 352. *)
Lemma exterior_differential_operator_values z:
  is_exterior_differential_value (J z) (exterior_differential_operator z).
Proof. exact:ExteriorDifferential.laws. Qed.

(** Source for [exterior_differential_operator_bound]:
    the original alternation has norm at most m+1,
    supporting the original differentiation laws in
    Federer 4.1.6, p. 353. *)
Theorem exterior_differential_operator_bound z:
  Q (exterior_differential_operator z)<=(m.+1)%:R*ZN z.
Proof.
exact:(exterior_differential_value_norm_bound hNV hNW hP hQ
  (exterior_differential_operator_values z)
  (continuous_multilinear_one_norm_laws hZ z)).
Qed.

(** Source for [exterior_differential_operator_bounded]:
    bounded linearity in the original induced norms,
    Federer 4.1.6, pp. 352–353. *)
Theorem exterior_differential_operator_bounded:
  exists C:R,0<=C /\ forall z,Q (exterior_differential_operator z)<=C*ZN z.
Proof. exists (m.+1)%:R; split; first exact:ler0n. exact:exterior_differential_operator_bound. Qed.
End ExteriorDifferentialOperator.
