(** Federer (1969), 1.7.6, p. 33: the covector pullback and the exterior map
    have equal operator norms. The proof transports the adjoint along the
    gamma isometries. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP InnerNorm InnerExterior InnerExteriorPositivity
  InnerExteriorIsomorphism ExteriorCovectorInner ExteriorCovectorBasis ExteriorNorm
  ExteriorMaps ExteriorGrading AlternatingDual AlternatingCoordinates LinearBasis FiniteOrdinalBasis
  OperatorNormUP OperatorNorm OperatorNormTransport OperatorDualNorm
  ExteriorAdjoint ExteriorOperatorNorm AdjointUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CovectorNorm.
Variable R : realType.
Hypothesis h2 : (1+1 : R) != 0.
Variables V U : lmodType R.
Variable B : V -> V -> R.
Variable C : U -> U -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hC : is_inner_product C.
Variables n k : nat.
Variable b : 'I_n -> V.
Variable e : 'I_k -> U.
Hypothesis hb : is_basis b.
Hypothesis he : is_basis e.
Variable f : {linear V -> U}.
Variable m : nat.
Local Notation hDV := (@exterior_covector_inner_productP R h2 V B hB n b hb m).
Local Notation hDU := (@exterior_covector_inner_productP R h2 U C hC k e he m).
Local Notation hEV := (@exterior_inner_productP R h2 V B hB m).
Local Notation hEU := (@exterior_inner_productP R h2 U C hC m).

(** Source for [covector_operator_norm]: Federer 1.7.6,
    p. 33, the operator norm of the m-covector pullback, with
    the induced covector products from 1.7.5. *)
Definition covector_operator_norm := linear_operator_norm hDU hDV
  (finite_ordinal_basis (inner_exterior_image_basis h2 hC he m)) (form_pullback_linear f m).

(** Source for [covector_operator_normP]: Federer 1.7.6,
    p. 33, the covector pullback norm obeys the unit-ball norm laws. *)
Theorem covector_operator_normP :
  is_operator_norm hDU hDV (form_pullback_linear f m) covector_operator_norm.
Proof. exact: linear_operator_normP. Qed.

(** Source for [covector_operator_adjoint_norm_equal]: Federer
    1.7.6, p. 33, ||exterior_m adjoint f|| = ||covector_m f||,
    by the gamma diagram and its two isometries. *)
Theorem covector_operator_adjoint_norm_equal (a : {linear U -> V})
    (ha : is_adjoint B C f a) :
  exterior_operator_norm h2 hC hB he a m = covector_operator_norm.
Proof.
apply: (@operator_norm_isometric_transport R (exterior_power U m) (exterior_power V m)
  (A_m U R^o m) (A_m V R^o m)
  (@exterior_inner_form R h2 U C hC m) (@exterior_inner_form R h2 V B hB m)
  (@exterior_covector_inner R h2 U C hC k e he m)
  (@exterior_covector_inner R h2 V B hB n b hb m)
  hEU hEV hDU hDV (exterior_power_map a m) (form_pullback_linear f m)
  (@inner_exterior_form R h2 U C hC m)).
- exact: inner_exterior_form_norm.
- have [g [_ hg]] := @inner_exterior_inverse_exists R h2 U C hC k e he m.
  move=> z; exists (g z); exact: hg.
- move=> x.
  change (exterior_covector_norm h2 hB hb (A_m_dual f (inner_exterior_form h2 hC x)) =
    exterior_norm h2 hB (exterior_power_map a m x)).
  rewrite (@adjoint_inner_exterior_form_diagram R h2 V U B C hB hC f a ha m x).
  exact: inner_exterior_form_norm.
- exact: exterior_operator_normP.
- exact: covector_operator_normP.
Qed.

(** Source for [covector_operator_norm_equal]: Federer 1.7.6,
    p. 33, equality of the exterior-map and covector-pullback norms. *)
Theorem covector_operator_norm_equal (a : {linear U -> V})
    (ha : is_adjoint B C f a) :
  exterior_operator_norm h2 hB hC hb f m = covector_operator_norm.
Proof.
rewrite (@exterior_operator_adjoint_norm_equal R h2 V U B C hB hC n k b e hb he f a ha m).
exact: covector_operator_adjoint_norm_equal.
Qed.
End CovectorNorm.
