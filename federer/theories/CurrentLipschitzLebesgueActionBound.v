(** Federer (1969), 4.1.25, p. 383: the smooth
    integrands are bounded by a constant times the
    summable mass of the original compact field. The
    dual mass/comass inequality and the pullback bound
    are the preceding laws of 1.8.1 and 4.1.7.
    Zero degree and a zero differential bound remain valid. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric RealFunctionalNormUP
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  ExteriorGrading ExteriorMaps AlternatingForms AlternatingDual AlternatingPairing
  CurrentCoefficientNorms CurrentDualNorm EuclideanHomOperator
  CurrentFormPullbackDifferenceBound CurrentMapDifferential
  CurrentLipschitzLebesgueActionFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section LebesgueActionBound.
Variable R : realType.
Hypothesis h2 : (1+1:R) != 0.
Variables m n k : nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation MX := (@current_vector_mass R h2 m k).
Local Notation PN := (@current_form_comass R h2 m k).
Local Notation QN := (@current_form_comass R h2 n k).
Local Notation hMX := (@current_vector_mass_real_norm R h2 m k).
Local Notation Op := (@euclidean_operator_norm R m n).

(** Source for [current_lipschitz_lebesgue_action_pairing_bound]:
    the original exterior image paired with a test form
    has absolute value at most |xi| M(phi) L^k,
    supplying domination in 4.1.25, p. 383.
    All exterior vectors, including zero and nonsimple
    vectors in an auxiliary degree, obey the same estimate. *)
Lemma current_lipschitz_lebesgue_action_pairing_bound
    (A:Hom X Y) (xi:exterior_power X k) (phi:A_m Y R^o k) (L B:R) :
  0<=L -> Op A<=L -> QN phi<=B ->
  `|pairing (exterior_power_map (hom_as_linear A) k xi) phi| <=
    MX xi*(B*L^+k).
Proof.
move=>hL hA hPhi.
rewrite -A_m_dual_pairing.
have hDual := real_functional_norm_bound
  (@current_mass_pairing_norm R h2 m k xi)
  (A_m_dual (hom_as_linear A) phi).
apply:le_trans hDual _.
apply:ler_wpM2l; first exact:real_seminorm_nonnegative hMX.1 xi.
apply:le_trans (@current_form_linear_pullback_bound R h2 m n k A L phi hL hA) _.
exact:(@ler_wpM2r R (L^+k) (exprn_ge0 k hL) (QN phi) B hPhi).
Qed.

(** Source for [current_lipschitz_lebesgue_action_family_pairing_bound]:
    a single integrable multiple of the original field's
    mass bounds every smooth action in 4.1.25, p. 383.
    This estimate uses the proved family laws only. *)
Lemma current_lipschitz_lebesgue_action_family_pairing_bound
    (f:X->Y) (L B:R) (g:nat->X->Y)
    (hFamily:is_current_lipschitz_lebesgue_action_family f L g)
    (xi:X->exterior_power X k) (phi:Y->A_m Y R^o k) :
  (forall y,QN (phi y)<=B) -> forall i x,
  `|pairing
    (exterior_power_map
      (hom_as_linear (@current_map_differential R m n setT (g i) x)) k (xi x))
    (phi (g i x))| <= MX (xi x)*(B*L^+k).
Proof.
move=>hPhi i x.
exact:(@current_lipschitz_lebesgue_action_pairing_bound
  (@current_map_differential R m n setT (g i) x) (xi x) (phi (g i x)) L B
  (@current_lipschitz_lebesgue_action_family_nonnegative R m n f L g hFamily)
  (@current_lipschitz_lebesgue_action_family_differential_bound R m n f L g hFamily i x)
  (@hPhi (g i x))).
Qed.
End LebesgueActionBound.
