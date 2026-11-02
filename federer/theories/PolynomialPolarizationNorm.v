(** Federer (1969), 1.10.5, p. 48: the upper norm comparison from
    polarization, ||phi|| <= m^m ||P||. The polarization identity is 1.9.3,
    p. 43. The estimate below is Federer's norm comparison, not an assertion
    that those. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import RealNormUP SymmetricForms SymmetricPolarizationCoefficients
  SymmetricPolarization HomogeneousPolynomialFunctions PolynomialNorm PolynomialFiniteNormBound
  SymmetricOperatorNormUP SymmetricOperatorNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [polarization_sign_norm]: Federer 1.10.5,
    p. 48, supporting use of 1.9.3: both scalar signs have
    absolute value one. *)
Lemma polarization_sign_norm (R : realFieldType) b : `|polarization_sign R b| = 1.
Proof. by rewrite /polarization_sign; case: b; rewrite ?normrN normr1. Qed.

(** Source for [polarization_weight_norm]: Federer 1.10.5,
    p. 48, supporting use of 1.9.3: the product of the
    scalar signs has absolute value one, even for the empty product. *)
Lemma polarization_weight_norm (R : realFieldType) m (s : polarization_signs m) :
  `|polarization_sign_weight R s| = 1.
Proof.
rewrite /polarization_sign_weight normr_prod.
under eq_bigr do rewrite polarization_sign_norm.
by rewrite prodr_const expr1n.
Qed.

(** Source for [polarization_signed_sum_norm_bound]: Federer
    1.10.5, p. 48, supporting consequence of the triangle
    inequality: a signed sum of m unit-ball vectors has norm at
    most m. This includes m zero. *)
Lemma polarization_signed_sum_norm_bound (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_seminorm N) m (t : m.-tuple V)
    (ht : symmetric_form_unit_tuple N t) (s : polarization_signs m) :
  N (\sum_i polarization_sign R (s i) *: tnth t i) <= m%:R.
Proof.
apply: le_trans (real_seminorm_sum hN _) _.
have he : (\sum_(i<m) (1:R)) = m%:R by rewrite sumr_const card_ord.
rewrite -he; apply: ler_sum=> i _.
by rewrite (real_seminorm_scale hN) polarization_sign_norm mul1r; exact: ht.
Qed.

(** Source for [polynomial_polarization_finite_norm_bound]: Federer
    1.10.5, p. 48, the upper norm comparison under a
    finite bound L on the polynomial norm. The 2^m signed
    evaluations in polarization each contribute at most m^m L. *)
Theorem polynomial_polarization_finite_norm_bound (R : realType) (V W : lmodType R)
    (NV : V -> R) (NW : W -> R) (hV : is_real_norm NV) (hW : is_real_seminorm NW)
    m (f : S_m V W m) L :
  (polynomial_norm (proj1 hV) NW (sform_polynomial_value f)<=L%:E)%E ->
  (symmetric_operator_norm (proj1 hV) NW f <= ((m%:R : R)^+m * L)%:E)%E.
Proof.
move=> hL.
have hL0 : 0<=L.
  have hh := le_trans (polynomial_norm_nonnegative (proj1 hV) hW (sform_polynomial_value f)) hL.
  by rewrite lee_fin in hh.
have hP : is_homogeneous_polynomial m (sform_polynomial_value f) by exists f.
apply: (proj2 (symmetric_operator_norm_bound (proj1 hV) NW f _))=> t ht.
have h2 : (0 < (2%:R : R)^+m) by rewrite exprn_gt0 ?ltr0n.
rewrite -(ler_pM2l h2).
have hp := @sform_polynomial_polarization R V W m (@pchar_num R) f t.
have hh := @real_seminorm_sum R W NW hW (Finite.clone (polarization_signs m) _)
  (fun s => polarization_sign_weight R s *:
    sform_polynomial_value f (\sum_i polarization_sign R (s i) *: tnth t i)).
rewrite hp (real_seminorm_scale hW) normrX normr_nat in hh.
apply: le_trans hh _.
have he : (\sum_(s : polarization_signs m) ((m%:R : R)^+m * L)) =
    (2%:R : R)^+m * ((m%:R : R)^+m * L).
  by rewrite sumr_const card_ffun card_bool card_ord -[LHS]mulr_natl natrX.
rewrite -he; apply: ler_sum=> s _.
rewrite (real_seminorm_scale hW) polarization_weight_norm mul1r.
apply: le_trans (@homogeneous_polynomial_finite_norm_bound R V W NV NW hV hW m
  (sform_polynomial_value f) hP L hL _) _.
apply: (ler_wpM2r hL0).
apply: lerXn2r; first exact: real_seminorm_nonnegative (proj1 hV) _.
- exact: ler0n.
- exact (@polarization_signed_sum_norm_bound R V NV (proj1 hV) m t ht s).
Qed.

(** Source for [polynomial_norm_form_upper_bound]: Federer
    1.10.5, p. 48, the second inequality in the displayed
    comparison, ||phi|| <= m^m ||P||. Infinite polynomial
    norms are retained; the zero-degree convention is 0^0=1. *)
Theorem polynomial_norm_form_upper_bound (R : realType) (V W : lmodType R)
    (NV : V -> R) (NW : W -> R) (hV : is_real_norm NV) (hW : is_real_seminorm NW)
    m (f : S_m V W m) :
  (symmetric_operator_norm (proj1 hV) NW f <=
    ((m%:R : R)^+m)%:E * polynomial_norm (proj1 hV) NW (sform_polynomial_value f))%E.
Proof.
have hn := polynomial_norm_nonnegative (proj1 hV) hW (sform_polynomial_value f).
case hP : (polynomial_norm (proj1 hV) NW (sform_polynomial_value f))=> [L| |] in hn *.
- rewrite -EFinM; apply: (@polynomial_polarization_finite_norm_bound R V W NV NW hV hW m f L).
  by rewrite hP.
- have hpos k : (0 < (k%:R : R)^+k).
    case: k=> [|k]; first by rewrite expr0 ltr01.
    by rewrite exprn_gt0 ?ltr0n.
  have hp := hpos m.
  have hpE : (0 < ((m%:R:R)^+m)%:E)%E by rewrite lte_fin.
  by rewrite muleC (gt0_mulye hpE) leey.
- by rewrite leeNy_eq in hn.
Qed.
