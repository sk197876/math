(** Federer (1969), 1.8.1, p. 38: equality of mass and Euclidean norm holds
    exactly for simple multivectors. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP InnerNorm InnerExterior
  InnerExteriorPolarity ExteriorNorm ExteriorCovectorInner
  SimplePolarityTransfer SimpleUnitBall AssociatedSubspace ComassUP
  ComassEuclidean ComassEquality MassUP MassBounds MassEuclidean MassPairingBound
  ExteriorGrading AlternatingCoordinates AlternatingPairing LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Equality.
Variable R : realType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Variable m : nat.
Hypothesis hm : (0 < m)%N.
Variable kappa : A_m V R^o m -> R.
Hypothesis hk : forall phi, is_comass h2 hB phi (kappa phi).
Local Notation N := (@exterior_norm R h2 V B hB m).

(** Source for [simple_mass_euclidean]: Federer 1.8.1,
    p. 38, simple vectors have mass equal to Euclidean norm. *)
Theorem simple_mass_euclidean x d : simple x -> is_mass kappa x d -> d = N x.
Proof.
move=> hx hd; apply/eqP; rewrite eq_le; apply/andP; split.
- exact (@simple_mass_upper R h2 V B hB m hm kappa hk x d hx hd).
- exact (@euclidean_le_mass R h2 V B hB n e he m hm kappa hk x d hd).
Qed.

(** Source for [mass_equality_simple]: Federer 1.8.1,
    p. 38, equality in the lower mass comparison forces simplicity.
    Dual evaluation forces gamma(x) to have comass equal to its
    Euclidean norm, so the comass equality criterion applies. *)
Theorem mass_equality_simple x d : is_mass kappa x d -> d = N x -> simple x.
Proof.
move=> hd hdN; have [hx|hx] := eqVneq x 0.
- rewrite hx; exact: (proj1 (@simple_unit_ball_zero R h2 V B hB m hm)).
have hNx : 0 < N x.
  rewrite lt0r exterior_norm_eq0; apply/andP; split=> //; exact: exterior_norm_nonnegative.
pose phi := inner_exterior_form h2 hB x.
have hupper : kappa phi <= N x.
  have hh := @comass_le_euclidean R h2 V B hB n e he m phi (kappa phi) (hk phi).
  by rewrite /phi inner_exterior_form_norm in hh.
have hlower : N x <= kappa phi.
  have hh := @mass_comass_pairing_bound R h2 V B hB m hm kappa hk x d hd phi.
  change (is_true (`|exterior_inner_form h2 hB x x| <= d * kappa phi)) in hh.
  rewrite -exterior_norm_square (ger0_norm (sqr_ge0 (N x))) hdN expr2
    (ler_pM2l hNx) in hh.
  exact hh.
have heq : kappa phi = exterior_covector_norm h2 hB he phi.
  rewrite /phi inner_exterior_form_norm; apply/eqP; rewrite eq_le.
  exact/andP.
have hs := @comass_equality_simple R h2 V B hB n e he m hm phi (kappa phi) (hk phi) heq.
have [y [hy hgamma]] := @simple_covector_polarity_preimage R h2 V B hB n e he m phi hs.
have hyx : y = x.
  apply: (@inner_exterior_form_injective R h2 V B hB m); exact hgamma.
by rewrite -hyx.
Qed.

(** Source for [mass_euclidean_iff_simple]: Federer 1.8.1,
    p. 38, complete equality criterion for the mass comparison,
    including the zero vector in every positive degree. *)
Theorem mass_euclidean_iff_simple x d : is_mass kappa x d ->
  (d = N x <-> simple x).
Proof.
move=> hd; split; first exact: mass_equality_simple hd.
move=> hx; exact: simple_mass_euclidean hx hd.
Qed.

(** Source for [mass_definite]: Federer 1.8.1, p. 38,
    supporting definiteness of the claimed mass norm, from its
    lower Euclidean comparison. *)
Theorem mass_definite x : is_mass kappa x 0 -> x = 0.
Proof.
move=> hd; have hh := @euclidean_le_mass R h2 V B hB n e he m hm kappa hk x 0 hd.
have hn : N x = 0.
  apply/eqP; rewrite eq_le; apply/andP; split=> //; exact: exterior_norm_nonnegative.
apply/eqP; by rewrite -(exterior_norm_eq0 h2 hB) hn.
Qed.
End Equality.
