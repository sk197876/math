(** Federer (1969), 1.8.1, p. 38: mass lies between the Euclidean norm and
    sqrt(C(n,m)) times that norm. The mass remains specified abstractly. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm InnerNormalization
  InnerExterior InnerExteriorPositivity ExteriorNorm ExteriorCovectorInner
  ExteriorPairingBound ComassUP ComassEuclidean ComassComparison
  MassUP MassBounds ExteriorGrading AlternatingCoordinates AlternatingPairing LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory Num.Def.
Local Open Scope ring_scope.
Section Comparison.
Variable R : rcfType.
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
Local Notation D := (@exterior_covector_norm R h2 V B hB n e he m).
Local Notation C := (Num.sqrt (('C(n,m))%:R : R)).

(** Source for [mass_unit_evaluation_bound]: Federer 1.8.1,
    p. 38, supporting finite upper bound on the second supremum,
    obtained from the binomial comass comparison and Cauchy's inequality. *)
Lemma mass_unit_evaluation_bound x phi : kappa phi <= 1 -> pairing x phi <= C * N x.
Proof.
move=> hphi.
have hh := le_trans (ler_norm (pairing x phi))
  (@exterior_pairing_bound R h2 V B hB n e he m x phi).
have hD : D phi <= C.
  apply: (le_trans (@euclidean_le_comass R h2 V B hB n e he m hm phi (kappa phi) (hk phi))).
  have ht := ler_wpM2l (sqrtr_ge0 (('C(n,m))%:R : R)) hphi; by rewrite mulr1 in ht.
apply: (le_trans hh); rewrite mulrC.
exact: (ler_wpM2r (exterior_norm_nonnegative h2 hB x) hD).
Qed.

(** Source for [mass_le_euclidean_multiple]: Federer 1.8.1,
    p. 38, the upper mass comparison, including C(n,m)=0. *)
Theorem mass_le_euclidean_multiple x d : is_mass kappa x d -> d <= C * N x.
Proof.
move=> hd; apply: (@mass_least_upper_bound R V m kappa x d hd (C * N x)).
exact: mass_unit_evaluation_bound.
Qed.

(** Source for [euclidean_le_mass]: Federer 1.8.1, p. 38,
    the lower mass comparison. A normalised polarity covector has
    comass at most one and evaluates to the Euclidean norm. *)
Theorem euclidean_le_mass x d : is_mass kappa x d -> N x <= d.
Proof.
move=> hd; have [->|hx] := eqVneq x 0.
- rewrite exterior_norm_zero; exact (@mass_nonnegative R h2 V B hB m hm kappa hk x d hd).
pose y := inner_normalize (@exterior_inner_productP R h2 V B hB m) x.
pose phi := inner_exterior_form h2 hB y.
have hD : D phi = 1.
  rewrite /phi inner_exterior_form_norm /exterior_norm /y.
  exact: inner_normalize_norm hx.
have hphi : kappa phi <= 1.
  rewrite -hD; exact (@comass_le_euclidean R h2 V B hB n e he m phi (kappa phi) (hk phi)).
have hh := @mass_upper_law R V m kappa x d hd phi hphi.
have hp : pairing x phi = N x.
  rewrite /phi /y /inner_normalize linearZ (bilZr (@pairing_bilinear R V R^o m)).
  change ((N x)^-1 * exterior_inner_form h2 hB x x = N x).
  by rewrite -exterior_norm_square expr2 mulrA mulVf ?mul1r // exterior_norm_eq0.
by rewrite hp in hh.
Qed.
End Comparison.
