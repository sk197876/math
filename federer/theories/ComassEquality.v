(** Federer (1969), 1.8.1, p. 38: equality of comass and Euclidean norm
    holds exactly for simple covectors. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP InnerNorm InnerCauchyEquality
  InnerExterior InnerExteriorPositivity ExteriorNorm ExteriorCovectorInner
  ExteriorPairingBound DependentPair SimpleCovectors SimplePolarityTransfer
  SimpleUnitBall SimpleElementary ComassUP ComassBounds ComassAttainment
  ComassSimpleEquality InnerExteriorProducts SimpleAdaptedBasis
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
Local Notation D := (@exterior_covector_norm R h2 V B hB n e he m).
Local Notation N := (@exterior_norm R h2 V B hB m).
Local Notation H := (@exterior_covector_inner_productP R h2 V B hB n e he m).

(** Source for [comass_equality_simple]: Federer 1.8.1,
    p. 38, the equality-to-simplicity implication for comass. The
    maximizing simple vector gives equality in the Cauchy bound. *)
Theorem comass_equality_simple (phi : A_m V R^o m) c :
  is_comass h2 hB phi c -> c = D phi -> simple_covector h2 phi.
Proof.
move=> hc hcD; have [hp|hp] := eqVneq phi 0.
- have [hs hn] := @simple_unit_ball_zero R h2 V B hB m hm.
  have hh := @inner_exterior_simple R h2 V B hB m 0 hs.
  by rewrite linear0 -hp in hh.
have hD : 0 < D phi.
  rewrite lt0r; apply/andP; split; last exact: inner_norm_nonnegative.
  by rewrite /exterior_covector_norm inner_norm_eq0.
have [x [[hx hn] hxp]] := @comass_attained R h2 V B hB n e he m phi c hm hc.
have heval : pairing x phi = D phi by rewrite hxp hcD.
have hbound := @exterior_pairing_bound R h2 V B hB n e he m x phi.
rewrite heval (ger0_norm (ltW hD)) in hbound.
have hNx : N x = 1.
  apply/eqP; rewrite eq_le; apply/andP; split=> //.
  rewrite -(ler_pM2r hD) mul1r; exact hbound.
have heq : `|exterior_covector_inner h2 hB he phi (inner_exterior_form h2 hB x)| =
    D phi * D (inner_exterior_form h2 hB x).
  rewrite (inner_symmetric H) -exterior_pairing_inner heval
    (ger0_norm (ltW hD)) inner_exterior_form_norm hNx mulr1; reflexivity.
have hdep := proj1 (inner_cauchy_equality_dependent H _ _) heq.
have [hz|[a ha]] := proj1 (dependent_pair_cases phi (inner_exterior_form h2 hB x)) hdep.
- have hh := congr1 D hz.
  rewrite inner_exterior_form_norm hNx /exterior_covector_norm inner_norm0 in hh.
  by move: (oner_neq0 R); rewrite hh eqxx.
- rewrite ha.
  exact (@simple_covector_scale R h2 V m (inner_exterior_form h2 hB x) a hm
    (@inner_exterior_simple R h2 V B hB m x hx)).
Qed.

(** Source for [comass_euclidean_iff_simple]: Federer 1.8.1, p. 38, complete
    equality criterion for the first norm comparison *)
Theorem comass_euclidean_iff_simple (phi : A_m V R^o m) c :
  is_comass h2 hB phi c -> (c = D phi <-> simple_covector h2 phi).
Proof.
move=> hc; split; first exact: comass_equality_simple hc.
move=> hs; exact (@simple_comass_euclidean R h2 V B hB n e he m hm phi c hs hc).
Qed.
End Equality.
