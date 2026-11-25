(** Federer (1969), 1.8.1, p. 38: equality between comass and Euclidean norm
    for simple covectors. This direction uses a normalised simple polarity
    preimage. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm InnerNormalization
  InnerPolarity InnerExteriorProducts InnerExterior InnerExteriorPositivity ExteriorNorm ExteriorCovectorInner
  AssociatedSubspace SimplePolarityTransfer SimpleCovectors SimpleElementary SimpleUnitBall
  ComassUP ComassEuclidean ExteriorGrading AlternatingCoordinates AlternatingPairing LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Equality.
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
Local Notation N := (@exterior_norm R h2 V B hB m).
Local Notation D := (@exterior_covector_norm R h2 V B hB n e he m).

(** Source for [inner_exterior_simple]: Federer 1.8.1, p. 38,
    supporting transfer of simplicity through gamma, from its algebra
    extension property in 1.7.5, pp. 31-32. *)
Lemma inner_exterior_simple (x : exterior_power V m) :
  simple x -> simple_covector h2 (inner_exterior_form h2 hB x).
Proof.
move=> [t ->]; rewrite tuple_product inner_exterior_product_covectors.
by exists (fun i => inner_polarity hB (tnth t i)).
Qed.

(** Source for [simple_comass_euclidean]: Federer 1.8.1,
    p. 38, the simple-to-equality implication in the comass norm
    comparison. No attainment or real-completeness theorem is needed. *)
Theorem simple_comass_euclidean (phi : A_m V R^o m) c :
  simple_covector h2 phi -> is_comass h2 hB phi c -> c = D phi.
Proof.
move=> hs hc; have [x [hx hphi]] := @simple_covector_polarity_preimage R h2 V B hB n e he m phi hs.
apply/eqP; rewrite eq_le; apply/andP; split; first exact (@comass_le_euclidean R h2 V B hB n e he m phi c hc).
rewrite -hphi inner_exterior_form_norm.
have [hz|hz] := eqVneq x 0.
- rewrite hz exterior_norm_zero; exact: comass_nonnegative hm hc.
pose y := inner_normalize (@exterior_inner_productP R h2 V B hB m) x.
have hy : simple_unit_ball h2 hB y.
  split; first exact: simple_scale hm hx.
  rewrite /exterior_norm; by rewrite inner_normalize_norm.
have hb := @comass_upper_law R h2 V B hB m phi c hc y hy.
have hp : pairing y phi = N x.
  rewrite -hphi /y /inner_normalize (bilZl (@pairing_bilinear R V R^o m)).
  change ((N x)^-1 * exterior_inner_form h2 hB x x = N x).
  by rewrite -exterior_norm_square expr2 mulrA mulVf ?mul1r // exterior_norm_eq0.
by rewrite hp in hb.
Qed.
End Equality.
