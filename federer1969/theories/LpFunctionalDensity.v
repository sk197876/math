(** Federer (1969), 2.5.7, pp. 98–99: consequences of the
    representing-density specification, independent of its existence proof.
    The norm is the corrected closed-ball supremum, erratum p. 2, book p. 98
    line 11. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureAlmostUP FunctionOperatorSeminorm TotalScalarLpUP TotalScalarLpFiniteSeminorm
  TotalScalarPairingValue TotalLpPairingBound LpConjugatePair LpFunctionalDensityUP
  RepresentingDensityNorm RepresentingDensityUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [lp_functional_density_pairing_equivalence]: the integral
    display in Federer 2.5.7, p. 98, identified with the existing sealed
    product value Holder proves summability in the reverse direction. *)
Lemma lp_functional_density_pairing_equivalence (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p q (A : (X -> R) -> R) (k : X -> R) :
  is_lp_conjugate_pair p q ->
  (is_lp_functional_density mu p q A k <-> total_scalar_lp mu q k /\
    forall f, total_scalar_lp mu p f -> A f=total_scalar_pairing mu f k).
Proof.
move=> hpq; split; move=> [hk hrepr]; split=> // f hf.
- exact: esym (@total_scalar_pairing_value_of_integral R X mu f k (A f) (hrepr f hf)).
- rewrite (hrepr f hf); exact: (@total_lp_pairing_specification_and_bound R X mu hm p q f k hpq hf hk).1.
Qed.

(** Source for [lp_functional_density_norm]: exact norm identity for any
    density satisfying Federer 2.5.7, p. 98 The identity itself does not
    require the extra hypotheses needed to prove existence. *)
Theorem lp_functional_density_norm (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p q (A : (X -> R) -> R) (k : X -> R) :
  is_lp_conjugate_pair p q -> is_lp_functional_density mu p q A k ->
  total_scalar_lp_norm mu q k=function_operator_seminorm (total_scalar_lp mu p) A (finite_total_scalar_lp_norm mu p).
Proof.
move=> hpq hk.
have [hmem hrepr] := (proj1 (@lp_functional_density_pairing_equivalence R X mu hm p q A k hpq)) hk.
exact: esym (@representing_density_operator_norm R X mu hm p q A k hpq hmem hrepr).
Qed.

(** Source for [lp_functional_density_almost_unique]: almost uniqueness of
    any two densities satisfying Federer 2.5.7, p. 98 Densities remain
    actual total functions, not quotient classes. *)
Theorem lp_functional_density_almost_unique (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p q (A : (X -> R) -> R) (k l : X -> R) :
  is_lp_conjugate_pair p q -> is_lp_functional_density mu p q A k -> is_lp_functional_density mu p q A l ->
  measure_almost_everywhere mu [set x | k x=l x].
Proof.
move=> hpq hk hl.
have [hkm hkr] := (proj1 (@lp_functional_density_pairing_equivalence R X mu hm p q A k hpq)) hk.
have [hlm hlr] := (proj1 (@lp_functional_density_pairing_equivalence R X mu hm p q A l hpq)) hl.
exact: (@representing_density_almost_unique R X mu hm p q A k l hpq hkm hlm hkr hlr).
Qed.
