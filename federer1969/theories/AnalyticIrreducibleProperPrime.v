(** Federer (1969), 3.4.5, pp. 320–321:
    proper prime ideals correspond to nonempty irreducible
    variety germs. The literal printed empty-germ union case
    is proved separately instead of being silently discarded. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric AnalyticGermUP AnalyticGermRing SetGermUP SetGermBoundary
  CommutativeIdealUP CommutativePrimeProductUP GermVanishingSealed AnalyticVarietyGermUP
  AnalyticVarietyGermBooleanClosure AnalyticIrreducibleGermUP AnalyticIrreduciblePrimeProduct AnalyticIdealPropriety.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section ProperPrime.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variable a:X.
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation A:=[the comNzRingType of (@analytic_germ_ring R X NX hNX a)].
Local Notation ideal:=(@AnalyticSetIdeal.value R X NX hNX a).

(** Source for [analytic_empty_germ_union_irreducible]: the
    literal printed union predicate includes the empty germ,
    3.4.5, p. 320. This boundary is explicit. *)
Lemma analytic_empty_germ_union_irreducible:
  @is_union_irreducible_analytic_germ R X NX hNX a (@set_germ T a set0).
Proof.
split;first exact:analytic_variety_germ_empty.
move=>beta gamma hBeta hGamma hUnion.
have [hBetaEmpty _]:=set_germ_union_empty_factors (esym hUnion).
by left;symmetry.
Qed.

(** Source for [analytic_irreducible_proper_prime_equivalence]:
    the proper-prime form of the irreducibility assertion,
    3.4.5, p. 320. Requiring the germ to
    be nonempty is precisely equivalent to requiring its
    ideal to be proper; the literal union result is separate. *)
Theorem analytic_irreducible_proper_prime_equivalence (alpha:@set_germ_space T a):
  @is_analytic_variety_germ R X NX hNX a alpha ->
  (@is_nonempty_irreducible_analytic_germ R X NX hNX a alpha <->
    @is_prime_commutative_ideal A (ideal alpha)).
Proof.
move=>hAlpha;split.
- move=>[hIrreducible hNonempty].
  have [hIdeal hProduct]:=(@analytic_irreducible_prime_product_equivalence R X NX hNX a alpha hAlpha).1 hIrreducible.
  split;first exact:hIdeal.
  split;last exact:hProduct.
  move=>hUnit;apply:hNonempty;exact:(analytic_set_ideal_contains_one _).1 hUnit.
- move=>[hIdeal [hProper hProduct]];split.
  + apply/(@analytic_irreducible_prime_product_equivalence R X NX hNX a alpha hAlpha).
    by split.
  + move=>hEmpty;apply:hProper;apply/(analytic_set_ideal_contains_one _);exact:hEmpty.
Qed.
End ProperPrime.
