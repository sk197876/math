(** Federer (1969), 3.4.5, p. 320: the
    original irreducibility union test is equivalent to the
    prime-product property of the actual vanishing ideal.
    Propriety and the empty germ are treated separately. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric AnalyticGermUP AnalyticGermSealed AnalyticGermRing
  SetGermUP SetGermSealed SetGermLaws SetGermOrder SetGermBooleanOrder
  CommutativeIdealUP CommutativePrimeProductUP GermVanishingSealed GermVanishingIdeal
  AnalyticVarietyGermUP AnalyticVarietyGermBooleanClosure
  AnalyticZeroGermSealed AnalyticZeroGermLaws AnalyticZeroGermVarieties AnalyticZeroGermIdeal AnalyticIrreducibleGermUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section Irreducibility.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variable a:X.
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation A:=[the comNzRingType of (@analytic_germ_ring R X NX hNX a)].
Local Notation V alpha:=(@is_analytic_variety_germ R X NX hNX a alpha).
Local Notation ideal:=(@AnalyticSetIdeal.value R X NX hNX a).
Local Notation zero:=(@AnalyticZeroGerm.value R X NX hNX a).
Local Notation join:=(@SetGerms.join T a).
Local Notation meet:=(@SetGerms.meet T a).
Local Notation mul:=(@AnalyticGerms.mul R X NX hNX a).

(** Source for [analytic_irreducible_prime_product_equivalence]:
    the algebraic equivalence printed in 3.4.5,
    p. 320, for its literal union predicate and
    the prime-product condition. The empty germ remains
    admissible on both sides; proper primeness is separate. *)
Theorem analytic_irreducible_prime_product_equivalence (alpha:@set_germ_space T a):
  V alpha ->
  (@is_union_irreducible_analytic_germ R X NX hNX a alpha <->
    @has_prime_ideal_product_property A (ideal alpha)).
Proof.
move=>hAlpha;split.
- move=>[_ hIrreducible];split;first exact:analytic_set_ideal_ring_laws.
  move=>f g hProduct.
  have hContained: set_germ_subset alpha (join (zero f) (zero g)).
    rewrite -analytic_zero_germ_product.
    exact:((@analytic_zero_germ_ideal_equivalence R X NX hNX a alpha (mul f g)).1 hProduct).
  have hBeta:V (meet (zero f) alpha).
    exact:analytic_variety_germ_intersection (analytic_zero_germ_is_variety f) hAlpha.
  have hGamma:V (meet (zero g) alpha).
    exact:analytic_variety_germ_intersection (analytic_zero_germ_is_variety g) hAlpha.
  have hDecomposition:alpha=join (meet (zero f) alpha) (meet (zero g) alpha).
    rewrite -set_germ_distributive set_germ_intersection_commutative.
    exact:esym hContained.
  have [hEqual|hEqual]:=hIrreducible _ _ hBeta hGamma hDecomposition.
  + left;apply/(@analytic_zero_germ_ideal_equivalence R X NX hNX a alpha f).
    rewrite hEqual;exact:set_germ_meet_subset_left.
  + right;apply/(@analytic_zero_germ_ideal_equivalence R X NX hNX a alpha g).
    rewrite hEqual;exact:set_germ_meet_subset_left.
- move=>[_ hPrime];split;first exact:hAlpha.
  move=>beta gamma hBeta hGamma hDecomposition.
  have [f hF]:=@analytic_variety_germ_single_equation R X NX hNX a beta hBeta.
  have [g hG]:=@analytic_variety_germ_single_equation R X NX hNX a gamma hGamma.
  have hProduct:ideal alpha (mul f g).
    apply/(@analytic_zero_germ_ideal_equivalence R X NX hNX a alpha (mul f g)).
    rewrite analytic_zero_germ_product hF hG -hDecomposition.
    exact:set_germ_subset_reflexive.
  have [hFactor|hFactor]:=hPrime f g hProduct.
  + left;apply:set_germ_subset_antisymmetric.
    * rewrite -hF;exact:((@analytic_zero_germ_ideal_equivalence R X NX hNX a alpha f).1 hFactor).
    * rewrite hDecomposition;exact:set_germ_subset_join_left.
  + right;apply:set_germ_subset_antisymmetric.
    * rewrite -hG;exact:((@analytic_zero_germ_ideal_equivalence R X NX hNX a alpha g).1 hFactor).
    * rewrite hDecomposition;exact:set_germ_subset_join_right.
Qed.
End Irreducibility.
