(** Federer (1969), 3.4.12, p. 339, extending 3.4.5, p. 320: the
    original irreducibility union test is equivalent to the
    prime-product property of the actual vanishing ideal.
    Propriety and the empty germ are treated separately. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP RealNormUP NormMetric HolomorphicGermUP HolomorphicGermSealed HolomorphicGermRing
  SetGermUP SetGermSealed SetGermLaws SetGermOrder SetGermBooleanOrder
  CommutativeIdealUP CommutativePrimeProductUP HolomorphicGermVanishingSealed HolomorphicGermVanishingIdeal HolomorphicGermVanishingUnion HolomorphicVarietyGermSeparation
  HolomorphicVarietyGermUP HolomorphicVarietyGermBooleanClosure
  HolomorphicZeroGermSealed HolomorphicZeroGermLaws HolomorphicZeroGermVarieties HolomorphicZeroGermIdeal HolomorphicIrreducibleGermUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Irreducibility.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Hypothesis hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX.
Variable a:X.
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation A:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)].
Local Notation V alpha:=(@is_holomorphic_variety_germ R X NX hNX a alpha).
Local Notation ideal:=(@HolomorphicSetIdeal.value R X NX hNX a).
Local Notation zero:=(@HolomorphicZeroGerm.value R X NX hNX a).
Local Notation join:=(@SetGerms.join T a).
Local Notation meet:=(@SetGerms.meet T a).
Local Notation mul:=(@HolomorphicGerms.mul R X NX hNX a).

(** Source for [holomorphic_irreducible_prime_product_equivalence]:
    the algebraic equivalence printed in 3.4.5,
    p. 320, for its literal union predicate and
    the prime-product condition. The empty germ remains
    admissible on both sides; proper primeness is separate. *)
Theorem holomorphic_irreducible_prime_product_equivalence (alpha:@set_germ_space T a):
  V alpha ->
  (@is_union_irreducible_holomorphic_germ R X NX hNX a alpha <->
    @has_prime_ideal_product_property A (ideal alpha)).
Proof.
move=>hAlpha;split.
- move=>[_ hIrreducible];split;first exact:holomorphic_set_ideal_ring_laws.
  move=>f g hProduct.
  have hContained: set_germ_subset alpha (join (zero f) (zero g)).
    rewrite -holomorphic_zero_germ_product.
    exact:((@holomorphic_zero_germ_ideal_equivalence R X NX hNX a alpha (mul f g)).1 hProduct).
  have hBeta:V (meet (zero f) alpha).
    exact:holomorphic_variety_germ_intersection (holomorphic_zero_germ_is_variety f) hAlpha.
  have hGamma:V (meet (zero g) alpha).
    exact:holomorphic_variety_germ_intersection (holomorphic_zero_germ_is_variety g) hAlpha.
  have hDecomposition:alpha=join (meet (zero f) alpha) (meet (zero g) alpha).
    rewrite -set_germ_distributive set_germ_intersection_commutative.
    exact:esym hContained.
  have [hEqual|hEqual]:=hIrreducible _ _ hBeta hGamma hDecomposition.
  + left;apply/(@holomorphic_zero_germ_ideal_equivalence R X NX hNX a alpha f).
    rewrite hEqual;exact:set_germ_meet_subset_left.
  + right;apply/(@holomorphic_zero_germ_ideal_equivalence R X NX hNX a alpha g).
    rewrite hEqual;exact:set_germ_meet_subset_left.
- move=>[_ hPrime];split;first exact:hAlpha.
  move=>beta gamma hBeta hGamma hDecomposition.
  case:(pselect (alpha=beta))=>[hEqual|hDifferent];first by left.
  case:(pselect (alpha=gamma))=>[hEqual|hDifferent'];first by right.
  have hBetaInside:set_germ_subset beta alpha by rewrite hDecomposition;exact:set_germ_subset_join_left.
  have hGammaInside:set_germ_subset gamma alpha by rewrite hDecomposition;exact:set_germ_subset_join_right.
  have hSeparating delta (hDelta:V delta) (hInside:set_germ_subset delta alpha) (hDistinct:alpha<>delta):
      exists f:A,ideal delta f /\~ideal alpha f.
    apply:contrapT=>hNo.
    have hInclusion:ideal delta `<=` ideal alpha.
      move=>f hf;apply:contrapT=>hn;apply:hNo;by exists f.
    apply:hDistinct.
    apply:set_germ_subset_antisymmetric;last exact:hInside.
    exact:(@holomorphic_variety_germ_ideal_separation R X NX hNX a delta alpha hDelta hInclusion).
  have [f [hf hNotF]]:=hSeparating beta hBeta hBetaInside hDifferent.
  have [g [hg hNotG]]:=hSeparating gamma hGamma hGammaInside hDifferent'.
  have hInBeta:ideal beta (mul f g).
    change (ideal beta ((f:A)*g));rewrite mulrC.
    exact:(@commutative_ideal_mul A (ideal beta) (@holomorphic_set_ideal_ring_laws R X NX hNX a beta) g f hf).
  have hInGamma:ideal gamma (mul f g).
    exact:(@commutative_ideal_mul A (ideal gamma) (@holomorphic_set_ideal_ring_laws R X NX hNX a gamma) f g hg).
  have hProduct:ideal alpha (mul f g).
    rewrite hDecomposition holomorphic_set_ideal_union;by split.
  have [hFactor|hFactor]:=hPrime f g hProduct.
  + exfalso;exact:hNotF hFactor.
  + exfalso;exact:hNotG hFactor.
Qed.
End Irreducibility.
