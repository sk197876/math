(** Supporting Federer (1969), 3.4.8(5), p. 328:
    a germ with zero centre value factors as
    the sum of its pointed coordinates times its
    actual analytic radial quotients. The proof uses
    the original Taylor and Leibniz laws. Every
    coordinate representative is a local witness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP LinearBasis FiniteDualDimension
  ContinuousMultilinearUP ContinuousMultilinearSealed AnalyticGermUP AnalyticGermRing
  AnalyticGermRepresentatives AnalyticGermJetsSealed AnalyticGermDirectionalCoefficient
  AnalyticGermDirectionalArithmetic AnalyticGermDirectionalInjective AnalyticRadialQuotientSealed
  AnalyticRadialCoefficientSum PointedFunctionalGermProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_hadamard_factorisation]: a
    finite basis gives an actual coordinate factorisation
    of each original vanishing germ. This expands
    Taylor's formula from 3.1.24, pp. 238–239,
    in the ideal-closedness proof for 3.4.8(5), p. 328.
    No factorisation or vanishing-to-power conclusion
    is supplied as a premise. *)
Theorem analytic_hadamard_factorisation (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) a n (b:'I_n->X) (hb:is_basis b)
  (f:'I_n->@analytic_representative_type R X NX hNX a)
  (alpha:[the comNzRingType of (@analytic_germ_ring R X NX hNX a)]):
  (forall j x,analytic_representative_value (f j) x = dual_basis hb j (x-a)) ->
  @AnalyticGermJets.value R X NX hNX a 0%N alpha = 0 ->
  alpha = \sum_(j<n) (analytic_germ (f j):@analytic_germ_ring R X NX hNX a)*
    (@AnalyticRadialQuotient.map R X NX hNX a alpha (b j)).
Proof.
move=>hF hZero.
apply:(@analytic_germ_directional_coefficients_injective R X NX hNX a)=>k v.
rewrite (@analytic_germ_directional_sum R X NX hNX a k v (Finite.clone 'I_n _)).
case:k=>[|k].
- have hSum:(\sum_(j<n) @analytic_germ_directional_coefficient R X NX hNX a 0%N
      ((analytic_germ (f j):@analytic_germ_ring R X NX hNX a)*
        (@AnalyticRadialQuotient.map R X NX hNX a alpha (b j))) v) = 0.
    apply:big1=>j _.
    exact:(@pointed_functional_product_zero_coefficient R X NX hNX a (dual_basis hb j)
      (f j) (@AnalyticRadialQuotient.map R X NX hNX a alpha (b j)) v (hF j)).
  by rewrite hSum /analytic_germ_directional_coefficient hZero linear0 mulr0.
- have hTerm j:@analytic_germ_directional_coefficient R X NX hNX a k.+1
      ((analytic_germ (f j):@analytic_germ_ring R X NX hNX a)*
        (@AnalyticRadialQuotient.map R X NX hNX a alpha (b j))) v =
      dual_basis hb j v*@analytic_germ_directional_coefficient R X NX hNX a k
        (@AnalyticRadialQuotient.map R X NX hNX a alpha (b j)) v.
    exact:(@pointed_functional_product_successor_coefficient R X NX hNX a (dual_basis hb j)
      (f j) (@AnalyticRadialQuotient.map R X NX hNX a alpha (b j)) k v (hF j)).
  under eq_bigr do rewrite hTerm.
  exact:esym (@analytic_radial_coefficient_basis_sum R X NX hNX a n b hb alpha k v).
Qed.
