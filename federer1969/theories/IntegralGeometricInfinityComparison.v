(** Federer (1969), 2.10.6, p. 173:
    every integral-geometric exponent is bounded by the
    infinity exponent. Reuse the complete 3.3.16 result. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric IntegralGeometricMeasure
  StructureIntegralGeometricExponentAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [integral_geometric_below_infinity]:
    direct I_t^m<=I_infinity^m comparison in
    Federer 2.10.6, p. 173, citing
    3.3.16, pp. 299–300. Finite
    original infinity mass gives equality by that
    already proved theorem. Infinite right mass gives
    the inequality by extended-real order. No target
    measurability or finite Hausdorff-mass premise is added. *)
Theorem integral_geometric_below_infinity (R : realType) n m (hMN : (m<=n)%N)
    (t : \bar R) (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  1<=t ->@integral_geometric_measure R n m hMN t A<=
    @integral_geometric_measure R n m hMN +oo A.
Proof.
move=> hT.
case: (ltP (@integral_geometric_measure R n m hMN +oo A) +oo)=> [hFinite|hInfinite].
- by rewrite (@federer_3_3_16_exponent_agreement R n m hMN A t hFinite hT).
- have hTop : @integral_geometric_measure R n m hMN +oo A=+oo.
    apply/eqP; by rewrite eq_le hInfinite leey.
  by rewrite hTop leey.
Qed.
