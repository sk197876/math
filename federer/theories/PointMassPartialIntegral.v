(** Federer (1969), 4.1.11, p. 365: the point-current
    specialization of the literal repeated mass integral.
    Reuse point evaluation from 2.5.15, p. 108, almost
    invariance from 2.4.3(2), p. 81, and the extended
    nonnegative constant integral from 2.4.10, p. 85. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialZeroExtension
  MeasureUP MeasureAlmostUP MeasureIntegralUP MeasureIntegralAlmostEquality MeasureIntegralGraphEquivalence
  MeasureSubsetIntegral MeasureSubsetConstantIntegral PointMassMeasure PointMassRegularity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [point_mass_almost_iff]: an assertion holds
    almost everywhere for the original unit point mass
    exactly when it holds at its point, supporting Federer
    4.1.11, p. 365, by 2.3.1, p. 72. *)
Theorem point_mass_almost_iff (R:realType) (X:choiceType) (c:X) (P:set X):
  measure_almost_everywhere (point_mass R c) P<->P c.
Proof.
rewrite /measure_almost_everywhere;split.
- move=>h;apply:contrapT=>hNot.
  rewrite (@point_mass_in R X c (~` P) hNot) in h.
  have hNe:(1 : \bar R)!=0 by rewrite eqe oner_eq0.
  by rewrite h eqxx in hNe.
- move=>h;apply:point_mass_out=>hNot;exact:hNot h.
Qed.

(** Source for [point_mass_nonnegative_partial_integral]:
    a nonnegative original partial value at the mass point
    is its integral, supporting the point-cone mass estimate
    in Federer 4.1.11, p. 365. The value may be infinite;
    no values outside the original domain are supplied. *)
Theorem point_mass_nonnegative_partial_integral (R:realType) (X:choiceType) (c:X)
    (f:partial_function X (extended_real_line R)) (a : \bar R):
  0<=a->partial_function_graph f c a->is_measure_integral (point_mass R c) f a.
Proof.
move=>ha hGraph.
pose mu:=point_mass R c.
pose hm:=point_mass_is_measure R c.
pose k:=partial_function_total (fun _:X=>(a:extended_real_line R)).
have hSubset:=@measure_nonnegative_constant_subset_integral R X mu setT a hm
  (point_mass_every_set_measurable R c setT) ha.
rewrite /mu (@point_mass_in R X c setT Logic.I) mule1 in hSubset.
have hConst:is_measure_integral mu k a.
  apply:(measure_integral_graph_equivalent _ hSubset)=>x v.
  exact:(@partial_function_zero_extension_on X (extended_real_line R) 0 setT k x v Logic.I).
apply:(measure_integral_almost_equal hm hConst).
apply:(@point_mass_almost_iff R X c _).2.
exists a;split;[by []|exact:hGraph].
Qed.
