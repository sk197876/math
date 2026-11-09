(** Federer (1969), 3.3.2, pp. 287–288: positive reciprocal
    aperture cutoffs are cofinal. Identify the independently sealed
    original upper limit with the corrected countable-tail expression. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  ExtendedRealBoundsUP ExtendedRealBounds ExtendedRealReciprocalBounds
  StructureConeDensityUP StructureConeDensity StructureLimsupLevels.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_cone_density_reciprocalE]: the
    cofinality step supporting the corrected T_(j,i) formula
    in Federer 3.3.2, p. 288, erratum pp. 5–6,
    book p. 288 lines 1–6. Equality keeps every positive
    real aperture cutoff in the original specification. *)
Theorem structure_cone_density_reciprocalE (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))) (delta:R) z:
  structure_cone_density hmn phi A delta z=
    structure_tail_upper_limit (structure_cone_cost hmn phi A) delta z.
Proof.
have h:=@structure_cone_density_specification R n m hmn phi A delta z.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply:extended_real_inf_greatest=>q [i ->].
  apply:(h.1 ((i.+1)%:R:R)^-1).
  + by rewrite invr_gt0 ltr0n.
  + constructor; [exact:extended_real_sup_upper|exact:extended_real_sup_least].
- apply:h.2=>t q ht hq.
  have [i hSmall]:=positive_reciprocal_nat_small ht.
  have hBound:(structure_tail_upper_limit (structure_cone_cost hmn phi A) delta z<=
      structure_tail_supremum (structure_cone_cost hmn phi A) delta i z)%E.
    apply:extended_real_inf_lower; by exists i.
  apply:le_trans hBound _; apply:extended_real_sup_least=>v [r [s [hr [hs ->]]]].
  apply:(extended_real_supremum_upper hq).
  exists r,s; split=>//; split=>//; apply/andP; split; first exact:(andP hs).1.
  exact:(lt_trans (andP hs).2 hSmall).
Qed.
