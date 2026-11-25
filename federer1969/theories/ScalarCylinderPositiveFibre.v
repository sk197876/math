(** Federer (1969), 3.2.33, p. 270: Y is empty
    for the original partial-map definition of 3.2.32. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  RealOpenIntervals EuclideanOpenUnitCube PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  HausdorffMeasure RectifiablePositiveFibreCoareaUP ScalarCylinderMapUP ScalarCylinderFibreNull IntervalBumpPrimitiveUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_cylinder_original_positive_fibre_empty]:
    Y=empty in Federer 3.2.33, p. 270, with
    the exact original partial fibres and the complementary
    degree m-mu from 3.2.32. The coordinate arithmetic
    identifies that degree with k+1; all actual fibres
    have already been proved null, including singleton
    fibres when k=0. *)
Theorem scalar_cylinder_original_positive_fibre_empty (R:realType) mu k (a b:nat->R) (psi g:R->R)
    (F:R_n R ((mu+1)+k)->R_n R (mu+1)):
  is_scalar_cylinder_map g F ->is_interval_bump_primitive a b psi g ->
  let f:=partial_function_source_restrict (@euclidean_open_unit_cube R ((mu+1)+k)) (partial_function_total F) in
  positive_partial_fibre_locus ((mu+1)+k) mu f=set0.
Proof.
move=>hF hPrimitive f.
have hDegree:((mu+1+k)-mu)%N=k.+1 by rewrite -addnA addKn add1n.
have hFibre y:partial_function_preimage f [set y]=[set x|euclidean_open_unit_cube x /\F x=y].
  apply/seteqP; split=>x.
  - move=>[z [[hx hz] he]].
    change (F x=z) in hz; change (z=y) in he.
    split; first exact hx; exact:(eq_trans hz he).
  - move=>[hx hEq]; exists y; split; last reflexivity.
    by split.
rewrite /positive_partial_fibre_locus hDegree.
apply/seteqP; split=>y hy; last by case:hy.
change (is_true ((0< @hausdorff_measure R
  (inner_metric_space (@euclidean_inner_productP R ((mu+1)+k))) k.+1
  (partial_function_preimage f [set y]))%E)) in hy.
by rewrite hFibre (scalar_cylinder_fibre_hausdorff_zero hF (interval_primitive_strict hPrimitive) y) ltxx in hy.
Qed.
