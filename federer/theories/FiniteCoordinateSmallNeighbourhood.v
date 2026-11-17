(** Federer (1969), 3.4.8(11), p. 333:
    finitely many coordinate-axis bounds hold
    on one neighbourhood of zero. Reuse
    the original finite-dimensional linear bounds and
    the norm-domain neighbourhood criterion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra.
From Federer Require Import Hom RealNormUP NormMetric LinearBasis NormDifferentialUP NormFiniteLinearBound
  NormBoundedLinearTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_coordinate_small_neighbourhood]:
    all original coordinates are small
    on a common neighbourhood, supporting
    the m=0 axis argument of
    3.4.8(11), p. 333. *)
Theorem finite_coordinate_small_neighbourhood (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) n (e:'I_n->X) (he:is_basis e)
    (omega:'I_n->Hom X R^o) (d:'I_n->R):
  (forall j,0<d j) ->
  nbhs (0:real_norm_metric_space hNX) [set x|forall j,`|omega j x|<d j].
Proof.
move=>hPositive.
have hEach j:nbhs (0:real_norm_metric_space hNX) [set x | `|omega j x|<d j].
  have [C [hC hBound]]:=@norm_finite_linear_bounded R X R^o NX (fun z:R^o=>`|z|) hNX
    (@scalar_absolute_value_norm R) n e he (omega j).
  have hCOne:0<C+1 by lra.
  have hRadius:0<d j/(C+1) by rewrite divr_gt0 //;exact:hPositive j.
  apply:(proj2 (metricType_numDomainType.nbhs_mdistP (0:real_norm_metric_space hNX) _)).
  exists (d j/(C+1));first exact:hRadius.
  move=>x hx.
  change (is_true (NX (0-x)<d j/(C+1))) in hx.
  rewrite sub0r (real_seminorm_negate hNX.1) in hx.
  have hProduct:NX x*(C+1)<d j by move:hx;rewrite ltr_pdivlMr.
  apply:le_lt_trans (hBound x) _.
  have hNorm:=real_seminorm_nonnegative hNX.1 x;nra.
have hAll:=@filter_forall (real_norm_metric_space hNX) 'I_n
  (fun j x=>is_true (`|omega j x|<d j)) (nbhs (0:real_norm_metric_space hNX)) (nbhs_filter (0:real_norm_metric_space hNX)) hEach.
apply:(filterS _ hAll)=>x hx;exact:hx.
Qed.
