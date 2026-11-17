(** Federer (1969), 3.4.11, p. 338:
    convert the proved global Hausdorff nullity of an
    actual homogeneous majorant to its original global
    analytic-set dimension. Reuse 3.4.8(16), p. 337,
    original hull recovery and isometric source translation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness FiniteAnalyticVarietyUP EuclideanSubmanifoldUP
  SetGermUP SetGermOrder SetGermBoundary GermVanishingSealed AnalyticDepthSealed
  AnalyticVarietyGermUP AnalyticSetLocalDepth AnalyticSetDimension BoundedNaturalSupremumUP
  IdealVarietyGermSealed IdealVarietyVanishingLaws Federer348RelativeOpenDimension
  HausdorffMeasure HausdorffIsometricBijection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_null_set_dimension_bound]: the
    original global dimension bound of the homogeneous
    polynomial majorant in 3.4.11, p. 338.
    This supporting implication applies to every actual
    globally analytic set, including the empty set. *)
Theorem analytic_null_set_dimension_bound (R:realType) n (S:set (R_n R n)) d:
  let hB:=@euclidean_inner_productP R n in
  let NX:=inner_norm hB in
  let hNX:=inner_norm_real_norm hB in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  @is_analytic_set_in R (R_n R n) NX hNX setT S ->
  @hausdorff_measure R (inner_metric_space hB) d.+1 S=0%E ->
  (@analytic_set_dimension R n S<=d)%N.
Proof.
move=>hB NX hNX T hAnalytic hNull.
have hLocal a (ha:S a):(@analytic_set_local_depth R n S a<=d)%N.
pose X:=R_n R n;pose E:=inner_metric_space hB.
pose Z:set X:=[set x|S (a+x)].
pose u:=fun x:X=>x-a;pose v:=fun x:X=>a+x.
have hUV:cancel u v by move=>x;rewrite /u /v addrC subrK.
have hVU:cancel v u by move=>x;rewrite /u /v addrAC subrr add0r.
have hDistance (x y:E):@mdist R E (u x) (u y)=@mdist R E x y.
  rewrite !inner_metric_distanceE /u.
  have hSub:(x-a)-(y-a)=x-y by rewrite opprD addrAC addrA subrK.
  by rewrite hSub.
have hImage:u @` S=Z.
  apply/seteqP;split.
  - move=>x [y hy <-];change (S (v (u y)));by rewrite hUV.
  - move=>x hx;exists (v x);first exact:hx.
    exact:hVU.
have hZNull:@hausdorff_measure R E d.+1 Z=0%E.
  by rewrite -hImage (@hausdorff_bijective_isometry_invariance R E E u v hUV hVU hDistance).
have hZAnalytic:=@analytic_set_translated_germ R n S a (hAnalytic a Logic.I).
have hRelative:@relatively_open_set T Z Z.
  exists setT;split;first exact:openT.
  by rewrite setIT.
have [hI hHullDimension]:=@federer_3_4_8_16 R n Z Z d hZAnalytic hRelative hZNull.
have hNonempty:=@analytic_set_translated_nonempty R n S a ha.
case:hHullDimension=>[hEmpty|hDimension].
- exfalso;apply:hNonempty;apply:set_germ_subset_empty.
  rewrite -hEmpty;exact:(@set_germ_in_variety_of_its_ideal R X NX hNX 0 (@set_germ T 0 Z) hI).
- rewrite (@vanishing_ideal_variety_recovery R X NX hNX 0 (@set_germ T 0 Z) hI) in hDimension.
  exact:hDimension.
case:(pselect (S=set0))=>hEmpty.
- rewrite (@bounded_natural_supremum_empty (R_n R n) S (@analytic_set_local_depth R n S)
    (@analytic_set_dimension R n S) (@analytic_set_dimension_laws R n S) hEmpty).
  exact:leq0n.
- have [a [ha hValue]]:=@bounded_natural_supremum_attained (R_n R n) S
    (@analytic_set_local_depth R n S) (@analytic_set_dimension R n S)
    (@analytic_set_dimension_laws R n S) hEmpty.
  rewrite -hValue;exact:hLocal a ha.
Qed.
