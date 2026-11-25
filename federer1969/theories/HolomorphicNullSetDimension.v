(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.11, p. 338:
    convert the proved global Hausdorff nullity of an
    actual homogeneous majorant to its original global
    holomorphic-set dimension. Reuse 3.4.8(16), p. 337,
    original hull recovery and isometric source translation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import EuclideanSubmanifoldUP FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness FiniteHolomorphicVarietyUP HolomorphicSubmanifoldUP
  SetGermUP SetGermOrder SetGermBoundary HolomorphicGermVanishingSealed HolomorphicDepthSealed
  HolomorphicVarietyGermUP HolomorphicSetLocalDepth HolomorphicSetDimension BoundedNaturalSupremumUP
  HolomorphicIdealVarietyGermSealed HolomorphicIdealVarietyVanishingLaws Federer3412RelativeOpenDimension
  HausdorffMeasure HausdorffIsometricBijection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_null_set_dimension_bound]: the
    original global dimension bound of the homogeneous
    polynomial majorant in 3.4.11, p. 338.
    This supporting implication applies to every actual
    globally holomorphic set, including the empty set. *)
Theorem holomorphic_null_set_dimension_bound (R:realType) n (S:set (coordinate_space (ComplexScalars.C R) n)) d:
  let hB:=hermitian_real_inner_product (@standard_hermitian_productP R n) in
  let NX:=@holomorphic_coordinate_norm R n in
  let hNX:=complex_norm_real (@holomorphic_coordinate_norm_laws R n) in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  @is_holomorphic_set_in R (coordinate_space (ComplexScalars.C R) n) NX hNX setT S ->
  @hausdorff_measure R (inner_metric_space hB) (d+d).+2 S=0%E ->
  (@holomorphic_set_dimension R n S<=d)%N.
Proof.
move=>hB NX hNX T hHolomorphic hNull.
have hLocal a (ha:S a):(@holomorphic_set_local_depth R n S a<=d)%N.
pose X:=coordinate_space (ComplexScalars.C R) n;pose E:=inner_metric_space hB.
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
have hZNull:@hausdorff_measure R E (d+d).+2 Z=0%E.
  by rewrite -hImage (@hausdorff_bijective_isometry_invariance R E E u v hUV hVU hDistance).
have hZHolomorphic:=@holomorphic_set_translated_germ R n S a (hHolomorphic a Logic.I).
have hRelative:@relatively_open_set T Z Z.
  exists setT;split;first exact:openT.
  by rewrite setIT.
have [hI hHullDimension]:=@federer_3_4_12_16 R n Z Z d hZHolomorphic hRelative hZNull.
have hNonempty:=@holomorphic_set_translated_nonempty R n S a ha.
case:hHullDimension=>[hEmpty|hDimension].
- exfalso;apply:hNonempty;apply:set_germ_subset_empty.
  rewrite -hEmpty;exact:(@HolomorphicIdealVarietyVanishingLaws.set_germ_in_variety_of_its_ideal R X NX hNX 0 (@set_germ T 0 Z) hI).
- rewrite (@HolomorphicIdealVarietyVanishingLaws.vanishing_ideal_variety_recovery R X NX hNX 0 (@set_germ T 0 Z) hI) in hDimension.
  exact:hDimension.
case:(pselect (S=set0))=>hEmpty.
- rewrite (@bounded_natural_supremum_empty (coordinate_space (ComplexScalars.C R) n) S (@holomorphic_set_local_depth R n S)
    (@holomorphic_set_dimension R n S) (@holomorphic_set_dimension_laws R n S) hEmpty).
  exact:leq0n.
- have [a [ha hValue]]:=@bounded_natural_supremum_attained (coordinate_space (ComplexScalars.C R) n) S
    (@holomorphic_set_local_depth R n S) (@holomorphic_set_dimension R n S)
    (@holomorphic_set_dimension_laws R n S) hEmpty.
  rewrite -hValue;exact:hLocal a ha.
Qed.
