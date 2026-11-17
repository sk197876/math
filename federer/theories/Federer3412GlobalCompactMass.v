(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.10, p. 337:
    every compact subset of the original holomorphic
    domain meets S in finite H^(2m) mass,
    where m is its actual global dimension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness InnerNormTopologyAdapters
  SetGermUP HolomorphicVarietyGermUP HolomorphicSetLocalCover
  FiniteHolomorphicVarietyUP FiniteHolomorphicVarietyRelativeClosed
  HolomorphicSetLocalDepth HolomorphicSetDimension BoundedNaturalSupremumUP
  HolomorphicCentreFiniteMass CompactLocalFiniteMass HausdorffMeasure MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_3_4_12_global_compact_mass]: the first
    measure assertion of 3.4.10, p. 337,
    at the exact original global dimension, for
    every compact C contained in U. Local
    irreducible representatives and the existing compact-cover
    theorem supply the bound; no mass or
    measurability conclusion is a premise. *)
Theorem federer_3_4_12_global_compact_mass (R:realType) n (U S C:set (coordinate_space (ComplexScalars.C R) n)) m:
  let hB:=hermitian_real_inner_product (@standard_hermitian_productP R n) in
  let hNX:=complex_norm_real (@holomorphic_coordinate_norm_laws R n) in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  @open T U ->S `<=` U ->
  @is_holomorphic_set_in R (coordinate_space (ComplexScalars.C R) n) (inner_norm hB) hNX U S ->
  @holomorphic_set_dimension R n S=m ->
  @compact (inner_metric_space hB) C ->C `<=` U ->
  (@hausdorff_measure R (inner_metric_space hB) (m+m) (C `&` S)< +oo)%E.
Proof.
move=>hB hNX T hU hSU hHolomorphic hDimension hCompact hCU.
pose X:=coordinate_space (ComplexScalars.C R) n;pose E:=inner_metric_space hB.
rewrite setIC.
apply:(@compact_local_finite_mass R [the topologicalType of E]
  (@hausdorff_measure R E (m+m)) S C (@hausdorff_measure_is_measure R E (m+m)) hCompact)=>a ha.
case:(pselect (S a))=>haS.
- have hBound:(@holomorphic_set_local_depth R n S a<=m)%N.
    rewrite -hDimension;exact:(@bounded_natural_supremum_upper (coordinate_space (ComplexScalars.C R) n) S (@holomorphic_set_local_depth R n S)
      (@holomorphic_set_dimension R n S) (@holomorphic_set_dimension_laws R n S) a haS).
  have [W [hW [hWa hMass]]]:=@holomorphic_centre_local_finite_mass R n S a m
    (hHolomorphic a (hCU a ha)) hBound.
  exists W;split;first exact:(inner_norm_openP hB W).2 hW.
  by split.
- have hCover:=(@holomorphic_set_local_cover_equivalence R X (inner_norm hB) hNX U S).1 hHolomorphic.
  have [V [haV hVariety]]:=hCover a (hCU a ha).
  have [K [hK hEquation]]:=finite_holomorphic_variety_relative_closed_form hVariety.
  have haNotK:~K a.
    move=>haK;apply:haS;have h:(V `&` S) a by rewrite hEquation;split.
    exact:h.2.
  pose W:=V `&` ~` K.
  have hW:@open T W:=openI hVariety.1 (closed_openC hK).
  exists W;split;first exact:(inner_norm_openP hB W).2 hW.
  split;first by split.
  have hEmpty:S `&` W=set0.
    apply/seteqP;split;last by move=>x.
    move=>x [hxS [hxV hxNot]];apply:hxNot.
    have h:(V `&` S) x by split.
    by rewrite hEquation in h;exact:h.2.
  by rewrite hEmpty (measure_empty (@hausdorff_measure_is_measure R E (m+m))) lt0y.
Qed.
