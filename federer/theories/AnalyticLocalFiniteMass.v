(** Federer (1969), 3.4.10, p. 337:
    transfer the compact finite-mass germ representative
    to the actual original set near its centre.
    Use the proved equality-on-a-neighbourhood law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  SetGermUP SetGermExistence AnalyticVarietyGermUP GermVanishingSealed AnalyticDepthSealed
  AnalyticGermFiniteMassRepresentative HausdorffMeasure MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_origin_local_finite_mass]: the local
    measure bound underlying the first assertion of
    3.4.10, p. 337. Neither the original
    set nor its finite-mass representative is assumed
    measurable; equal germs provide the actual inclusion. *)
Theorem analytic_origin_local_finite_mass (R:realType) n (S:set (R_n R n)) k:
  let hB:=@euclidean_inner_productP R n in
  let NX:=inner_norm hB in
  let hNX:=inner_norm_real_norm hB in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  @is_analytic_variety_germ R (R_n R n) NX hNX 0%R (@set_germ T 0%R S) ->
  (@AnalyticDepth.value R (R_n R n) (@euclidean_inner_product R n) hB n
    (@coordinate_basis R n) (@coordinate_basisP R n) (dual_basis (@coordinate_basisP R n))
    (@AnalyticSetIdeal.value R (R_n R n) NX hNX 0%R (@set_germ T 0%R S))<=k)%N ->
  exists W:set (R_n R n),@open T W /\W 0 /\
    (@hausdorff_measure R (inner_metric_space hB) k (S `&` W)< +oo)%E.
Proof.
move=>hB NX hNX T hAnalytic hBound.
have [A [hCompact [hGerm hMass]]]:=@analytic_germ_finite_mass_representative R n
  (@set_germ T 0%R S) k hAnalytic hBound.
have [W [hW [hW0 hEqual]]]:=(@set_germ_equality_original T 0 A S).1 hGerm.
exists W;split;first exact:hW.
split;first exact:hW0.
apply:(le_lt_trans (@measure_mono R (inner_metric_space hB)
  (@hausdorff_measure R (inner_metric_space hB) k)
  (@hausdorff_measure_is_measure R (inner_metric_space hB) k) (S `&` W) A _) hMass).
move=>x hx;have h:=(hx:(S `&` W) x);by rewrite -hEqual in h;exact:h.1.
Qed.
