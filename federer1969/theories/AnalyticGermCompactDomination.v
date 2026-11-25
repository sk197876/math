(** Federer (1969), 3.4.10, p. 337:
    dominate a local exceptional set by a compact
    finite-mass representative of its smaller-dimensional
    analytic hull. Keep an empty hull separate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  SetGermUP SetGermOrder AnalyticVarietyGermUP GermVanishingSealed AnalyticDepthSealed
  AnalyticGermFiniteMassRepresentative HausdorffMeasure MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_germ_compact_domination]: the local
    exceptional-set mass bound in 3.4.10, p. 337.
    Only a proved smaller-dimensional analytic containing
    germ is supplied. The compact finite-mass set
    is then constructed by the earlier representative
    theorem, with no measurability premise. *)
Theorem analytic_germ_compact_domination (R:realType) n (S:set (R_n R n)) k:
  let hB:=@euclidean_inner_productP R n in
  let NX:=inner_norm hB in
  let hNX:=inner_norm_real_norm hB in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  forall nu:@set_germ_space T 0,
  @is_analytic_variety_germ R (R_n R n) NX hNX 0 nu ->
  set_germ_subset (@set_germ T 0 S) nu ->
  (nu=@set_germ T 0 set0 \/
    (@AnalyticDepth.value R (R_n R n) (@euclidean_inner_product R n) hB n
      (@coordinate_basis R n) (@coordinate_basisP R n) (dual_basis (@coordinate_basisP R n))
      (@AnalyticSetIdeal.value R (R_n R n) NX hNX 0%R nu)<=k)%N) ->
  exists K:set (R_n R n),@compact (inner_metric_space hB) K /\
    set_germ_subset (@set_germ T 0 S) (@set_germ T 0 K) /\
    (@hausdorff_measure R (inner_metric_space hB) k K< +oo)%E.
Proof.
move=>hB NX hNX T nu hNu hContained [hEmpty|hDimension].
- exists set0;split;first exact:compact0.
  split;first by rewrite -hEmpty.
  by rewrite (measure_empty (@hausdorff_measure_is_measure R (inner_metric_space hB) k)) lt0y.
- have [K [hCompact [hGerm hMass]]]:=@analytic_germ_finite_mass_representative R n nu k hNu hDimension.
  exists K;split;first exact:hCompact.
  split;last exact:hMass.
  by rewrite hGerm.
Qed.
