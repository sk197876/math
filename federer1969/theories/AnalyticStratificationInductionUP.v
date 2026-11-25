(** Federer (1969), corrected 3.4.8(11), pp. 327, 333:
    the induction is simultaneous in every finite
    ambient dimension. The construction may keep each
    actual stratum inside the given analytic representative.
    This existence invariant supplies the local component
    consequence used at the smaller critical depths. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
  EuclideanInnerProduct InnerNorm HilbertFormCompactness SetGermUP FiniteAnalyticVarietyUP
  GermVanishingSealed AnalyticDepthSealed AnalyticFiniteStratificationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_stratification_at_bound]:
    the original induction statement for (11), p. 333,
    strengthened to retain the actual representative and
    allow an upper dimension bound. These are independent
    existence requirements, not an assumed stratification theorem. *)
Definition analytic_stratification_at_bound (R:realType) (m:nat):Prop:=
  forall n (U H U0 S0:set (R_n R n)),
    let NX:=inner_norm (@euclidean_inner_productP R n) in
    let hNX:=inner_norm_real_norm (@euclidean_inner_productP R n) in
    let T:=Topological.clone (real_norm_metric_space hNX) _ in
    let germ:=@set_germ T 0 in
    let depth:=@AnalyticDepth.value R (R_n R n) (@euclidean_inner_product R n)
      (@euclidean_inner_productP R n) n (@coordinate_basis R n) (@coordinate_basisP R n)
      (dual_basis (@coordinate_basisP R n)) in
    U 0 ->@is_finite_analytic_variety R (R_n R n) NX hNX U H ->
    U0 0 ->@is_finite_analytic_variety R (R_n R n) NX hNX U0 S0 ->
    (depth (@AnalyticSetIdeal.value R (R_n R n) NX hNX 0 (germ H))<=m)%N ->
    exists mu,exists V S G:'I_mu->set (R_n R n),
      @is_analytic_finite_stratification R n (germ H) (germ S0) m U0 S0 mu V S G /\
      forall i,S i `<=` H.
