(** Federer (1969), 3.4.10, p. 338:
    an actual analytic manifold patch inside an
    analytic set gives its global dimension lower
    bound. Reuse the original local/global dimension
    laws, source translation and manifold germ nonnullity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness SetGermUP SetGermOrder SetGermCentreMember
  AnalyticVarietyGermUP AnalyticSetLocalDepth AnalyticSetDimension BoundedNaturalSupremumUP
  AnalyticSubmanifoldUP AnalyticSubmanifoldSourceTranslation AnalyticManifoldGermDimensionLower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_manifold_subset_dimension]: a
    selected actual analytic sheet supplies the lower
    dimension bound for the example cited by
    3.4.10, p. 338. Its original
    centre and its inclusion in S remain
    explicit; the bound follows from previously
    proved local and global laws. *)
Theorem analytic_manifold_subset_dimension (R:realType) n k
    (S Z:set (R_n R n)) (a:R_n R n):
  let X:=R_n R n in
  let hB:=@euclidean_inner_productP R n in
  let NX:=inner_norm hB in
  let hNX:=inner_norm_real_norm hB in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  @is_analytic_variety_germ R X NX hNX a (@set_germ T a S) ->
  @is_euclidean_analytic_submanifold R n k Z ->Z a ->Z `<=` S ->
  (k<=@analytic_set_dimension R n S)%N.
Proof.
move=>X hB NX hNX T hAnalytic hZ haZ hZS.
pose S0:set X:=[set x|S (a+x)].
pose Z0:set X:=[set x|Z (a+x)].
have hS0:=@analytic_set_translated_germ R n S a hAnalytic.
have hZ0:=@analytic_submanifold_source_translation R n k Z (-a) hZ.
have hSame:[set x:X|Z (x-(-a))]=Z0.
  apply:funext=>x;change (Z (x-(-a))=Z (a+x));by rewrite opprK addrC.
rewrite hSame in hZ0.
have hCentre:Z0 0 by change (Z (a+0));rewrite addr0.
have hNonempty:=@set_germ_centre_member_nonempty T 0 Z0 hCentre.
have hSubset:set_germ_subset (@set_germ T 0 Z0) (@set_germ T 0 S0).
  apply:set_germ_subset_from_sets=>x hx;exact:hZS (a+x) hx.
have hLocal:=@analytic_manifold_germ_dimension_lower R n k Z0 (@set_germ T 0 S0)
  hS0 hZ0 hNonempty hSubset.
have hGlobal:=@bounded_natural_supremum_upper X S (@analytic_set_local_depth R n S)
  (@analytic_set_dimension R n S) (@analytic_set_dimension_laws R n S) a (hZS a haZ).
exact:leq_trans hLocal hGlobal.
Qed.
