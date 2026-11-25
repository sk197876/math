(** Federer (1969), 3.4.10, p. 337:
    express the proved finite local manifold cover
    as an actual finite family of subsets.
    Removing duplicate indices preserves the cover and
    every original dimension bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations
  FiniteCoordinates FiniteDualDimension EuclideanInnerProduct InnerNorm HilbertFormCompactness
  SetGermUP SetGermOrder AnalyticVarietyGermUP GermVanishingSealed AnalyticDepthSealed
  AnalyticSubmanifoldUP AnalyticGermFiniteManifoldCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_germ_manifold_family]: the
    finite local family used for the manifold
    cover in 3.4.10, p. 337.
    This only converts the already proved indexed
    cover into a family of actual sets. *)
Theorem analytic_germ_manifold_family (R:realType) n (A:set (R_n R n))
    (nu:@set_germ_space (Topological.clone
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0) k:
  let X:=R_n R n in
  let hB:=@euclidean_inner_productP R n in
  let NX:=inner_norm hB in
  let hNX:=inner_norm_real_norm hB in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  @is_analytic_variety_germ R X NX hNX 0 nu ->
  set_germ_subset (@set_germ T 0 A) nu ->
  (nu=@set_germ T 0 set0 \/
    (@AnalyticDepth.value R X (@euclidean_inner_product R n) hB n
      (@coordinate_basis R n) (@coordinate_basisP R n) (dual_basis (@coordinate_basisP R n))
      (@AnalyticSetIdeal.value R X NX hNX 0 nu)<=k)%N) ->
  exists F:set (set X),finite_set F /\
    (forall P,F P ->exists d,(d<=k)%N /\@is_euclidean_analytic_submanifold R n d P) /\
    set_germ_subset (@set_germ T 0 A) (@set_germ T 0 (\bigcup_(P in F) P)).
Proof.
move=>X hB NX hNX T hNu hSub hBound.
have [J [P [d [hP hCover]]]]:=@analytic_germ_finite_manifold_cover R n A nu k hNu hSub hBound.
exists (P @` setT);split;first exact:(finite_image P (@finite_finset J setT)).
split.
- move=>Q [j _ <-];exists (d j);exact:hP j.
- have hUnion:(\bigcup_(Q in P @` setT) Q)=\bigcup_j P j.
    apply/seteqP;split.
    + move=>x [Q [j _ <-] hx];by exists j.
    + move=>x [j _ hx];exists (P j);[by exists j|exact:hx].
  by rewrite hUnion.
Qed.
