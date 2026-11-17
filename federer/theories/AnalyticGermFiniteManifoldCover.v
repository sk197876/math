(** Federer (1969), 3.4.10, p. 337:
    a set germ contained in an analytic germ
    of dimension at most k has a finite
    local cover by analytic manifolds of dimension
    at most k. Apply the already proved
    corrected stratification; empty germs remain explicit. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations
  FiniteCoordinates FiniteDualDimension EuclideanInnerProduct InnerNorm HilbertFormCompactness
  SetGermUP SetGermSealed SetGermLaws SetGermExistence SetGermOrder
  AnalyticVarietyGermUP FiniteAnalyticVarietyUP FiniteAnalyticVarietyBoundary
  GermVanishingSealed AnalyticDepthSealed AnalyticFiniteStratificationUP
  AnalyticFiniteStratificationExistence FunctionalAnalyticManifold AnalyticSubmanifoldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ManifoldCover.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation hB:=(@euclidean_inner_productP R n).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation G0:=(@set_germ_space T 0).
Local Notation germ:=(@set_germ T 0).
Local Notation ideal:=(@AnalyticSetIdeal.value R X NX hNX 0).
Local Notation depth:=(@AnalyticDepth.value R X (@euclidean_inner_product R n)
  hB n (@coordinate_basis R n) (@coordinate_basisP R n)
  (dual_basis (@coordinate_basisP R n))).

(** Source for [analytic_germ_finite_manifold_cover]: the
    local finite cover used in 3.4.10,
    p. 337. All manifold pieces and their
    dimensions are chosen from corrected 3.4.8(11),
    p. 327; no dimension or covering conclusion
    is assumed for the original set. *)
Theorem analytic_germ_finite_manifold_cover (A:set X) (nu:G0) k:
  @is_analytic_variety_germ R X NX hNX 0 nu ->
  set_germ_subset (germ A) nu ->
  (nu=germ set0 \/(depth (ideal nu)<=k)%N) ->
  exists J:finType,exists F:J->set X,exists d:J->nat,
    (forall j,(d j<=k)%N /\@is_euclidean_analytic_submanifold R n (d j) (F j)) /\
    set_germ_subset (germ A) (germ (\bigcup_j F j)).
Proof.
move=>hNu hSub [hEmpty|hDepth].
- exists (Finite.clone unit _),(fun _=>set0),(fun _=>0%N);split.
  + move=>j;split;first exact:leq0n.
    by move=>x.
  + have hUnion:(\bigcup_(j:unit) (set0:set X))=set0.
      apply/seteqP;split;[by move=>x [j _]|by move=>x].
    by rewrite hUnion -hEmpty.
- have [U [H [hU0 [hH hEquation]]]]:=hNu.
  have hBound:(depth (ideal (germ H))<=k)%N by rewrite hEquation.
  have hVoid:=@finite_analytic_variety_domain_empty R X NX hNX U hH.1.
  have [mu [V [F [G [hLaws hInside]]]]]:=@analytic_finite_stratification_exists_at_bound R k n
    U H U set0 hU0 hH hU0 hVoid hBound.
  have [d hD]:=choice (fun i=>analytic_stratification_functional hLaws i).
  exists (Finite.clone 'I_mu _),F,d;split.
  + move=>j;split;first exact:(hD j).1.
    exact:functional_analytic_submanifold_analytic (hD j).2.
  + have hUnion:=analytic_stratification_germ hLaws.
    rewrite (@set_germ_complement_equation T 0 _ _ _ (@SetGerms.laws T 0)) setC0
      (@set_germ_intersection_equation T 0 _ _ _ (@SetGerms.laws T 0)) setIT in hUnion.
    by rewrite -hUnion hEquation.
Qed.
End ManifoldCover.
