(** Federer (1969), 3.4.9, p. 337:
    restrict an original functional analytic stratum to
    every ball whose closed ball lies in its domain.
    The sphere equation supplies an analytic cut; compact
    local component finiteness and the existing relative
    clopen component identity prove the finite count. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness SetGermUP FiniteNormEquivalence NormDifferentialUP NormOpenDomainLaws
  NormBoundedLinearTopology NormAnalyticUP NormAnalyticConstant NormAnalyticOperations
  EuclideanSquaredNormAnalytic FunctionalAnalyticSubmanifoldUP FunctionalAnalyticNonzeroCut
  FiniteAnalyticVarietyUP AnalyticVarietyGermUP FunctionalAnalyticDifference
  AnalyticDifferenceLocalComponents CompactLocalComponentFiniteness RelativeClopenComponentSlice MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section BallComponents.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation hB:=(@euclidean_inner_productP R n).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).

(** Source for [functional_analytic_ball_finite_components]: the finite
    component requirement after replacing Si by its actual
    ball intersection in 3.4.9, p. 337. The
    radius is arbitrary under the printed small-ball
    containment; no regular-value condition is imposed on it. *)
Theorem functional_analytic_ball_finite_components m (U S:set X) r:
  @is_functional_analytic_submanifold R n m U S ->0<r ->
  [set x|NX x<=r] `<=` U ->
  finite_set (@connected_component T (S `&` [set x|NX x<r]) @`
    (S `&` [set x|NX x<r])).
Proof.
move=>hS hR hKU.
pose O:set X:=[set x|NX x<r].
pose K:set X:=[set x|NX x<=r].
pose chi:X->R^o:=fun x=>(NX x)^+2-r^+2.
have hOpen:@open T O.
  have hSame:O=[set x:real_norm_metric_space hNX|@mdist R [the metricType R of real_norm_metric_space hNX] (0:X) x<r].
    apply:funext=>x.
    change (is_true (NX x<r)=is_true (NX (0-x)<r)).
    by rewrite sub0r (real_seminorm_negate hNX.1).
  rewrite hSame;exact:metric_open_ball_open.
have hKCompact:@compact T K.
  have h:=@finite_norm_closed_ball_compact R X n (@coordinate_basis R n)
    (@coordinate_basisP R n) NX hNX 0 r.
  have hEqual:[set y:real_norm_metric_space hNX|NX (y-0)<=r]=K.
    apply:funext=>y;change (is_true (NX (y-0)<=r)=is_true (NX y<=r));by rewrite subr0.
  change (@compact T [set y|NX (y-0)<=r]) in h.
  by rewrite hEqual in h.
have hKClosed:@closed T K.
  exact:(@compact_closed T K (@metric_hausdorff R (real_norm_metric_space hNX)) hKCompact).
have hInterior x (hx:U x):norm_domain_interior NX U x.
  have hU:=hS.2.1;rewrite openE in hU.
  exact:(@norm_domain_interior_neighbourhood R X NX hNX U x).2 (hU x hx).
have hSquare:=@norm_analytic_open_restriction R X R^o NX (fun z:R^o=>`|z|)
  hNX (@scalar_absolute_value_norm R) setT U (fun x=>(NX x)^+2)
  (fun _ _=>Logic.I) hInterior (@euclidean_squared_norm_analytic R n).
have hConstant:=@norm_constant_analytic R X R^o NX (fun z:R^o=>`|z|)
  hNX (@scalar_absolute_value_norm R) U hInterior (r^+2).
have hChi:=norm_analytic_subtract hSquare hConstant.
pose A:set X:=[set x|S x /\chi x<>0].
have hAFunctional:=@functional_analytic_nonzero_cut R n m U S chi hS hChi.
have [H [N [hH [hN hAEquation]]]]:=functional_analytic_difference hAFunctional.
change (A=H `\` N) in hAEquation.
have hFinite:finite_set (@connected_component T A @` (A `&` K)).
  rewrite hAEquation.
  apply:(@compact_local_component_finiteness T (H `\` N) K hKCompact)=>a ha.
  have hHGerm:@is_analytic_variety_germ R X NX hNX a (@set_germ T a H).
    exists U,H;split;first exact:hKU a ha;by split.
  have hNGerm:@is_analytic_variety_germ R X NX hNX a (@set_germ T a N).
    exists U,N;split;first exact:hKU a ha;by split.
  exact:analytic_difference_local_components hHGerm hNGerm.
have hChiNonzero x (hx:O x):chi x<>0.
  have hLess:(NX x)^+2<r^+2.
    by rewrite ltr_sqr ?nnegrE ?inner_norm_nonnegative //;exact:ltW hR.
  move=>hZero;have hEqual:(NX x)^+2=r^+2:=subr0_eq hZero.
  by rewrite hEqual ltxx in hLess.
have hSliceK:S `&` O `<=` K by move=>x [_ hx];exact:ltW hx.
apply:(@relative_clopen_component_slice_finite T (S `&` O) A O K hOpen _ _ hSliceK hFinite).
- apply/seteqP;split.
  + move=>x [hxS hxO];split;last exact:hxO.
    split;[exact:hxS|exact:hChiNonzero x hxO].
  + by move=>x [[hxS _] hxO];split.
- move=>x [[hxS hxChi] hxClosure];split;first exact:hxS.
  have hxK:K x:=hKClosed x (@closureS T (S `&` O) K hSliceK x hxClosure).
  have hDifferent:NX x!=r.
    apply/eqP=>hEqual;apply:hxChi;by rewrite /chi hEqual subrr.
  change (is_true (NX x<r));by rewrite lt_neqAle hDifferent hxK.
Qed.
End BallComponents.
