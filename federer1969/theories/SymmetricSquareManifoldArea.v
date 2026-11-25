(** Federer (1969), 3.2.28(4), p. 267:
    the full two-to-one area identity, without any
    global compactness or finite-mass assumption. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import Hom LinearBasis GrassmannAbbreviations EuclideanInnerProduct InnerProductUP InnerNorm InnerMetric
  NormMetricScaleContinuity SymmetricGrading InnerSymmetric InnerSymmetricPositivity
  FiniteInnerChartUP FiniteInnerSubmanifoldUP FiniteInnerSmoothCompactImage
  SubmanifoldCountableCompactCover CompactInvariantExhaustion SymmetricSquareGeometry SymmetricSquareSmooth
  SymmetricSquareCompactArea MeasureExhaustionImageIdentity HausdorffMeasure HausdorffClosedCoverAgreement
  MeasureUP BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [inner_projective_square_manifold_area]:
    H^mu(B)=2 H^mu(TB), Federer 3.2.28(4),
    p. 267, for every antipodal class-k
    submanifold of the finite-dimensional unit sphere,
    k>=1. Increasing invariant compact subsets retain
    both points in every fibre; 3.2.20 on those
    subsets and continuity below prove the unrestricted
    identity, including infinite Hausdorff mass. *)
Theorem inner_projective_square_manifold_area (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) n (b:'I_n->V) (hb:is_basis b)
    mu k (S:set V):
  (1<=k)%N ->is_inner_submanifold B mu k S ->
  (forall x,S x ->inner_norm hB x= 1%R) ->(forall x,S x ->S (-x)%R) ->
  @hausdorff_measure R (inner_metric_space hB) mu S=
    (2:R)%:E* @hausdorff_measure R (inner_metric_space (@symmetric_inner_productP R V B hB 2)) mu
      ((@inner_projective_square R V) @` S).
Proof.
Local Open Scope ring_scope.
move=>hk hMan hUnit hAnti.
pose X:=inner_metric_space hB.
pose Y:=inner_metric_space (@symmetric_inner_productP R V B hB 2).
pose F:=@inner_projective_square R V.
have [N [e [p [hChart hS]]]]:=hMan.
have [K [hK hCover]]:=submanifold_countable_compact_cover hS.
pose E:=inner_metric_space (@euclidean_inner_productP R N).
have hE:continuous (fun z:E=>(e z:X)).
  apply:(@metric_fixed_lipschitz_continuous R E X _ 1%R ler01)=>x y.
  rewrite !inner_metric_distanceE mul1r.
  change (is_true (inner_norm hB (e x-e y)<=inner_norm (@euclidean_inner_productP R N) (x-y))).
  by rewrite -linearB (@finite_inner_chart_norm R V B hB N e p hChart).
have hEK i:@compact [the topologicalType of X] (e @` K i) /\e @` K i `<=` S.
  split; first exact:continuous_compact (continuous_subspaceT hE) (hK i).1.
  move=>x [z hz <-]; have [y hy hyz]:=(hK i).2 z hz.
  by rewrite -hyz (finite_inner_chart_right_inverse hChart).
have hECover:S=\bigcup_i (e @` K i).
  apply/seteqP; split=>x.
  - move=>hx; have hp:(p @` S) (p x) by exists x.
    rewrite hCover in hp; have [i _ hi]:=hp.
    exists i; first exact I; exists (p x); first exact hi.
    exact:(finite_inner_chart_right_inverse hChart x).
  - move=>[i _ hx]; exact:(hEK i).2 x hx.
have hNeg:continuous (fun x:X=>((-x)%R:X)).
  apply:(@metric_fixed_lipschitz_continuous R X X _ 1%R ler01)=>x y.
  rewrite !inner_metric_distanceE mul1r.
  change (is_true (inner_norm hB ((-x)-(-y))<=inner_norm hB (x-y))).
  have he:(-x)-(-y)= -(x-y) by rewrite opprB opprK addrC.
  by rewrite he inner_normN.
have [L [hL [hInc hLCover]]]:=@compact_invariant_exhaustion [the topologicalType of X] S
  (fun x:X=>(-x)%R) (fun i=>e @` K i) hNeg (fun x=>opprK x) hAnti hEK hECover.
have hLF i:@compact [the topologicalType of Y] (F @` L i).
  exact:(@inner_class_map_compact_image R V (symmetric_power V 2) B
    (@symmetric_inner_form R V B hB 2) hB (@symmetric_inner_productP R V B hB 2) F 0%N (L i)
    (@inner_projective_square_smooth R V B hB 0%N) (hL i).1).
have hMeas i:measure_measurable (@hausdorff_measure R X mu) (L i).
  apply:(borel_regular_borel_measurable (@hausdorff_measure_is_measure R X mu)
    (@hausdorff_measure_borel_regular R X mu)).
  apply:closed_borel_set; exact:compact_closed (@metric_hausdorff R X) (hL i).1.
have hFMeas i:measure_measurable (@hausdorff_measure R Y mu) (F @` L i).
  apply:(borel_regular_borel_measurable (@hausdorff_measure_is_measure R Y mu)
    (@hausdorff_measure_borel_regular R Y mu)).
  apply:closed_borel_set; exact:compact_closed (@metric_hausdorff R Y) (hLF i).
apply:(@measure_exhaustion_image_identity R [the choiceType of X] [the choiceType of Y]
  (@hausdorff_measure R X mu) (@hausdorff_measure R Y mu) S F L 2%R
  (@hausdorff_measure_is_measure R X mu) (@hausdorff_measure_is_measure R Y mu)
  ltac:(by rewrite ler0n) hMeas hFMeas hInc hLCover).
move=>i; exact:(@inner_projective_square_compact_area R V B hB n b hb mu k S (L i)
  hk hMan (hL i).2.1 (hL i).1 hUnit (hL i).2.2).
Qed.
