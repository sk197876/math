(** Federer (1969), 2.10.47, p. 204: the cutoff at sqrt(n) 2^(-i) is bounded
    above by gamma_i. Every eligible grid cube is a nonempty generator at
    that cutoff. Prove this for an arbitrary nonnegative set cost, so the
    Hausdorff cost is a direct instance. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  DyadicCubeGridUP DyadicCubeGrid DyadicCubeGridLaws DyadicScaleBounds
  RefiningCoverContent MetricDiameterUP MetricDiameter HausdorffLengthUP
  MetricScaleEnvelopeUP MetricScaleCutoffCost MetricScaleWeightedBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [dyadic_cube_extended_diameter_bound]: supporting
    sqrt(n) 2^(-j) diameter bound in 2.10.47,
    p. 204, expressed by the abstract diameter laws. *)
Lemma dyadic_cube_extended_diameter_bound (R : realType) n (a : R_n R n) Q :
  is_dyadic_cube_grid a Q -> forall j s,
  extended_metric_diameter (@Q j s)<=(Num.sqrt n%:R/((2^j)%N)%:R)%:E.
Proof.
move=> hQ j s; apply: (metric_diameter_least (extended_metric_diameter_specification (@Q j s))).
- rewrite lee_fin; apply: mulr_ge0; [exact: sqrtr_ge0 | exact: ltW (dyadic_side_positive R j)].
- move=> x y hx hy; rewrite lee_fin; exact: (@dyadic_cube_distance_bound R n a Q hQ j s x y hx hy).
Qed.

(** Source for [dyadic_content_cutoff_lower_bound]: the first
    printed comparison of 2.10.47, p. 204, for
    an arbitrary nonnegative cost. Restriction to the root
    cube is unnecessary for this direction. *)
Theorem dyadic_content_cutoff_lower_bound (R : realType) n (a : R_n R n) Q
    (cost : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R)
    i gamma nu :
  is_dyadic_cube_grid a Q ->
  is_refining_cover_content (dyadic_cube_level Q) cost i gamma ->
  is_metric_scale_envelope (fun S : @nonempty_metric_sets R (inner_metric_space (@euclidean_inner_productP R n))=>val S)
    (fun S=>cost (val S)) (Num.sqrt n%:R/((2^i)%N)%:R)%:E nu ->
  (forall S, S!=set0 -> 0<=cost S) -> forall E, nu E<=gamma E.
Proof.
move=> hQ hg hn hc.
have hm := metric_scale_envelope_is_measure hn (fun S=>hc _ (set_valP S)).
apply: (refining_cover_content_comparison hg hm)=> T [j [hij [s _ <-]]].
have hne := @dyadic_cube_nonempty R n a Q hQ j s.
pose t : @nonempty_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)) :=
  exist _ (@Q j s) (mem_set hne).
apply: (@metric_scale_generator_bound R _ _ _ _ _ nu t hn (hc _ hne)).
apply: le_trans (@dyadic_cube_extended_diameter_bound R n a Q hQ j s) _.
rewrite lee_fin; apply: ler_wpM2l; first exact: sqrtr_ge0.
exact: dyadic_side_antitone hij.
Qed.
