(** Supporting image containment for Federer (1969), 2.10.5(2), p. 173, and
    its forward reference to 3.2.36, p. 272. Fix a compact convex source and
    a translated section ball. The image under p of a strict contraction of
    that source lies in q(K) for every q in a neighbourhood of p. Correct
    the evaluation error with the proved inverse of q g; its uniform norm
    bound keeps the correction within the contracted section buffer. This
    expands the needed local lifting argument without assuming the full
    joint convex-volume theorem or Steiner's formula. Source context and
    supporting linear and convex references: NearbyProjectionSections.v and
    ConvexSectionContraction.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From mathcomp Require Import lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerNorm
  InnerNormedTopology EuclideanProjectionSpace InnerConvex TensorUP AffineDilation
  NearbyProjectionSections CompactProjectionEvaluationControl ConvexSectionContraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_convex_projected_contraction_neighbourhood]:
    supporting lower control of nearby compact
    convex projection volumes in Federer
    2.10.5(2), p. 173, and 3.2.36, p. 272.
    The supplied section ball is obtained from
    positive projected volume in the preceding
    construction, rather than added to the
    final volume-continuity hypotheses. *)
Theorem compact_convex_projected_contraction_neighbourhood (R : realType) (n m : nat)
    (K : set (inner_metric_space (@euclidean_inner_productP R n)))
    (p : euclidean_projection_space R n m) (b : R_n R n)
    (g : {linear R_n R m -> R_n R n}) (r s : R) :
  compact K -> is_inner_convex K -> cancel g (euclidean_projection_linear p) ->
  0<r -> 0<s -> s<1 ->
  (forall u : inner_metric_space (@euclidean_inner_productP R m),
    mdist (0%R : inner_metric_space (@euclidean_inner_productP R m)) u<r -> K (b+g u)) ->
  exists V : set (euclidean_projection_space R n m), open V /\ V p /\
    forall q, V q -> euclidean_projection_linear p @` ((@affine_dilation R (R_n R n) b s) @` K)
      `<=` euclidean_projection_linear q @` K.
Proof.
move=> hK hc hgp hr hs hs1 hbuffer.
pose P := euclidean_projection_space R n m.
pose X := inner_metric_space (@euclidean_inner_productP R n).
pose Y := inner_metric_space (@euclidean_inner_productP R m).
pose D : set X := (@affine_dilation R (R_n R n) b s) @` K.
have hdcont : continuous (@affine_dilation R (R_n R n) b s : X -> X).
  move=> x; apply: (@continuousD R X X (fun _ => (1-s)*:b) (fun z => s*:z) x).
  - exact: cst_continuous.
  - apply: continuousZ; first exact: cst_continuous.
    exact: cvg_id.
have hD : compact D.
  apply: continuous_compact=> //; apply: continuous_subspaceT; exact hdcont.
have he : 0<(1-s)*r/2 by rewrite divr_gt0 // mulr_gt0 // subr_gt0.
have [V1 [hV1 [hp1 hInv]]] := @nearby_projection_sections_bounded_inverse R n m p g hgp.
have [V2 [hV2 [hp2 hCtrl]]] := @compact_projection_evaluation_control R n m D p ((1-s)*r/2) hD he.
exists (V1 `&` V2); split; first exact: openI hV1 hV2.
split; first by split.
move=> q [hq1 hq2] y [x hx <-].
have [h [hfh [hhf hbound]]] := hInv q hq1.
pose w : Y := h (euclidean_projection_linear p x-euclidean_projection_linear q x).
have hsmall : mdist (0%R:Y) w<(1-s)*r.
  rewrite inner_metric_distanceE sub0r inner_normN /w.
  apply: le_lt_trans (hbound _) _.
  have hb := hCtrl q x hq2 hx; rewrite inner_metric_distanceE in hb.
  lra.
have hKx : K (x+g w).
  have [z hz hzx] := hx; rewrite -hzx /affine_dilation.
  exact: (@convex_contracted_section_buffer R n m K b z g r s w
    hc hz hs hs1 hbuffer hsmall).
exists (x+g w)=> //.
have hcorr : euclidean_projection_linear q (g w)=
    euclidean_projection_linear p x-euclidean_projection_linear q x.
  exact: hhf _.
by rewrite linearD hcorr addrC subrK.
Qed.
