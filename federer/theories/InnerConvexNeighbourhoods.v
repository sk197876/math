(** Supporting convex geometry for Federer (1969), 2.10.4(2), p. 172:
    closure preserves convexity, and metric open thickenings of convex sets
    are convex. These expand the open/closed generator comparison, using
    only the given vector operations, norm laws and topology. They hold in
    arbitrary inner-product spaces; finite dimension is used separately for
    compactness. Source context and the absence of a corresponding. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import InnerProductUP InnerNorm InnerNormInequalities InnerMetric
  InnerNormedTopology InnerConvex MetricOpenThickening.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inner_affine_variable_continuous]: supporting
    continuity of a fixed affine variable in the
    convex generator comparison of Federer 2.10.4(2),
    p. 172, with the norm topology of 1.7.1,
    p. 28. No external affine-map theorem is used. *)
Lemma inner_affine_variable_continuous (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (c : R)
    (y : inner_metric_space hB) :
  continuous (fun x : inner_metric_space hB => (c*:x+y : inner_metric_space hB)).
Proof.
move=> x; apply: continuousD; last exact: cst_continuous.
apply: continuousZ; first exact: cst_continuous.
exact: cvg_id.
Qed.

(** Source for [inner_convex_closure]: supporting closed
    convex replacement in Federer 2.10.4(2), p. 172.
    Fix each endpoint in turn and pass through its
    closure using a continuous affine map and a closed
    target. Empty sets are included. *)
Theorem inner_convex_closure (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (A : set V) :
  is_inner_convex A -> @is_inner_convex R V (@closure (inner_metric_space hB) A).
Proof.
move=> hA x y hx hy t ht0 ht1.
pose C : set (inner_metric_space hB) := @closure (inner_metric_space hB) A.
have hC : closed C := @closed_closure (inner_metric_space hB) A.
have hfirst (b : inner_metric_space hB) : A b -> C ((1-t)*:x+t*:b).
  move=> hb.
  pose f (a : inner_metric_space hB) := ((1-t)*:a+t*:b : inner_metric_space hB).
  have hf : continuous f := @inner_affine_variable_continuous R V B hB (1-t) (t*:b).
  have hc := (@continuous_closedP (inner_metric_space hB) (inner_metric_space hB) f).1 hf C hC.
  have hs : A `<=` f @^-1` C.
    move=> a ha; apply: (@subset_closure (inner_metric_space hB) A).
    exact: hA a b ha hb t ht0 ht1.
  exact (hc _ (@closureS (inner_metric_space hB) A _ hs x hx)).
pose g (b : inner_metric_space hB) := (t*:b+(1-t)*:x : inner_metric_space hB).
have hg : continuous g := @inner_affine_variable_continuous R V B hB t ((1-t)*:x).
have hc := (@continuous_closedP (inner_metric_space hB) (inner_metric_space hB) g).1 hg C hC.
have hs : A `<=` g @^-1` C.
  move=> b hb; change (C (t*:b+(1-t)*:x)).
  rewrite addrC; apply: hfirst; exact hb.
have hh : C (t*:y+(1-t)*:x) := hc _ (@closureS (inner_metric_space hB) A _ hs y hy).
rewrite addrC in hh; exact hh.
Qed.

(** Source for [inner_convex_open_thickening]: supporting
    open convex enlargement for Federer 2.10.4(2),
    p. 172. Interpolate the chosen nearby source
    endpoints and use the norm triangle inequality.
    The radius may be arbitrary; nonpositive radii
    give the empty set. *)
Theorem inner_convex_open_thickening (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (A : set V) (r : R) :
  is_inner_convex A -> @is_inner_convex R V
    (@metric_open_thickening R (inner_metric_space hB) A r).
Proof.
move=> hA x y [a ha hax] [b hb hby] t ht0 ht1.
pose c := (1-t)*:a+t*:b.
exists c; first exact: hA a b ha hb t ht0 ht1.
change (is_true (mdist c ((1-t)*:x+t*:y : inner_metric_space hB)<r)).
rewrite inner_metric_distanceE.
have he : c-((1-t)*:x+t*:y)=(1-t)*:(a-x)+t*:(b-y).
  by rewrite /c !scalerBr opprD addrACA.
rewrite he.
have ht : 0<=1-t by rewrite subr_ge0.
have hh := inner_norm_triangle hB ((1-t)*:(a-x)) (t*:(b-y)).
rewrite !inner_normZ !ger0_norm // in hh.
pose q := Order.max (inner_norm hB (a-x)) (inner_norm hB (b-y)).
have hqa : inner_norm hB (a-x)<=q by rewrite /q le_max lexx.
have hqb : inner_norm hB (b-y)<=q by rewrite /q le_max lexx orbT.
have hq : q<r by rewrite /q gt_max; exact/andP.
have hbnd : (1-t)*inner_norm hB (a-x)+t*inner_norm hB (b-y)<=(1-t)*q+t*q.
  apply: lerD; [by rewrite ler_wpM2l|by rewrite ler_wpM2l].
have hsum : (1-t)*q+t*q=q by rewrite mulrBl mul1r subrK.
rewrite hsum in hbnd; exact: le_lt_trans (le_trans hh hbnd) hq.
Qed.
