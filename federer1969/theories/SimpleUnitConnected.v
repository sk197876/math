(** Federer (1969), 1.8.1, p. 38: S is connected. connectedness is not
    separately asserted there. We express S as the union of its radial
    segments, all meeting at zero, and use only general topological
    connectedness. *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import boolp classical_sets set_interval reals topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import InnerProductUP InnerMetric InnerNormedTopology
  InnerExteriorPositivity ExteriorGrading SimpleUnitBall.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [simple_unit_ball_connected]: Federer 1.8.1,
    p. 38, connectedness of the simple unit ball. The radial-segment
    proof works in arbitrary ambient dimension and positive degree. *)
Theorem simple_unit_ball_connected (R : realType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    m (hm : (0 < m)%N) :
  connected (@simple_unit_ball R h2 V B hB m :
    set (inner_metric_space (@exterior_inner_productP R h2 V B hB m))).
Proof.
pose E := inner_metric_space (@exterior_inner_productP R h2 V B hB m).
pose S : set E := @simple_unit_ball R h2 V B hB m.
pose P (x : E) := (fun t : R^o => t *: x) @` `[0,1].
have hP x : connected (P x).
  apply: connected_continuous_connected; first exact: segment_connected.
  apply: continuous_subspaceT => t; apply: continuousZ.
  - by [].
  - exact: cst_continuous.
have h0 : (\bigcap_(x in S) P x) !=set0.
  exists 0 => x hx; exists (0 : R); last by rewrite scale0r.
  by rewrite set_itvcc /= lexx ler01.
have heq : S = \bigcup_(x in S) P x.
  apply/seteqP; split=> x.
  - move=> hx; exists x => //; exists (1 : R); last by rewrite scale1r.
    by rewrite set_itvcc /= ler01 lexx.
  - move=> [y hy [t ht <-]].
    move: ht; rewrite set_itvcc /= => /andP[ht0 ht1].
    apply: simple_unit_ball_scale hm _ hy; by rewrite (ger0_norm ht0).
change (connected S); rewrite heq.
apply: bigcup_connected h0 _ => x hx; exact: hP.
Qed.
