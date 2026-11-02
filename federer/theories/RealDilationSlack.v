(** Supporting real polynomial continuity for the
    homothetic comparison in Federer (1969), 2.10.4(2),
    p. 172. A dilation parameter strictly above one
    can keep its degree-m cost below any strict
    upper bound at one. This is a proof ingredient,
    not an extra printed measure assertion. Source
    editions and the homothety context: ProjectedVolumeDilation.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology num_normedtype pseudometric_normed_Zmodule normed_module.
From mathcomp Require Import lra.
From Federer Require Import RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_integral_power_continuous]: supporting
    polynomial continuity in the proof of Federer
    2.10.4(2), p. 172. Multiplication and constants
    suffice, including the empty power m=0. *)
Lemma real_integral_power_continuous (R : realType) (m : nat) :
  continuous (fun t : R^o => t^+m).
Proof.
elim: m=> [|m ih] t; first exact: cvg_cst.
have he : (fun y : R^o => y^+m.+1)=(fun y : R^o => y*y^+m).
  by apply: funext=> y; rewrite exprS.
rewrite he; exact: cvgM cvg_id (ih t).
Qed.

(** Source for [real_positive_dilation_cost_slack]: supporting
    arbitrarily small strict dilations for Federer
    2.10.4(2), p. 172. The coefficient need not
    be positive in this elementary continuity lemma. *)
Lemma real_positive_dilation_cost_slack (R : realType) (m : nat) (c b : R) :
  c<b -> exists t : R, 1<t /\ c*t^+m<b.
Proof.
move=> hcb.
pose f (z : real_line_metric R) : real_line_metric R := c*z^+m.
have hf : continuous f.
  move=> z; apply: (@continuousM R R^o (fun _ => c) (fun y => y^+m) z).
  - exact: cst_continuous.
  - exact: real_integral_power_continuous.
have h0 : f 1=c by rewrite /f expr1n mulr1.
have hn : nbhs (f 1) [set y : real_line_metric R | y<b].
  rewrite h0; have ho : @open (real_line_metric R) [set y | y<b] := @open_lt R b.
  by rewrite openE in ho; exact: ho c hcb.
have [e he hball] := proj1 (metricType_numDomainType.nbhs_mdistP (1 : real_line_metric R) _)
  (hf 1 _ hn).
have hepos : 0<e := he.
pose t := 1+e/2.
have ht : 1<t by rewrite /t ltrDl divr_gt0.
have hdist : mdist (1 : real_line_metric R) t<e.
  rewrite /t real_line_metric_distanceE opprD addrA subrr add0r normrN ger0_norm.
  - lra.
  - by rewrite divr_ge0 // ltW.
exists t; split=> //; exact: hball t hdist.
Qed.
