(** Federer (1969), 2.5.20, p. 114: the radial splitting in 2.5.12(4), p.
    103, preserves continuous vector families. At nonzero norm the quotient
    formula is continuous; at zero its norm is bounded by the original
    continuous norm. The narrow num_normedtype import supplies only real
    order-topology background. Source context: CompactFunctionSpaceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology num_normedtype.
From mathcomp.analysis.normedtype_theory Require Import pseudometric_normed_Zmodule normed_module.
From Federer Require Import RealNormUP NormMetric RealMetricBackground NormMetricContinuity
  NormMetricJointScale ContinuousRadialSplitLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_radial_split_continuous]: supporting
    verification of the last clause of Federer 2.5.12(4),
    p. 103, for Q in 2.5.20, p. 114.
    The zero-norm case is proved directly, so division does
    not introduce an unsupported nonvanishing hypothesis. *)
Theorem norm_radial_split_continuous (R : realType) (X : topologicalType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (w : X -> E) (f : X -> R) :
  continuous (w : X -> real_norm_metric_space hN) ->
  continuous (f : X -> real_line_metric R) ->
  (forall x, 0<=f x) -> (forall x, f x<=N (w x)) ->
  continuous (fun x => (norm_radial_split N (w x) (f x) : real_norm_metric_space hN)).
Proof.
move=> hw hf hf0 hb a.
have hnorm : continuous (fun x : X => (N (w x) : real_line_metric R)).
  move=> x; exact: continuous_comp (hw x) (@real_norm_metric_norm_continuous R E N hN (w x)).
case: (eqVneq (N (w a)) 0)=> [hz|hnz].
- have hwa : w a=0 := hN.2 _ hz.
  have hxi : norm_radial_split N (w a) (f a)=0 by rewrite /norm_radial_split hwa scaler0.
  move=> U hU.
  have [e he hball] := proj1 (metricType_numDomainType.nbhs_mdistP
    (norm_radial_split N (w a) (f a) : real_norm_metric_space hN) U) hU.
  have hnear : nbhs (N (w a) : real_line_metric R) [set r | r<e].
    apply: open_nbhs_nbhs; split; first exact: open_lt.
    by rewrite hz.
  have hs := hnorm a _ hnear.
  apply: (@filterS _ _ (@nbhs_filter X a) _ _ _ hs)=> x hx.
  apply: hball.
  change (N (norm_radial_split N (w a) (f a)-norm_radial_split N (w x) (f x))<e).
  rewrite hxi sub0r (real_seminorm_negate hN.1)
    (norm_radial_split_norm hN (hf0 x) (hb x)).
  exact: le_lt_trans (hb x) hx.
- have hratio : (fun x : X => (f x/N (w x) : real_line_metric R)) @ nbhs a -->
      (f a/N (w a) : real_line_metric R).
    apply: (@continuousM R X f (fun x => (N (w x))^-1) a); first exact: hf a.
    apply: (@continuousV R X (fun x => N (w x)) a)=> //; exact: hnorm a.
  exact: continuous_comp (cvg_pair hratio (hw a))
    (@real_norm_metric_joint_scale_continuous R E N hN (f a/N (w a),w a)).
Qed.
