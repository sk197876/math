(** Federer (1969), 3.1.11, pp. 220–221:
    integration of the derivative of a class-one
    normed-vector curve. The endpoint difference is
    proved to be the norm limit of all fine
    tagged sums, even when the target is incomplete. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import RealNormUP NormDifferentialUP NormClassOneUP
  NormHigherCurveDerivativeUP NormedStieltjesUP NormedPrimitiveCell
  NormedPrimitivePartition NormedSegmentUniformContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [normed_curve_fundamental_theorem]:
    the fundamental theorem underlying the integration-by-parts
    proof of Taylor's formula in Federer 3.1.11,
    pp. 220–221, with the tagged-sum interpretation
    of 2.5.17, pp. 110–111. The primitive
    itself supplies the integral value; completeness is
    not imposed on the normed target. *)
Theorem normed_curve_fundamental_theorem (R : realType) (Y : lmodType R)
    (NY : Y->R) (hNY : is_real_norm NY)
    (A : R->Prop) (F D : R->Y) (a b : R) :
  a<=b -> (forall t, a<=t<=b -> A t) ->
  (forall t, A t -> has_norm_differential (fun s : R^o=>`|s|) NY A F t
    (scalar_coefficient_linear_map (D t))) ->
  norm_class_zero (fun s : R^o=>`|s|) NY A D ->
  has_normed_stieltjes_integral NY D (fun t=>t) a b (F b-F a).
Proof.
move=> hab hAB hD hcD; split; first exact hab.
move=> e he.
pose eta := e/(b-a+1).
have hwidth : 0<=b-a by rewrite subr_ge0.
have hden : 0<b-a+1 by lra.
have heta : 0<eta by rewrite /eta divr_gt0.
have [d [hd hmod]] := norm_class_zero_real_segment_uniform hNY hAB hcD heta.
exists d; split=> // w hw hm.
have hcell p u q : a<=p -> p<=u -> u<=q -> q<=b -> q-p<d ->
    NY ((q-p)*:D u-(F q-F p))<=eta*(q-p).
  move=> hap hpu huq hqb hsmall.
  have hsegment s : p<=s<=q -> a<=s<=b.
    move=> /andP [hps hsq]; apply/andP; split;
      [exact: le_trans hap hps|exact: le_trans hsq hqb].
  apply: (@normed_primitive_cell_estimate R Y NY hNY A F D p q u eta
    hpu huq (ltW heta)).
  - move=> s hs; exact: hD s (hAB s (hsegment s hs)).
  - move=> s hs.
    have hsu : `|s-u|<=q-p.
      have /andP [hps hsq] := hs.
      rewrite ler_norml; apply/andP; split; lra.
    have hu : a<=u<=b by apply/andP; split;
      [exact: le_trans hap hpu|exact: le_trans huq hqb].
    exact: ltW (hmod s u (hsegment s hs) hu (le_lt_trans hsu hsmall)).
have hb := normed_primitive_partition_estimate hNY hcell hw hm.
have heq : eta*(b-a+1)=e by rewrite /eta divfK // gt_eqF.
have hlast : eta*(b-a)<e by nra.
exact: le_lt_trans hb hlast.
Qed.
