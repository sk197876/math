(** Federer (1969), 2.9.24, p. 169: absolute continuity of g on [a,b]
    supplies the local bounded-variation input used by 2.9.20, pp. 165–166.
    The local Federer erratum has no entry for this formula. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  constructive_ereal topology ring lra.
From Federer Require Import RealMetricBackground CurveVariationUP CurveArcLength
  StieltjesIntegral StieltjesSubstitution RealAbsoluteContinuityUP
  RealAbsoluteContinuityVariation FiniteIntervalVariationLocalization.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [uniform_short_variation_sum_bound]: supporting finite
    subdivision argument for Federer 2.9.24, p. 169, and 2.9.20, p. 166. If
    every subinterval of length at most d has variation at most one, n
    successive cells of width h<=d have variation at most n. Zero-width and
    zero-cell cases are included. *)
Lemma uniform_short_variation_sum_bound (R : realType) (g : R -> R)
    (a b d h : R) : 0<=h -> h<=d ->
  (forall u v : R, a<=u -> u<=v -> v<=b -> v-u<=d ->
    (curve_variation (g : R -> real_line_metric R) u v<=1)%E) ->
  forall (n : nat) (u : R), a<=u -> u+n%:R*h<=b ->
    (curve_variation (g : R -> real_line_metric R) u (u+n%:R*h)<=n%:R%:E)%E.
Proof.
move=> hh hhd hsmall; elim=> [|n ih] u hau hub.
- by rewrite mul0r addr0 curve_variation_self.
- have hn0 : 0<=n%:R*h by rewrite mulr_ge0 // ler0n.
  have hend : u+n.+1%:R*h=u+h+n%:R*h.
    by rewrite -addn1 natrD mulrDl mul1r; ring.
  have huh : u<=u+h by lra.
  have huhb : u+h<=b by rewrite hend in hub; lra.
  have huhe : u+h-u<=d by lra.
  have hfirst := hsmall u (u+h) hau huh huhb huhe.
  have hrest := ih (u+h) (le_trans hau huh).
  rewrite hend in hub.
  have hR := hrest hub.
  have horder : u+h<=u+h+n%:R*h by lra.
  rewrite hend (@curve_variation_split R [the metricType R of real_line_metric R]
    g u (u+h) (u+h+n%:R*h) huh horder).
  have hbnd := leeD hfirst hR.
  have hnE : ((1 : R)%:E+(n%:R : R)%:E)%E=(n.+1%:R : R)%:E.
    by rewrite -EFinD -[n.+1]addn1 natrD addrC.
  by rewrite hnE in hbnd.
Qed.

(** Source for [real_absolute_continuity_finite_variation]: supporting
    finite variation implied by the printed absolute continuity hypothesis
    in Federer 2.9.24, p. 169. Neither continuity nor variation outside
    [a,b] is assumed. *)
Theorem real_absolute_continuity_finite_variation (R : realType) (g : R -> R)
    (a b : R) : a<=b -> is_absolutely_continuous_real_curve g a b ->
  (curve_variation (g : R -> real_line_metric R) a b < +oo)%E.
Proof.
move=> hab hAC.
have [d [hd hsmall]] := real_absolute_continuity_small_variation hAC ltr01.
have [n hn] := @uniform_mesh_small R a b d hab hd.
pose h := (b-a)/n.+1%:R.
have hh : 0<=h by rewrite /h divr_ge0 ?subr_ge0 ?ler0n.
have hhd : h<=d := ltW (hn n (leqnn n)).
have hend : a+n.+1%:R*h=b.
  by rewrite /h mulrC mulfVK ?pnatr_eq0 // addrC subrK.
have hb := @uniform_short_variation_sum_bound R g a b d h hh hhd hsmall
  n.+1 a (lexx a).
rewrite hend in hb.
exact: le_lt_trans (hb (lexx b)) (ltry _).
Qed.

(** Source for [absolutely_continuous_retracted_curve_variation]: supporting
    globally defined proof representative for the local absolute-continuity
    hypothesis in Federer 2.9.24, p. 169. *)
Lemma absolutely_continuous_retracted_curve_variation (R : realType) (g : R -> R)
    (a b : R) : a<=b -> is_absolutely_continuous_real_curve g a b ->
  curve_locally_finite_variation (g \o @segment_retraction R a b : R -> real_line_metric R).
Proof.
move=> hab hAC; exact: finite_interval_retracted_curve_variation hab
  (real_absolute_continuity_finite_variation hab hAC).
Qed.
