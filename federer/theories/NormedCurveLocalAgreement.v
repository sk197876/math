(** Federer (1969), 2.9.22, p. 167, actual norm derivative,
    supporting the interval localization of curves in 3.2.46,
    p. 281. Derivatives depend only on a neighbourhood of their
    original point; no extension values are inserted. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import NormedCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [normed_curve_derivative_neighbourhood_agreement]:
    locality of the actual limit in 2.9.22, p. 167, used to replace
    compact-interval curves by Lipschitz representatives in Federer
    3.2.46, p. 281. No derivative is postulated for the representative. *)
Lemma normed_curve_derivative_neighbourhood_agreement (R : realType)
    (E : lmodType R) (N : E -> R) (C D : R -> E) x r v :
  0 < r -> (forall t, `|t-x| < r -> C t = D t) ->
  has_normed_curve_derivative N C x v ->
  has_normed_curve_derivative N D x v.
Proof.
move=> hr hEq hC e he.
have hAt : C x = D x by apply: hEq; rewrite subrr normr0.
have [d [hd hControl]] := hC e he.
exists (Num.min d r); split; first by rewrite lt_min hd hr.
move=> h; rewrite lt_min=> /andP [hh /andP [hhd hhr]].
have hPoint : C (x+h) = D (x+h).
  apply: hEq; by rewrite addrAC subrr add0r.
rewrite -hPoint -hAt; apply: hControl; by apply/andP.
Qed.

(** Source for [normed_curve_derivative_interval_agreement]:
    replacing a curve without changing its values on the compact
    interval preserves the derivative at every interior point in
    Federer 3.2.46, p. 281. The two endpoints are kept separate. *)
Lemma normed_curve_derivative_interval_agreement (R : realType)
    (E : lmodType R) (N : E -> R) (C D : R -> E) a b x v :
  a < x < b -> (forall t, a <= t <= b -> C t = D t) ->
  (has_normed_curve_derivative N C x v <->
   has_normed_curve_derivative N D x v).
Proof.
move=> /andP [hax hxb] hEq.
pose r := Num.min (x-a) (b-x).
have hr : 0 < r by rewrite /r lt_min !subr_gt0 hax hxb.
have hLocal t : `|t-x| < r -> C t = D t.
  rewrite /r lt_min=> /andP [hta htb].
  have hta' : x-t < x-a by rewrite distrC in hta; exact: le_lt_trans (ler_norm _) hta.
  have htb' : t-x < b-x := le_lt_trans (ler_norm _) htb.
  apply: hEq; apply/andP; split; lra.
split.
- exact: normed_curve_derivative_neighbourhood_agreement hr hLocal.
- apply: normed_curve_derivative_neighbourhood_agreement hr _.
  by move=> t ht; exact: esym (hLocal t ht).
Qed.
