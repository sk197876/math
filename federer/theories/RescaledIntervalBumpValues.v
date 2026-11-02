(** Federer (1969), 3.2.33, p. 270: scalar values
    of an individual term of the printed smooth series. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp lra.
From Federer Require Import RealOpenIntervals PositiveUnitIntervalBumpUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [rescaled_interval_bump_values]: supporting
    nonnegative normal convergence and exact positivity of psi
    in Federer 3.2.33, p. 270. Every term lies between
    zero and d^(j+1) and is positive precisely on its
    actual interval. No convergence or positivity of the sum
    is assumed. *)
Lemma rescaled_interval_bump_values (R:realType) (phi:R->R) j a b t:
  is_positive_unit_interval_bump phi ->a<b ->
  let d:=b-a in
  0<=d^+j.+1*phi ((t-a)/d)<=d^+j.+1 /\
  (0<d^+j.+1*phi ((t-a)/d) <->real_open_interval a b t).
Proof.
move=>hPhi hab d.
have hd:0<d by rewrite /d subr_gt0.
have hPower:0<d^+j.+1:=exprn_gt0 _ hd.
have /andP [hNonnegative hUnit]:=positive_interval_bump_bounds hPhi ((t-a)/d).
split.
- apply/andP; split; first exact:mulr_ge0 (ltW hPower) hNonnegative.
  by rewrite -{2}[d^+j.+1]mulr1 (ler_wpM2l (ltW hPower) hUnit).
- have hPos:(0<d^+j.+1*phi ((t-a)/d))= (0<phi ((t-a)/d)).
    by rewrite pmulr_rgt0.
  rewrite hPos (positive_interval_bump_positive hPhi).
  split.
  + move=>/andP [h0 h1].
    have ht0:0<t-a by move:h0; rewrite ltr_pdivlMr // mul0r.
    have ht1:t-a<d by move:h1; rewrite ltr_pdivrMr // mul1r.
    change (a<t /\t<b); rewrite /d in ht1; split; lra.
  + move=>[h0 h1]; apply/andP; split.
    * apply:divr_gt0=>//; by rewrite subr_gt0.
    * rewrite ltr_pdivrMr // mul1r /d; lra.
Qed.
