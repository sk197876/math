(** General metric background supporting Federer (1969), 3.1.1,
    p. 211: a finite Lipschitz bound preserves Cauchy filters. This
    is used for basis evaluations on the continuous operator space. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_lipschitz_cauchy_image]: supporting metric
    fact for completeness of Z in 3.1.1, p. 211. No completeness
    of either space is needed to preserve the Cauchy property. *)
Lemma metric_lipschitz_cauchy_image (R : realType) (T U : metricType R)
    (f : T -> U) (L : R) (F : set_system T) (PF : ProperFilter F) :
  0 <= L -> (forall x y, mdist (f x) (f y) <= L*mdist x y) ->
  cauchy F -> cauchy (f @ F).
Proof.
move=> hL hb hc; have FF : Filter F := @filter_filter _ F PF.
have PF' : ProperFilter (f @ F) := @fmap_proper_filter T U f F PF.
apply: (proj2 (@cauchyP R U (f @ F) PF'))=> e he.
have hp : 0 < 1+L by rewrite ltr_pwDl.
have hd : 0 < e/(1+L) by rewrite divr_gt0.
have [x hx] := proj1 (@cauchyP R T F PF) hc _ hd.
exists (f x); apply: (@filterS _ F FF _ _ _ hx)=> y hy.
change (ball (f x) e (f y)); rewrite !ballEmdist /= in hy *.
apply: le_lt_trans (hb x y) _.
have hle : L*mdist x y <= (1+L)*mdist x y.
  apply: ler_wpM2r; first exact: mdist_ge0.
  by rewrite lerDr.
apply: le_lt_trans hle _.
rewrite mulrC -ltr_pdivlMr //; exact hy.
Qed.
