(** General metric background supporting Federer (1969), 2.2.10, p. 65:
    coordinate projections carry Cauchy filters to Cauchy filters. This is
    used to prove product completeness, before applying the locally proved
    2.2.8. Source context: SuslinSetUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [distance_nonincreasing_cauchy_image]: supporting
    metric background for Federer 2.2.10, p. 65: a map
    that does not increase distances carries any proper Cauchy
    filter to a Cauchy filter. This includes projections and
    the inclusion of a metric subspace. *)
Lemma distance_nonincreasing_cauchy_image (R : realType) (T U : metricType R)
    (f : T -> U) (F : set_system T) (PF : ProperFilter F) :
  (forall x y, mdist (f x) (f y) <= mdist x y) ->
  cauchy F -> cauchy (f @ F).
Proof.
move=> hf hc; have FF : Filter F := @filter_filter _ F PF.
have PF' : ProperFilter (f @ F) := @fmap_proper_filter T U f F PF.
apply: (proj2 (@cauchyP R U (f @ F) PF'))=> e he.
have [x hx] := proj1 (@cauchyP R T F PF) hc e he.
exists (f x); apply: (@filterS _ F FF _ _ _ hx)=> y hy.
change (ball (f x) e (f y)); rewrite !ballEmdist /= in hy *.
exact: le_lt_trans (hf x y) hy.
Qed.
