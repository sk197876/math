(** Federer (1969), 2.10.45, printed p. 203: let the positive covering
    margin tend to zero in the factor (u+delta)^m. This supporting numerical
    limit keeps zero side length, degree zero and a zero coefficient. Source
    context: SquaredMetricProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets
  constructive_ereal topology lra ring.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealBounds HausdorffDiameterCost HausdorffGaugeContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_polynomial_margin_limit]: supporting
    removal of delta from the final covering-cost estimate
    in 2.10.45, p. 203. The bounded quantity may
    initially be infinite, but the coefficient is finite;
    this is why the product theorem assumes finite H^k(V). *)
Theorem nonnegative_polynomial_margin_limit (R : realType) m (u cap K : R) (x : \bar R) :
  (0<=u)%R -> (0<cap)%R -> (0<=K)%R ->
  (forall delta : R, (0<delta)%R -> (delta<cap)%R ->
    x<=(K*(u+delta)^+m)%R%:E) -> x<=(K*u^+m)%R%:E.
Proof.
move=> hu hc hK hbound.
case: (eqVneq K 0%R)=> hK0.
  have hh := hbound (cap/2)%R.
  have hp : (0<cap/2)%R by lra.
  have hlt : (cap/2<cap)%R by lra.
  by have hb := hh hp hlt; rewrite hK0 !mul0r in hb *.
have hKpos : (0<K)%R by rewrite lt_neqAle eq_sym hK0 hK.
rewrite leNgt; apply/negP=> hbad.
have [q [hbq hqx]] := @extended_rationals_order_dense R (K*u^+m)%R%:E x hbad.
have hb : (K*u^+m<ratr q)%R by move: hbq; rewrite lte_fin.
pose A := (K/hausdorff_normalisation R m)%R.
have hA : (0<A)%R := divr_gt0 hKpos (hausdorff_normalisation_positive R m).
have hnorm : (A*hausdorff_normalisation R m=K)%R.
  rewrite /A divfK //; exact: lt0r_neq0 (hausdorff_normalisation_positive R m).
have hg : (hausdorff_normalisation R m*u^+m<ratr q/A)%R.
  by rewrite ltr_pdivlMr // mulrC mulrA hnorm.
have hut : (u<u+cap)%R by lra.
have [e [he [hcap hcost]]] := @hausdorff_real_gauge_small_enlargement R m u (u+cap)%R (ratr q/A)%R hut hg.
have hdelta : (0<e+e)%R by lra.
have hsmall : (e+e<cap)%R by lra.
have hh := hbound (e+e)%R hdelta hsmall.
have hr : (K*(u+(e+e))^+m<ratr q)%R.
  move: hcost; by rewrite ltr_pdivlMr // mulrC mulrA hnorm addrA.
have hlt : x<(ratr q : R)%:E.
  apply: le_lt_trans hh _; by rewrite lte_fin.
by have hf := lt_trans hqx hlt; rewrite ltxx in hf.
Qed.
