(** Federer (1969), 3.4.2(6)–(7), p. 312: compact pieces in a
    zero-dimensional manifold have eventually zero oscillation. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import ModuleQuotient GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness NormMetric ExtendedSupremumUP
  EuclideanSubmanifoldUP SubmanifoldBasicLaws CompactIsolatedSourceSeparation
  PositiveRightOrderLimit CriticalOscillationUP CriticalOscillation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [eventually_zero_positive_cutoff_limit]: supporting the
    vanishing-oscillation assertion in the discrete case of 3.4.2(7),
    p. 312. An extended-real function that is zero at every sufficiently
    small positive cutoff has the ordinary right-hand limit zero. *)
Lemma eventually_zero_positive_cutoff_limit (R:realType) (u:R->\bar R) d:
  0<d ->(forall delta,0<delta ->delta<d ->u delta=0%E) ->
  positive_right_extended_order_limit u 0%E.
Proof.
move=>hd hZero;split.
- move=>b hb;exists d;split;first exact:hd.
  move=>delta hdelta hsmall;by rewrite (hZero delta hdelta hsmall).
- move=>b hb;exists d;split;first exact:hd.
  move=>delta hdelta hsmall;by rewrite (hZero delta hdelta hsmall).
Qed.

(** Source for [critical_eta_zero_below_separation]: supporting the
    discrete case of 3.4.2(7), p. 312. A uniform source isolation scale
    excludes all original positive-distance quotient tests below it. *)
Lemma critical_eta_zero_below_separation (R:realType) m (Y:lmodType R)
    (NY:Y->R) (Z:subspace (R_n R m)) (S C:set (R_n R m))
    (f:R_n R m->Y) (lambda delta d:R):
  (forall x c,S x ->C c ->inner_norm (@euclidean_inner_productP R m) (x-c)<d ->x=c) ->
  delta<d ->critical_eta NY Z S C f lambda delta=0%E.
Proof.
move=>hSep hd;apply/eqP;rewrite eq_le;apply/andP;split;last exact:critical_eta_nonnegative.
apply:(extended_supremum_least (critical_eta_laws NY Z S C f lambda delta)).
move=>q [->|[x [c [hx [hc [_ [/andP[hp hdist] hq]]]]]]];first exact:lexx.
have he:x=c:=hSep x c hx hc (le_lt_trans hdist hd).
by rewrite he subrr inner_norm0 ltxx in hp.
Qed.

(** Source for [critical_zero_manifold_eta_zero_limit]: the
    zero-dimensional case of (6) and the mu=nu=0 base case of (7),
    3.4.2, p. 312. Compactness derives a uniform isolation scale from
    the already proved isolated-point characterization of 3.1.19.
    The conclusion holds for every function and every real exponent. *)
Theorem critical_zero_manifold_eta_zero_limit (R:realType) m k (Y:lmodType R)
    (NY:Y->R) (Z:subspace (R_n R m)) (S C:set (R_n R m))
    (f:R_n R m->Y) lambda:
  @is_euclidean_submanifold R m 0 k S ->C `<=` S ->
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m))) C ->
  positive_right_extended_order_limit
    (fun delta=>critical_eta NY Z S C f lambda delta) 0%E.
Proof.
move=>hS hCS hC.
have hIso c (hc:C c):norm_isolated_point
    (inner_norm (@euclidean_inner_productP R m)) S c.
  exact:(zero_submanifold_point_isolated hS (hCS c hc)).
have [d [hd hSep]]:=@compact_isolated_source_separation R (R_n R m)
  (inner_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R m)) S C hC hIso.
apply:(@eventually_zero_positive_cutoff_limit R
  (fun delta=>critical_eta NY Z S C f lambda delta) d hd)=>delta hdelta hsmall.
exact:(@critical_eta_zero_below_separation R m Y NY Z S C f lambda delta d hSep hsmall).
Qed.
