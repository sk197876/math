(** The fine subrelation in Federer (1969), 2.9.3, p. 154. A strict lower
    covering limit supplies arbitrarily small values below the threshold.
    Localisation to an open neighbourhood and a fixed positive diameter cap
    preserves fineness. The cap makes the auxiliary cells bounded for the
    original measure class M. it explicitly restricts to positive finite
    denominator values. Here the threshold remains Federer's strict one. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import CoveringFamilyUP CoveringRelationUP CoveringRelationFineness
  CoveringRelationLimits MetricDiameterUP MetricDiameter ExtendedRealBounds PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [covering_lower_limit_small_value]: supporting
    form of the fineness assertion in Federer 2.9.3,
    p. 154. A strict lower limit below b
    gives a defined value below b at every positive scale.
    No additional domain-fineness hypothesis is assumed. *)
Lemma covering_lower_limit_small_value (R : realType) (X : metricType R)
    (V : X -> set X -> Prop) (f : partial_function (set X) (\bar R))
    (x : X) (b : \bar R) (e : R) :
  covering_lower_limit V f x<b -> (0<e)%R ->
  exists S y, V x S /\ extended_metric_diameter S<e%:E /\
    partial_function_graph f S y /\ y<b.
Proof.
move=> hl he.
have hinf : extended_real_inf (covering_value_range V f x e)<b :=
  le_lt_trans (@covering_lower_limit_ge_level R X V f x e he) hl.
apply: contrapT=> hn.
have hb : b<=extended_real_inf (covering_value_range V f x e).
  apply: extended_real_inf_greatest=> y [S [hS [hd hf]]].
  rewrite leNgt; apply/negP=> hy; apply: hn; exists S,y; by split=> //; split=> //; split.
by have := le_lt_trans hb hinf; rewrite ltxx.
Qed.

(** Source for [covering_lower_sublevel]: auxiliary fine
    subrelation for Federer 2.9.3, p. 154.
    In addition to the printed neighbourhood and strict value
    cutoff, impose a positive diameter cap. This is an
    auxiliary refinement, not an additional theorem hypothesis. *)
Definition covering_lower_sublevel (R : realType) (X : metricType R)
    (V : X -> set X -> Prop) (f : partial_function (set X) (\bar R))
    (b : \bar R) (W : set X) (cap : R) (x : X) (S : set X) :=
  V x S /\ S `<=` W /\ extended_metric_diameter S<cap%:E /\
    exists y, partial_function_graph f S y /\ y<b.

(** Source for [covering_lower_sublevel_bounded]: supporting
    boundedness of the auxiliary cells in the proof of
    Federer 2.9.3, p. 154. The bound permits
    using the original finiteness-on-bounded-sets hypothesis. *)
Lemma covering_lower_sublevel_bounded (R : realType) (X : metricType R)
    (V : X -> set X -> Prop) (f : partial_function (set X) (\bar R))
    (b : \bar R) (W : set X) (cap : R) x S :
  covering_lower_sublevel V f b W cap x S -> metric_set_bounded S.
Proof. move=> [_ [_ [hd _]]]; exact: lt_trans hd (ltry cap). Qed.

(** Source for [covering_lower_sublevel_fine]: the fine-at-
    A-intersection-W assertion in Federer 2.9.3, p. 154,
    with an auxiliary bounded-cell cutoff. Use a radius below
    the requested scale, the open neighbourhood radius and
    the fixed cap; the containing base point controls inclusion. *)
Lemma covering_lower_sublevel_fine (R : realType) (X : metricType R)
    (V : X -> set X -> Prop) (f : partial_function (set X) (\bar R))
    (b : \bar R) (W : set X) (cap : R) (x : X) :
  is_covering_relation V -> open W -> W x -> (0<cap)%R ->
  covering_lower_limit V f x<b ->
  covering_relation_fine_at (covering_lower_sublevel V f b W cap) x.
Proof.
move=> hv hW hx hcap hl.
have hnb : nbhs x W by rewrite openE in hW; exact: hW x hx.
have [d hd hWd] := (metricType_numDomainType.nbhs_mdistP x _).1 hnb.
apply: (covering_relation_fine_iff_small_diameter _ x).2=> e he.
pose t := (Num.min e (Num.min d cap))%R.
have ht : (0<t)%R by rewrite /t !lt_min he hd hcap.
have hte : (t<=e)%R by rewrite /t ge_min lexx.
have htdc : (t<=Num.min d cap)%R by rewrite /t ge_min lexx orbT.
have hdc : (Num.min d cap<=d)%R by rewrite ge_min lexx.
have htd : (t<=d)%R := le_trans htdc hdc.
have hcc : (Num.min d cap<=cap)%R by rewrite ge_min lexx orbT.
have htc : (t<=cap)%R := le_trans htdc hcc.
have [S [y [hS [hdiam [hf hy]]]]] := @covering_lower_limit_small_value R X V f x b t hl ht.
have hwithin : S `<=` W.
  move=> z hz; apply: hWd.
  have hdist := metric_diameter_upper (extended_metric_diameter_specification S) (hv x S hS) hz.
  have htdE : t%:E<=d%:E by rewrite lee_fin.
  have hh := le_lt_trans hdist (lt_le_trans hdiam htdE).
  by rewrite lte_fin in hh.
exists S; split.
- split=> //; split=> //; split.
  + apply: lt_le_trans hdiam _; by rewrite lee_fin.
  + by exists y.
- apply: lt_le_trans hdiam _; by rewrite lee_fin.
Qed.
