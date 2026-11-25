(** Federer (1969), 3.2.40, p. 276: the actual number
    of equal-width level intervals is determined by their
    conserved power cost from 2.10.28, p. 193. *)
From mathcomp Require Import all_boot all_order all_algebra finmap
  boolp classical_sets reals constructive_ereal topology ring.
From Federer Require Import RealMetricBackground RealPower RealPowerSuccessor
  RealPowerContinuity CompactIntervalGauge MetricDiameter
  EqualCostIntervalTreeUP PowerCantorLevelWeights.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_fset_constant_real_sum]: supporting scalar
    finite-count calculation for Federer 3.2.40, p. 276.
    This is finite addition, including the empty family. *)
Lemma finite_fset_constant_real_sum (R:realType) (X:choiceType)
    (F:{fset X}) (a:R):
  (\sum_(x<-F) a)=#|` F|%:R*a.
Proof.
rewrite big_seq_fsetE sumr_const cardT cardfE cardE.
exact:esym (mulr_natl a _).
Qed.

(** Source for [power_cantor_uniform_level_weight_count]: supporting
    the level-square tube estimate in Federer 3.2.40, p. 276.
    The actual finite level has N intervals of common width s,
    and its conserved power cost gives N*s^m=1. Neither N
    nor the widths are specified by a replacement construction. *)
Lemma power_cantor_uniform_level_weight_count (R:realType) (c m:R)
    (J:compact_real_intervals R) n H j (s:R):
  0<c ->0<m ->m<1 ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c*real_power t m) J n H ->
  (forall S,S \in H j ->fine (@extended_metric_diameter R
    [the metricType R of real_line_metric R] (val S))=s) ->
  #|` H j|%:R*real_power s m= 1.
Proof.
move=>hc hm hm1 hJ hTree hWidth.
have hSum:=@power_cantor_level_weight_sum R c m J n H hc hm hm1 hJ hTree j.
have hTerms:(\sum_(S<-H j) real_power
    (fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val S))) m)=
    \sum_(S<-H j) real_power s m.
  apply:eq_big_seq=>S hS; by rewrite (hWidth S hS).
by rewrite hTerms finite_fset_constant_real_sum in hSum.
Qed.

(** Source for [power_cantor_square_scaled_count]: supporting the
    common factor N_j^2*s_j in Federer 3.2.40, p. 276.
    Actual conserved weights identify it with s_j^(1-2m).
    Positivity of the width justifies every reciprocal; the
    exponent m need not be restricted for this scalar identity. *)
Lemma power_cantor_square_scaled_count (R:realType) (m s:R) (N:nat):
  0<s ->N%:R*real_power s m= 1 ->
  (N%:R)^+2*s=real_power s (1-2 * m).
Proof.
move=>hs hCount.
have hPositive:=@real_power_strictly_positive R s m hs.
have hNonzero:real_power s m!=0 by rewrite gt_eqF.
have hN:(N%:R:R)=(real_power s m)^-1.
  have h:=congr1 (fun z:R=>z/real_power s m) hCount.
  by rewrite mulfK // div1r in h.
have hSquare:(real_power s m)^+2=real_power s (2 * m).
  have hExponent:m+m= 2 * m by ring.
  by rewrite expr2 -(@real_power_add_exponents_positive R s m m hs) hExponent.
have hProduct:real_power s (1-2 * m)=s*real_power s (- (2 * m)).
  by rewrite (@real_power_add_exponents_positive R s 1 (- (2 * m)) hs)
    (@real_power_one_exponent R s (ltW hs)).
by rewrite hN exprVn hSquare -(@real_power_negative_exponent R s (2 * m) hs) hProduct mulrC.
Qed.
