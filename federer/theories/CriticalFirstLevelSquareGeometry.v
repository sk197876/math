(** Federer (1969), 3.3.20, p. 308: actual first-split geometry. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology lra ring.
From Federer Require Import RealMetricBackground CriticalFirstLevelIntervalSelection
  CriticalSecondLevelIntervals CriticalCornerCoordinate CriticalCornerCoordinateSeparation
  EuclideanInnerProduct InnerMetric EuclideanRealPlane MetricCartesianProductUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_second_level_interval_in_parent]: the actual
    original second-level interval is contained in its original first-level
    parent in the initial reduction of 3.3.20, p. 308. *)
Lemma critical_second_level_interval_in_parent (R:realType) (b t:bool):
  (`[critical_second_level_coordinate R b t,
    critical_second_level_coordinate R b t+1/16]:set R) `<=`
  (`[critical_first_level_coordinate R b,
    critical_first_level_coordinate R b+1/4]:set R).
Proof.
move=>x;rewrite /critical_second_level_coordinate /critical_first_level_coordinate.
case:b;case:t;rewrite /= !in_itv /=;move=>/andP[h0 h1];apply/andP;split;lra.
Qed.

(** Source for [critical_first_level_coordinate_gap]: the gap between
    opposite first-level intervals is one half, 3.3.20, p. 308. *)
Lemma critical_first_level_coordinate_gap (R:realType) (b:bool) (x y:R):
  (`[critical_first_level_coordinate R b,critical_first_level_coordinate R b+1/4]:set R) x ->
  (`[critical_first_level_coordinate R (negb b),critical_first_level_coordinate R (negb b)+1/4]:set R) y ->
  (1/2:R)<=`|x-y|.
Proof.
have hN:x-y<=`|x-y| :=ler_norm _.
have hO:y-x<=`|x-y| by rewrite distrC;exact:ler_norm.
case:b;rewrite /critical_first_level_coordinate /= !in_itv /=;
  move=>/andP[hx0 hx1] /andP[hy0 hy1];lra.
Qed.

(** Source for [critical_first_level_distinct_square_gap]: two distinct
    original first-level squares have distance at least one half,
    3.3.20, p. 308. Both coordinate orientations are proved. *)
Lemma critical_first_level_distinct_square_gap (R:realType) (b d e f:bool)
    (p q:inner_metric_space (@euclidean_inner_productP R 2)):
  (b,d)!=(e,f) ->
  (`[critical_first_level_coordinate R b,critical_first_level_coordinate R b+1/4]:set R) (euclidean_real_plane_first p) ->
  (`[critical_first_level_coordinate R d,critical_first_level_coordinate R d+1/4]:set R) (euclidean_real_plane_second p) ->
  (`[critical_first_level_coordinate R e,critical_first_level_coordinate R e+1/4]:set R) (euclidean_real_plane_first q) ->
  (`[critical_first_level_coordinate R f,critical_first_level_coordinate R f+1/4]:set R) (euclidean_real_plane_second q) ->
  (1/2:R)<=mdist p q.
Proof.
move=>hDifferent hp0 hp1 hq0 hq1.
have hX:`|euclidean_real_plane_first p-euclidean_real_plane_first q|<=mdist p q.
  have h:=(metric_product_first_nonexpanding (@euclidean_real_plane_is_metric_product R)).2 p q Logic.I Logic.I.
  by rewrite mul1r real_line_metric_distanceE in h.
have hY:`|euclidean_real_plane_second p-euclidean_real_plane_second q|<=mdist p q.
  have h:=(metric_product_second_nonexpanding (@euclidean_real_plane_is_metric_product R)).2 p q Logic.I Logic.I.
  by rewrite mul1r real_line_metric_distanceE in h.
have hOpp:forall u v:bool,u!=v ->v=negb u by move=>[] [] //.
case hBE:(b==e).
- have hSame:e=b by apply/eqP;by rewrite eq_sym hBE.
  rewrite hSame in hDifferent hq0.
  have hDNE:d!=f.
    apply/negP=>/eqP hDF;move:hDifferent;by rewrite hDF eqxx.
  have hFlip:f=negb d:=hOpp _ _ hDNE.
  rewrite hFlip in hq1.
  exact:le_trans (critical_first_level_coordinate_gap hp1 hq1) hY.
- have hNE:b!=e by rewrite hBE.
  have hFlip:e=negb b:=hOpp _ _ hNE.
  rewrite hFlip in hq0.
  exact:le_trans (critical_first_level_coordinate_gap hp0 hq0) hX.
Qed.

(** Source for [critical_first_level_diagonal_square_gap]: opposite
    original first-level corner squares have distance at least sqrt(2)/2,
    the initial diagonal alternative in 3.3.20, p. 308. *)
Lemma critical_first_level_diagonal_square_gap (R:realType) (b d:bool)
    (p q:inner_metric_space (@euclidean_inner_productP R 2)):
  (`[critical_first_level_coordinate R b,critical_first_level_coordinate R b+1/4]:set R) (euclidean_real_plane_first p) ->
  (`[critical_first_level_coordinate R d,critical_first_level_coordinate R d+1/4]:set R) (euclidean_real_plane_second p) ->
  (`[critical_first_level_coordinate R (negb b),critical_first_level_coordinate R (negb b)+1/4]:set R) (euclidean_real_plane_first q) ->
  (`[critical_first_level_coordinate R (negb d),critical_first_level_coordinate R (negb d)+1/4]:set R) (euclidean_real_plane_second q) ->
  Num.sqrt (2:R)/2<=mdist p q.
Proof.
have hCoordinate t:critical_corner_coordinate (4:R) t 0=critical_first_level_coordinate R t.
  by case:t;rewrite /critical_corner_coordinate /critical_first_level_coordinate /=;field;rewrite ?pnatr_eq0.
move=>hp0 hp1 hq0 hq1.
have hFourPositive:(0<4:>R) by rewrite ltr0n.
have h:=@critical_opposite_corner_square_gap R 4 b d 0 0 0 0 0 p q
  hFourPositive (leqnn 0).
rewrite !hCoordinate in h.
have hBound:=h hp0 hp1 hq0 hq1.
have hFactor:(1-(0+4)%:R/(2 * 4):R)= 1/2 by field;rewrite ?pnatr_eq0.
rewrite hFactor in hBound.
lra.
Qed.
