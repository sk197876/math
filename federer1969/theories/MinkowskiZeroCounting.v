(** Federer (1969), 3.2.37, pp. 273--274: both contents in
    degree zero equal the existing counting measure. Consequently the
    printed non-measure sentence needs a positive-degree qualification;
    degree-zero positive atoms must not be discarded. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric MinkowskiContents
  MinkowskiContentsBasic FinitePointTubeVolume CountingMeasure NonnegativeSum
  MeasureUP MeasureBasic PositiveRadiusLowerApproximation PositiveRadiusLimitBounds
  EuclideanBallVolume.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_point_zero_minkowski_contents]: supporting
    degree-zero computation for Federer 3.2.37, pp. 273--274.
    Both actual contents of a finite source equal its full cardinality. *)
Lemma finite_point_zero_minkowski_contents (R:realType) n
    (B:{fset inner_metric_space (@euclidean_inner_productP R n)}):
  upper_minkowski_content 0 [set` B]=(#|` B|%:R:R)%:E /\
  lower_minkowski_content 0 [set` B]=(#|` B|%:R:R)%:E.
Proof.
have [e [he hTube]]:=finite_point_tube_volume (R:=R) B.
have hQuotient r:(0<r<e)%R ->
    minkowski_tube_quotient 0 [set` B] r=(#|` B|%:R:R)%:E.
  move=>hr; have hPositive:=minkowski_tube_denominator_positive n 0 (andP hr).1.
  rewrite /minkowski_tube_quotient subn0 (hTube r hr).
  rewrite subn0 in hPositive.
  by rewrite inver (gt_eqF hPositive) -EFinM -mulrA mulfV ?mulr1 ?gt_eqF.
have hUpper:upper_minkowski_content 0 [set` B]<=(#|` B|%:R:R)%:E.
  apply:positive_radius_upper_eventual_bound he _=>r hr; by rewrite hQuotient.
have hLower:(#|` B|%:R:R)%:E<=lower_minkowski_content 0 [set` B].
  apply:positive_radius_lower_eventual_bound he _=>r hr; by rewrite hQuotient.
have hOrder:=minkowski_contents_ordered 0 [set` B].
split; apply/eqP; rewrite eq_le; apply/andP; split=>//.
- exact:le_trans hLower hOrder.
- exact:le_trans hOrder hUpper.
Qed.

(** Source for [counting_measure_lower_minkowski_bound]: every
    finite source subset supplies a disjoint-ball lower bound, hence
    counting measure is at most the degree-zero lower content,
    Federer 3.2.37, pp. 273--274. Arbitrary infinite sources remain. *)
Lemma counting_measure_lower_minkowski_bound (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))):
  @counting_measure R _ S<=lower_minkowski_content 0 S.
Proof.
rewrite counting_measure_sum; apply:nonnegative_sum_least=>B hBS.
have hB:= (finite_point_zero_minkowski_contents (R:=R) B).2.
have hMono:lower_minkowski_content 0 [set` B]<=lower_minkowski_content 0 S.
  exact:(@minkowski_contents_monotone R n 0 [set` B] S hBS).1.
rewrite hB in hMono.
apply:le_trans _ hMono.
rewrite sumEFin big_seq_fsetE sumr_const cardT cardfE cardE -mulr_natl mulr1.
exact:lexx.
Qed.

(** Source for [zero_minkowski_contents_counting]: the proved
    natural-degree-zero qualification to Federer 3.2.37, p. 274.
    Both contents are exactly counting measure on every original source,
    including uncountable sets and the positive ambient-zero unit atom. *)
Theorem zero_minkowski_contents_counting (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))):
  upper_minkowski_content 0 S=@counting_measure R _ S /\
  lower_minkowski_content 0 S=@counting_measure R _ S.
Proof.
have hLower:=counting_measure_lower_minkowski_bound S.
have hOrder:=minkowski_contents_ordered 0 S.
have hUpper:upper_minkowski_content 0 S<=@counting_measure R _ S.
  case:(pselect (finite_set S))=>hS; last by rewrite (@counting_measure_infinite R (inner_metric_space (@euclidean_inner_productP R n)) S hS); exact:leey.
  pose B:=fset_set S.
  have hE:[set` B]=S.
    apply/seteqP; split=>x hx.
    + have hx':x \in B:=hx; move:hx'; by rewrite /B in_fset_set // => /set_mem.
    + change (x \in B); rewrite /B in_fset_set //; exact:mem_set hx.
  rewrite -hE counting_measure_finite (finite_point_zero_minkowski_contents (R:=R) B).1.
  exact:lexx.
split; apply/eqP; rewrite eq_le; apply/andP; split=>//.
- exact:le_trans hLower hOrder.
- exact:le_trans hOrder hUpper.
Qed.
