(** Federer (1969), 2.9.18(1), p. 163: the finite off-target covers and
    recursively separated radius sequence. The specification records the
    printed laws before selecting a witness. Natural index n denotes printed
    positive index n+1. General topology supplies the finite-subcover
    background. The measure-formula erratum issue is treated separately in
    WeightedHitMeasure.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import MetricClosedBalls MetricSetDistanceUP MetricSetDistanceSealed MetricSetDistanceClosure
  MetricSetSeparationInfimum MeasurableSeparationUP CompactFiniteCover NowhereDenseUP ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_positive_values_lower_bound]: supporting
    finite-minimum argument for dist(S_j,T)>0 in Federer
    2.9.18(1), p. 163. A positive function
    on a finite set has a positive uniform lower bound;
    the empty finite set satisfies this auxiliary property too. *)
Lemma finite_positive_values_lower_bound (R : realType) (X : choiceType)
    (S : set X) (f : X -> R) : finite_set S ->
  (forall x, S x -> 0<f x) -> exists e : R, 0<e /\ forall x, S x -> e<=f x.
Proof.
move=> /finite_fsetP [F ->].
elim/fset1U_rect: F=> [|a F ha ih] hp.
- exists 1; split; first exact: ltr01.
  by move=> x; rewrite /= inE.
- have haa : [set` (a |` F)%fset] a.
    change (is_true (a \in (a |` F)%fset)); exact: fset1U1.
  have hpa : 0<f a := hp a haa.
  have hpf x : x \in F -> 0<f x.
    move=> hx; apply: hp.
    change (is_true (x \in (a |` F)%fset)); exact: fset1Ur hx.
  have [e [he hb]] := ih hpf.
  exists (Num.min (f a) e); split; first by rewrite lt_min hpa he.
  move=> x hx; have hxF : x \in (a |` F)%fset := hx.
  move/fset1UP: hxF=> [->|hxmem].
  + by rewrite ge_min lexx.
  + apply: le_trans _ (hb x hxmem); by rewrite ge_min lexx orbT.
Qed.

(** Source for [finite_closed_set_positive_separation]: supporting
    positive distance between S_j and T in Federer 2.9.18(1),
    p. 163. Finite off-target centers have positive
    distance from a nonempty closed target. The proof uses
    only abstract point-distance laws and the finite-minimum bound. *)
Lemma finite_closed_set_positive_separation (R : realType) (X : metricType R)
    (S T : set X) : finite_set S -> closed T -> T !=set0 -> S `<=` ~` T ->
  (0<metric_set_distance_infimum S T)%E.
Proof.
move=> hS hT hTn hoff.
pose d := @MetricSetDistance.value R X T hTn.
have hd : is_metric_set_distance T d := @MetricSetDistance.laws R X T hTn.
have hp x : S x -> 0<d x.
  move=> hx; exact (@metric_set_distance_positive_outside_closed R X T d hd x hT (hoff x hx)).
have [e [he hb]] := @finite_positive_values_lower_bound R X S d hS hp.
apply: (metric_positive_infimum_separation_iff S T).2.
exists e; split=> // x hx y hy.
exact: le_trans (hb x hx) (@metric_set_distance_lower R X T d hd x y hy).
Qed.

(** Source for [finite_off_target_ball_cover]: direct finite
    open-ball cover used to choose S_j in Federer
    2.9.18(1), p. 163. Compactness extracts
    finitely many centers from the dense complement. For a
    nonempty target their set-distance lies strictly between
    zero and the chosen radius. *)
Theorem finite_off_target_ball_cover (R : realType) (X : metricType R)
    (T : set X) (r : R) : compact T -> is_nowhere_dense T -> T !=set0 -> 0<r ->
  exists S : set X, finite_set S /\ S `<=` ~` T /\
    (forall x, T x -> exists a, S a /\ mdist a x<r) /\
    (0<metric_set_distance_infimum S T<r%:E)%E.
Proof.
move=> hT hnd hTn hr.
have hTc : closed T := compact_closed (@metric_hausdorff R X) hT.
pose U (a : X) := [set x | mdist a x<r].
have hcover : T `<=` \bigcup_(a in ~` T) U a.
  move=> x hx.
  have [a [ha hdist]] := @closed_nowhere_dense_nearby_point R X T x r hTc hnd hr.
  exists a=> //; by rewrite /U /= metric_sym.
have [F hF hTF] := @compact_open_finite_cover X X (~` T) U T hT
  (fun a _ => @metric_open_ball_open R X a r) hcover.
pose S : set X := [set` F].
have hfinite : finite_set S := finite_fset F.
have hoff : S `<=` ~` T.
  move=> a ha; have hmem : a \in F := ha.
  exact (set_mem (hF a hmem)).
have hcov x : T x -> exists a, S a /\ mdist a x<r.
  move=> hx; have [a ha hax] := hTF x hx; by exists a.
have hpos := @finite_closed_set_positive_separation R X S T hfinite hTc hTn hoff.
have [x hx] := hTn; have [a [ha har]] := hcov x hx.
have hmem : metric_set_cross_distances S T (mdist a x)%:E.
  by exists a; split=> //; exists x.
have hupper := @extended_real_inf_lower R _ _ hmem.
exists S; split=> //; split=> //; split=> //.
apply/andP; split=> //; apply: le_lt_trans hupper _; by rewrite lte_fin.
Qed.
