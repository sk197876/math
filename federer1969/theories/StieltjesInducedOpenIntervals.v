(** Supporting induced-measure interval laws for Federer (1969), 2.10.7, pp.
    174–175, from 2.5.17, p. 111. For nondecreasing g, the negative induced
    measure vanishes; the positive one is bounded by each raw interval
    increment and equals it at continuity endpoints. Supply local finiteness
    and the half-open bookkeeping needed for uniqueness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology normedtype.
From mathcomp Require Import lra.
From Federer Require Import RealMetricBackground StieltjesImageMeasures StieltjesInducedPairLaws
  StieltjesMonotone StieltjesContinuityPoints MeasureUP MeasureBasic HalfOpenIntervalAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [monotone_induced_open_interval_bound]:
    supporting raw-increment bound for the actual
    positive induced measure in Federer 2.10.7,
    p. 174, from 2.5.17, p. 111.
    No endpoint continuity is needed for the bound. *)
Lemma monotone_induced_open_interval_bound (R : realType) (g : R -> R)
    (mu nu : set R -> \bar R) (a b : R) :
  (forall x y, (x<=y)%R -> (g x<=g y)%R) -> is_induced_measure_pair g mu nu ->
  (a<b)%R -> mu `]a,b[<=(g b-g a)%:E.
Proof.
move=> hg hp hab.
have hfin := @monotone_locally_finite_variation R g hg.
have hzero := (@induced_measure_pair_monotone R g hfin hg mu nu hp).1.
have [_ [_ [_ [_ [_ [_ [_ [_ [_ [hOpen _]]]]]]]]]] :=
  @induced_measure_pair_laws R g hfin mu nu hp.
have hb := hOpen a b (ltW hab).
by rewrite hzero adde0 (@monotone_total_variation R g hg a b (ltW hab)) in hb.
Qed.

(** Source for [monotone_induced_open_interval_increment]:
    supporting induced-measure identity at the
    continuity endpoints in Federer 2.10.7,
    p. 174, from 2.5.17, p. 111. *)
Lemma monotone_induced_open_interval_increment (R : realType) (g : R -> R)
    (mu nu : set R -> \bar R) (a b : R) :
  (forall x y, (x<=y)%R -> (g x<=g y)%R) -> is_induced_measure_pair g mu nu ->
  (a<b)%R -> g @ a --> g a -> g @ b --> g b -> mu `]a,b[=(g b-g a)%:E.
Proof.
move=> hg hp hab hca hcb.
have hfin := @monotone_locally_finite_variation R g hg.
have hzero := (@induced_measure_pair_monotone R g hfin hg mu nu hp).1.
have [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [hinc _]]]]]]]]]]]] :=
  @induced_measure_pair_laws R g hfin mu nu hp.
have he := (hinc a b hab hca hcb).1; rewrite hzero sube0 in he.
exact: esym he.
Qed.

(** Source for [interval_increment_bound_local_finiteness]:
    supporting local finiteness for the uniqueness
    step in Federer 2.10.7, p. 174. Any
    outer measure bounded on open intervals by
    finite raw increments is finite on bounded
    half-open intervals, including empty ones. *)
Lemma interval_increment_bound_local_finiteness (R : realType) (g : R -> R)
    (mu : set R -> \bar R) (hm : is_measure mu) :
  (forall a b, (a<b)%R -> mu `]a,b[<=(g b-g a)%:E) ->
  forall a b, mu `[a,b[< +oo.
Proof.
move=> hbound a b; case: (leP a b)=> hab; last first.
  by rewrite (half_open_interval_empty (ltW hab)) (measure_empty hm) ltry.
have hwide : (a-1<b+1)%R by lra.
have hsub : `[a,b[ `<=` `](a-1)%R,(b+1)%R[.
  move=> x; rewrite /= !in_itv /= => /andP[ha hb]; apply/andP; split; lra.
exact: le_lt_trans (le_trans (measure_mono hm hsub) (hbound _ _ hwide)) (ltry _).
Qed.

(** Source for [null_endpoint_half_open_interval]:
    supporting passage from open to half-open
    intervals in the uniqueness step of Federer
    2.10.7, p. 174. Null endpoints leave
    the interval mass unchanged. *)
Lemma null_endpoint_half_open_interval (R : realType) (mu : set R -> \bar R)
    (hm : is_measure mu) (a b : R) :
  mu [set a]=0 -> mu [set b]=0 -> mu `[a,b[=mu `]a,b[.
Proof.
move=> ha hb.
have he := @measure_segment_open_interval R mu a b hm ha hb.
have hsub : `[a,b[ `<=` `[a,b].
  move=> x; rewrite /= !in_itv /= => /andP[hax hxb]; by rewrite hax (ltW hxb).
have hsuper : `]a,b[ `<=` `[a,b[.
  move=> x; rewrite /= !in_itv /= => /andP[hax hxb]; by rewrite (ltW hax) hxb.
have hu := measure_mono hm hsub; rewrite he in hu.
by apply/eqP; rewrite eq_le hu (measure_mono hm hsuper).
Qed.
