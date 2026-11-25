(** Federer (1969), 2.5.2, p. 92, and 2.5.3, p. 94: two-sided estimates for
    the L regular measure phi(S)=inf{lim lambda(f_n)} over suiting
    sequences. A positive lattice function at least one on S bounds phi(S)
    from above. A measure nu with the level estimate t nu{f>t} <= lambda(f)
    on L+ and continuous along increasing sequences of arbitrary sets is
    dominated by phi. These supporting consequences of the envelope laws are
    used to identify phi on the strips of Federer 2.5.11, p. 102, and in
    2.5.4, p. 95. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import FunctionLatticeUP MonotoneDaniellIntegralUP MonotoneDaniellIntegralLaws
  DaniellCoverUP ExtendedRealBoundsUP MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [daniell_envelope_hull_bound]: supporting upper
    estimate from the envelope formula of Federer 2.5.2, p. 92:
    the constant sequence h suits every set on which h is at least one. *)
Lemma daniell_envelope_hull_bound (R : realType) (X : Type) (L : set (X -> R))
    (A : (X -> R) -> R) (mu : set X -> \bar R) :
  is_daniell_cover_envelope L A mu -> forall (S : set X) (h : X -> R),
  positive_function_lattice L h -> (forall x, S x -> (1 <= h x)%R) -> mu S <= (A h)%:E.
Proof.
move=> henv S h hh hS.
apply: (daniell_cover_lower henv (f := fun _ => h)).
- split; first by move=> n.
  split; first by move=> n m _ x; exact: lexx.
  move=> x hx r hr; exists 0%N; exact: lt_le_trans hr (hS x hx).
- split; first by move=> z [n ->]; exact: lexx.
  by move=> d hd; apply: hd; exists 0%N.
Qed.

(** Source for [real_scaled_bound_limit]: supporting real inequality
    for the lower envelope estimate of Federer 2.5.2, p. 92: a
    nonnegative s with t s <= c for every t in (0,1) satisfies s <= c. *)
Lemma real_scaled_bound_limit (R : realType) (s c : R) :
  (0 <= s)%R -> (forall t : R, (0 < t < 1)%R -> (t * s <= c)%R) -> (s <= c)%R.
Proof.
move=> hs0 hreal.
have h2 : (0 < (2^-1 : R) < 1)%R.
  by rewrite invr_gt0 ltr0n /= invf_lt1 ?ltr0n // ltr1n.
rewrite leNgt; apply/negP=> hlt.
have hc0 : (0 <= c)%R.
  apply: le_trans (hreal _ h2); apply: mulr_ge0=> //.
  by rewrite invr_ge0 ler0n.
have hs0pos : (0 < s)%R by exact: le_lt_trans hc0 hlt.
pose t := ((c + s) / (2 * s))%R.
have ht : (0 < t < 1)%R.
  apply/andP; split.
  - by rewrite divr_gt0 ?mulr_gt0 ?ltr0n // ltr_wpDl.
  - by rewrite ltr_pdivrMr ?mulr_gt0 ?ltr0n // mul1r mulr_natl mulr2n ltrD2r.
have := hreal t ht.
rewrite /t invfM mulrA -mulrA mulVf ?mulr1; last exact: lt0r_neq0.
by rewrite ler_pdivrMr ?ltr0n // mulr_natr mulr2n lerD2l leNgt hlt.
Qed.

(** Source for [daniell_envelope_dominates]: supporting lower
    estimate from the envelope formula of Federer 2.5.2, p. 92.
    If a suiting sequence of S has limiting cost c, then for t<1 the
    strict levels {f_n>t} increase to a set containing S, and the
    level estimate bounds nu of each level by lambda(f_n)/t <= c/t.
    Continuity of nu along the levels and t to one give nu(S) <= c. *)
Theorem daniell_envelope_dominates (R : realType) (X : choiceType) (L : set (X -> R))
    (A : (X -> R) -> R) (mu nu : set X -> \bar R)
    (hL : is_function_lattice L) (hA : is_monotone_daniell_integral L A)
    (henv : is_daniell_cover_envelope L A mu) (hn : is_measure nu) :
  (forall f t, positive_function_lattice L f -> (0 < t)%R ->
    t%:E * nu [set x | (t < f x)%R] <= (A f)%:E) ->
  (forall (V : nat -> set X) c, (forall n m, (n <= m)%N -> V n `<=` V m) ->
    (forall n, nu (V n) <= c) -> nu (\bigcup_n V n) <= c) ->
  forall S, nu S <= mu S.
Proof.
move=> hcheb hcont S.
apply: (daniell_cover_greatest henv)=> f c [hpos [hmono hlim]] hcost.
have hfc : forall n, (A (f n))%:E <= c.
  by move=> n; apply: (extended_real_supremum_upper hcost); exists n.
have hc0 : 0 <= c.
  apply: le_trans (hfc 0%N); rewrite lee_fin.
  exact: (@monotone_daniell_integral_nonnegative R X L A hL hA (f 0%N) (hpos 0%N).1 (hpos 0%N).2).
have hbound : forall t : R, (0 < t < 1)%R -> t%:E * nu S <= c.
  move=> t /andP[ht0 ht1].
  pose V := fun n => [set x | (t < f n x)%R].
  have hV : forall n m, (n <= m)%N -> V n `<=` V m.
    by move=> n m hnm x hx; exact: lt_le_trans hx (hmono n m hnm x).
  have hSV : S `<=` \bigcup_n V n.
    by move=> x hx; have [n hn'] := hlim x hx t ht1; exists n.
  rewrite -lee_pdivlMl //.
  apply: le_trans (measure_mono hn hSV) _.
  apply: hcont hV _ => n.
  rewrite lee_pdivlMl //.
  exact: le_trans (hcheb (f n) t (hpos n) ht0) (hfc n).
case: (pselect (c = +oo))=> [->|hcinf]; first exact: leey.
have [c0 hc] : exists c0 : R, c = c0%:E.
  case: c hc0 hcinf {hfc hbound hcost}=> [c0 _ _|_ h|h _].
  - by exists c0.
  - by case: (h erefl).
  - by move: h; rewrite leeNy_eq.

rewrite hc in hbound *.
have h2 : (0 < (2^-1 : R) < 1)%R.
  by rewrite invr_gt0 ltr0n /= invf_lt1 ?ltr0n // ltr1n.
have hfin : nu S < +oo.
  have := hbound _ h2; rewrite -lee_pdivlMl ?invr_gt0 ?ltr0n // -EFinM=> hle.
  exact: le_lt_trans hle (ltry _).
have [s0 hs] : exists s0 : R, nu S = s0%:E.
  have := measure_nonnegative hn S.
  case: (nu S) hfin=> [s0 _ _|h _|_ h].
  - by exists s0.
  - by rewrite ltxx in h.
  - by rewrite leeNy_eq in h.
rewrite hs lee_fin; apply: real_scaled_bound_limit.
- by have := measure_nonnegative hn S; rewrite hs lee_fin.
- by move=> t ht; have := hbound t ht; rewrite hs -EFinM lee_fin.
Qed.
