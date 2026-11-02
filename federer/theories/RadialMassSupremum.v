(** Federer (1969), 2.10.20, pp. 181–182: bounded-ball masses exhaust the
    whole mass for a fixed-cutoff separated measure. Introduce the supremum
    of the increasing radial masses before proving it equals the total mass,
    so existence of the limit is not assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit MeasureIndexedCover MetricClosedBalls RadialShells RadialShellMeasureBounds
  NonnegativeSum NonnegativeSeriesTails ExtendedRealBounds ExtendedScaledErrorBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [unbounded_radius_order_limit]: direct order-
    topology meaning of r tending to infinity in
    2.10.20, p. 181. Both infinite limiting values
    are permitted; bounded exceptional radii are irrelevant. *)
Definition unbounded_radius_order_limit (R : realType) (f : R -> \bar R) (l : \bar R) :=
  (forall b, b<l -> exists r : R, forall u : R, (r<u)%R -> b<f u) /\
  (forall b, l<b -> exists r : R, forall u : R, (r<u)%R -> f u<b).

(** Source for [radial_mass_supremum]: supporting supremum
    representing the monotone radial limit abbreviated s
    in the proof of 2.10.20, p. 181. Negative
    radii add only the empty-ball mass zero. *)
Definition radial_mass_supremum (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (a : X) (A : set X) :=
  extended_real_sup [set b | exists r : R, b=mu (A `&` metric_closed_ball a r)].

(** Source for [radial_mass_le_supremum]: supporting
    bounded-ball upper bound in 2.10.20, pp. 181–182. *)
Lemma radial_mass_le_supremum (R : realType) (X : metricType R)
    (mu : set X -> \bar R) a A r : mu (A `&` metric_closed_ball a r)<=radial_mass_supremum mu a A.
Proof. apply: extended_real_sup_upper; by exists r. Qed.

(** Source for [radial_mass_supremum_le_total]: supporting
    easy direction of the radial equality in 2.10.20,
    p. 181, by inclusion of every truncated set in A. *)
Lemma radial_mass_supremum_le_total (R : realType) (X : metricType R)
    (mu : set X -> \bar R) a A : is_measure mu -> radial_mass_supremum mu a A<=mu A.
Proof.
move=> hm; apply: extended_real_sup_least=> b [r ->].
apply: (@measure_mono R X mu hm)=> x [hx _]; exact hx.
Qed.

(** Source for [radial_mass_has_supremum_limit]: supporting
    existence of the monotone radial limit in
    2.10.20, p. 181, prior to identifying it
    with the whole mass. No general continuity below
    of the measure is assumed. *)
Lemma radial_mass_has_supremum_limit (R : realType) (X : metricType R)
    (mu : set X -> \bar R) a A : is_measure mu ->
  unbounded_radius_order_limit (fun r => mu (A `&` metric_closed_ball a r)) (radial_mass_supremum mu a A).
Proof.
move=> hm; split.
- move=> b hb.
  have [r hr] : exists r : R, b<mu (A `&` metric_closed_ball a r).
    apply: contrapT=> hn.
    have hle : radial_mass_supremum mu a A<=b.
      apply: extended_real_sup_least=> z [r ->].
      rewrite leNgt; apply/negP=> hz; apply: hn; by exists r.
    by have := lt_le_trans hb hle; rewrite ltxx.
  exists r=> u hru; apply: lt_le_trans hr _.
  apply: (@measure_mono R X mu hm)=> x [hx hdist]; split=> //.
  exact: le_trans hdist (ltW hru).
- move=> b hb; exists 0%R=> u hu.
  exact: le_lt_trans (radial_mass_le_supremum mu a A u) hb.
Qed.

(** Source for [separated_radial_mass_supremum]: supporting
    shell-tail proof of the radial equality in
    2.10.20, pp. 181–182. If the radial supremum
    is finite, both parity subseries are finite and
    their tails tend to zero. Arbitrary target A and
    infinite total values are retained. *)
Theorem separated_radial_mass_supremum (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (a : X) (A : set X) (t : R) :
  is_measure mu -> (0<t)%R -> has_uniform_separated_union_bound mu t ->
  mu A=radial_mass_supremum mu a A.
Proof.
move=> hm ht hsep.
pose s := radial_mass_supremum mu a A.
have hbound r : mu (A `&` metric_closed_ball a r)<=s := radial_mass_le_supremum mu a A r.
have hs0 : 0<=s := le_trans (@measure_nonnegative R X mu hm (A `&` metric_closed_ball a 0%R)) (hbound 0%R).
have htotal : s<=mu A := radial_mass_supremum_le_total a A hm.
apply/eqP; rewrite eq_le htotal andbT.
change (mu A<=s).
case: (ltP s +oo)=> [hsfin|hsinf]; last exact: le_trans (leey (mu A)) hsinf.
have hsnum : s \is a fin_num by rewrite (ge0_fin_numE hs0).
pose M := fine s.
have hsval : s=M%:E by rewrite /M fineK.
rewrite hsval.
apply: (@extended_upper_bound_from_scaled_errors R (mu A) M 1%R (@ler01 R))=> eps heps.
have hterm n : 0<=mu (A `&` metric_radial_shell a t n) := @measure_nonnegative R X mu hm _.
have hseries := @radial_shell_series_bound R X mu a A t s hm ht hsep hbound.
have hsadd : s+s < +oo by rewrite hsval -EFinD ltry.
have hseriesfin := le_lt_trans hseries hsadd.
have [N hsmall] := nonnegative_series_tail_small hterm hseriesfin heps.
pose r := (N%:R*t)%R.
pose T n := A `&` metric_radial_shell a t n.
have hcover : A `<=` (A `&` metric_closed_ball a r) `|` \bigcup_(n in [set n | (N<=n)%N]) T n.
  move=> x hx; case: (pselect (metric_closed_ball a r x))=> hxr.
  - by left; split.
  - right; have [n hn] := metric_radial_shells_cover a ht x.
    have hNn : (N<=n)%N.
      rewrite leqNgt; apply/negP=> hnN; apply: hxr.
      have hu := (andP hn).2.
      have hidx : (n.+1%:R<=N%:R :> R)%R by rewrite ler_nat.
      have hh := ler_wpM2r (ltW ht) hidx.
      exact: le_trans hu hh.
    exists n=> //; by split.
have htail := @measure_indexed_cover R X [the choiceType of (nat : Type)] mu hm
  (\bigcup_(n in [set n | (N<=n)%N]) T n) [set n | (N<=n)%N] T (countableP _) (fun x hx => hx).
have hbinary := @measure_binary_cover R X mu hm A (A `&` metric_closed_ball a r)
  (\bigcup_(n in [set n | (N<=n)%N]) T n) hcover.
have hh := le_trans hbinary (leeD (hbound r) htail).
have hfinal := le_trans hh (leeD2l s (ltW hsmall)).
rewrite hsval -EFinD in hfinal.
by rewrite mul1r.
Qed.
