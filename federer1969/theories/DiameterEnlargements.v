(** Diametric enlargements in Federer (1969), 2.10.18, p. 180: union of the
    members meeting S with diameter at most twice diam S. The triangle
    inequality bounds their union by five times diam S. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology ring.
From Federer Require Import MetricDiameterUP MetricDiameter WeightedEnlargements DiametricRegularityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [diameter_enlargement]: direct definition
    of the displayed hat S in 2.10.18, p. 180.
    Extended diameters allow unbounded members of F. *)
Definition diameter_enlargement (R : realType) (X : metricType R)
    (F : set (set X)) (S : set X) : set X :=
  \bigcup_(T in [set T | F T /\ T `&` S <> set0 /\
    extended_metric_diameter T<=2%:E*extended_metric_diameter S]) T.

(** Source for [diameter_enlargement_contains]: supporting
    containment S subset hat S for 2.10.18, p. 180;
    a nonempty S is one of the sets in its own union. *)
Lemma diameter_enlargement_contains (R : realType) (X : metricType R)
    (F : set (set X)) S : F S -> S `<=` diameter_enlargement F S.
Proof.
move=> hS x hx; exists S=> //; split=> //; split.
- move=> he; have hxx : (S `&` S) x by split.
  by rewrite he in hxx.
- have hn := metric_diameter_nonnegative (extended_metric_diameter_specification S).
  have h12 : (1 : \bar R)<=2%:E by rewrite lee_fin ler1n.
  have h := lee_wpmul2r hn h12.
  by rewrite mul1e in h.
Qed.

(** Source for [weighted_enlargement_diameter_subset]: supporting
    identification of the 2.8.6 selection enlargements with
    hat S in the proof of 2.10.18(1), p. 180.
    Only the selected bounded subfamily needs real weights. *)
Lemma weighted_enlargement_diameter_subset (R : realType) (X : metricType R)
    (P F : set (set X)) (d : set X -> R) S :
  P `<=` F -> is_real_diameter_weight P d -> P S ->
  weighted_enlargement P d 2 S `<=` diameter_enlargement F S.
Proof.
move=> hPF hd hS x [T [hT [hmeet hbound]] hx].
exists T=> //; split; first exact: hPF.
split=> //.
have hTdiam := metric_diameter_unique (extended_metric_diameter_specification T) (hd T hT).
have hSdiam := metric_diameter_unique (extended_metric_diameter_specification S) (hd S hS).
by rewrite hTdiam hSdiam -EFinM lee_fin.
Qed.

(** Source for [diameter_enlargement_bound]: supporting small-diameter
    estimate used implicitly in the fine family of 2.10.18(1), p. 180 Two
    enlarged members can be joined through S, giving 2r+r+2r. This is an
    auxiliary bound, not a new hypothesis on Federer's family. *)
Lemma diameter_enlargement_bound (R : realType) (X : metricType R)
    (F : set (set X)) S (r : R) :
  (0<=r)%R -> extended_metric_diameter S<=r%:E ->
  extended_metric_diameter (diameter_enlargement F S)<=(5*r)%:E.
Proof.
move=> hr hS; apply: (metric_diameter_least (extended_metric_diameter_specification _)).
- by rewrite lee_fin mulr_ge0 ?ler0n.
- move=> x y [T [hT [hTS hTd]] hx] [U [hU [hUS hUd]] hy].
  have [a [haT haS]] : exists a, (T `&` S) a.
    apply: (set0P _).1; by apply/eqP.
  have [b [hbU hbS]] : exists b, (U `&` S) b.
    apply: (set0P _).1; by apply/eqP.
  have h2 : (0<=2%:E :> \bar R) by rewrite lee_fin ler0n.
  have hTb := le_trans hTd (lee_wpmul2l h2 hS).
  have hUb := le_trans hUd (lee_wpmul2l h2 hS).
  have hxa := le_trans (metric_diameter_upper (extended_metric_diameter_specification T) hx haT) hTb.
  have hby := le_trans (metric_diameter_upper (extended_metric_diameter_specification U) hbU hy) hUb.
  have hab := le_trans (metric_diameter_upper (extended_metric_diameter_specification S) haS hbS) hS.
  rewrite -EFinM lee_fin in hxa hby; rewrite lee_fin in hab.
  have htri := le_trans (metric_triangle x a y)
    (lerD (lexx _) (metric_triangle a b y)).
  rewrite lee_fin; apply: le_trans htri _.
  have hh := lerD hxa (lerD hab hby).
  have he : (2*r+(r+2*r)=5*r)%R by ring.
  by rewrite he in hh.
Qed.
