(** Federer (1969), 2.9.10, p. 157: continuous/singular derivates and
    independence of the Vitali relation. All scalar values retain partial
    domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground FunctionLatticeUP ContinuousFunctionLattice
  CoveringFamilyUP MetricDiameter MetricDiameterClosure MetricBoundedUnion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [bounded_support_continuous_functions]: direct
    lattice L in the first observation of Federer 2.9.10, p. 157:
    continuous, bounded, real-valued functions with bounded support.
    Boundedness of the nonzero set is equivalent to boundedness of
    its closure, the support, by diameter invariance under closure. *)
Definition bounded_support_continuous_functions (R : realType) (X : metricType R) : set (X -> R) :=
  [set f | continuous (f : X -> real_line_metric R) /\
    (exists M : R, forall x, `|f x|<=M) /\ metric_set_bounded [set x | f x!=0]].

(** Source for [bounded_support_continuous_support]: supporting
    identification with the printed support convention in Federer
    2.9.10, p. 157. No properness of the metric space is used. *)
Lemma bounded_support_continuous_support (R : realType) (X : metricType R) (f : X -> R) :
  bounded_support_continuous_functions f -> metric_set_bounded (closure [set x | f x!=0]).
Proof. move=> [_ [_ hb]]; by rewrite /metric_set_bounded extended_metric_diameter_closure. Qed.

(** Source for [bounded_support_continuous_zero]: zero member
    of the lattice L in Federer 2.9.10, p. 157, also for an
    empty ambient metric space. *)
Lemma bounded_support_continuous_zero (R : realType) (X : metricType R) :
  bounded_support_continuous_functions (fun _ : X => (0 : R)).
Proof.
split; first by move=> x; exact: cvg_cst.
split; first by exists 0; move=> x; rewrite normr0.
have he : [set _ : X | (0 : R)!=0]=set0 by apply/seteqP; split=> x; rewrite /= eqxx.
by rewrite he /metric_set_bounded extended_metric_diameter_empty ltry.
Qed.

(** Source for [bounded_support_continuous_lattice]: supporting
    verification of Federer's designation of L as a lattice in
    2.9.10, p. 157. All five laws of 2.5.1 are proved;
    finite unions preserve bounded supports, and truncation ceilings
    are nonnegative, as required by the original lattice definition. *)
Theorem bounded_support_continuous_lattice (R : realType) (X : metricType R) :
  is_function_lattice (@bounded_support_continuous_functions R X).
Proof.
have hc := @continuous_functions_lattice R X.
constructor.
- move=> f g [hf [[M hM] hfb]] [hg [[N hN] hgb]]; split.
  + exact (@function_lattice_add R X [set h : X -> R | continuous (h : X -> real_line_metric R)] hc f g hf hg).
  + split.
    * exists (M+N)=> x; exact: le_trans (ler_normD _ _) (lerD (hM x) (hN x)).
    * apply: le_lt_trans (extended_metric_diameter_mono _) (metric_bounded_union hfb hgb).
      move=> x /= hx; case: (pselect (f x=0))=> hf0; last by left; apply/negP=> /eqP.
      right; by move: hx; rewrite hf0 add0r.
- move=> c f hc0 [hf [[M hM] hfb]]; split.
  + exact (@function_lattice_scale R X [set h : X -> R | continuous (h : X -> real_line_metric R)] hc c f hc0 hf).
  + split.
    * exists (`|c|*M)=> x; rewrite normrM; apply: ler_wpM2l; [exact: normr_ge0|exact: hM].
    * apply: le_lt_trans (extended_metric_diameter_mono _) hfb.
      move=> x /= hx; apply/negP=> /eqP hf0; by move: hx; rewrite hf0 mulr0 eqxx.
- move=> f g [hf [[M hM] hfb]] [hg [[N hN] hgb]]; split.
  + exact (@function_lattice_minimum R X [set h : X -> R | continuous (h : X -> real_line_metric R)] hc f g hf hg).
  + split.
    * exists (Num.max M N)=> x; case: (leP (f x) (g x))=> hfg.
      -- apply: le_trans (hM x) _; by rewrite le_max lexx.
      -- apply: le_trans (hN x) _; by rewrite le_max lexx orbT.
    * apply: le_lt_trans (extended_metric_diameter_mono _) (metric_bounded_union hfb hgb).
        move=> x /= hx; case: (pselect (f x=0))=> hf0; last by left; apply/negP=> /eqP.
      right; apply/negP=> /eqP hg0; by move: hx; rewrite hf0 hg0 minxx eqxx.
- move=> c f hc0 [hf [[M hM] hfb]]; split.
  + exact (@function_lattice_truncation R X [set h : X -> R | continuous (h : X -> real_line_metric R)] hc c f hc0 hf).
  + split.
    * exists (Num.max M `|c|)=> x; case: (leP (f x) c)=> hfc.
      -- apply: le_trans (hM x) _; by rewrite le_max lexx.
      -- by rewrite le_max lexx orbT.
    * apply: le_lt_trans (extended_metric_diameter_mono _) hfb.
        move=> x /= hx; apply/negP=> /eqP hf0.
      by move: hx; rewrite hf0 (min_l hc0) eqxx.
- move=> f g [hf [[M hM] hfb]] [hg [[N hN] hgb]] hfg; split.
  + exact (@function_lattice_ordered_difference R X [set h : X -> R | continuous (h : X -> real_line_metric R)] hc f g hf hg hfg).
  + split.
    * exists (N+M)=> x; exact: le_trans (ler_normB _ _) (lerD (hN x) (hM x)).
    * apply: le_lt_trans (extended_metric_diameter_mono _) (metric_bounded_union hfb hgb).
      move=> x /= hx; case: (pselect (f x=0))=> hf0; last by left; apply/negP=> /eqP.
      right; by move: hx; rewrite hf0 subr0.
Qed.
