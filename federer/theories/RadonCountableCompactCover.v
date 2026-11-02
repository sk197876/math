(** Federer (1969), 2.5.10, p. 101: every set of finite Radon measure is
    almost covered by countably many compact sets. The finite set need not
    be measurable. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostBasic BorelRegularMeasureUP
  RadonMeasureUP RadonBorelRegularity RadonCompactApproximation ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [radon_finite_countable_compact_cover]: supporting assertion
    in Federer 2.5.10, p. 101. A Borel hull and compact approximations with
    errors 1/(n+1) give an actual sequence; no measurability of the original
    set is required. *)
Theorem radon_finite_countable_compact_cover (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hm : is_measure mu) (hr : is_radon_measure mu) (A : set T) :
  mu A < +oo -> exists K : nat -> set T,
    (forall n, compact (K n)) /\ mu (A `\` (\bigcup_n K n))=0.
Proof.
move=> hfin.
have hbr := radon_borel_regular hm hr.
have [B [hAB [hB he]]] := borel_regular_cover hbr A.
have hBm := borel_regular_borel_measurable hm hbr hB.
have hBfin : mu B < +oo by rewrite -he.
have hex n : exists K, compact K /\ K `<=` B /\ mu (B `\` K) < (((n.+1)%:R : R)^-1)%:E.
  apply: (@radon_compact_approximation R T mu hm hr B _ hBm hBfin).
  by rewrite invr_gt0 ltr0n.
pose K n := projT1 (cid (hex n)).
have hK n := projT2 (cid (hex n)).
exists K; split; first by move=> n; exact: (hK n).1.
apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
apply: (@extended_real_reciprocal_upper_bound R _ 0)=> n.
rewrite add0r.
apply: le_trans _ (ltW (hK n).2.2).
apply: (@measure_mono R T mu hm)=> x [hx hn]; split; first exact: hAB.
move=> hk; apply: hn; by exists n.
Qed.
