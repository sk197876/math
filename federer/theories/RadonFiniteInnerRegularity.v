(** Federer (1969), 2.5.10, p. 101, final paragraph: a positive finite
    measurable remainder contains a compact set of positive measure. This
    uses the approximation theorem in 2.2.5, p. 63. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic RadonMeasureUP RadonBorelRegularity
  RadonCompactApproximation ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [radon_finite_measurable_inner_least]: supporting
    inner-regularity formula for finite measurable sets in Federer 2.5.10,
    p. 101, from 2.2.5, p. 63 *)
Lemma radon_finite_measurable_inner_least (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hm : is_measure mu) (hr : is_radon_measure mu) (A : set T) c :
  measure_measurable mu A -> mu A < +oo ->
  (forall K, compact K -> K `<=` A -> mu K <= c) -> mu A <= c.
Proof.
move=> hA hfin hb.
have hc0 : 0 <= c.
  have hh := hb set0 compact0 (fun x hx => False_rect _ hx).
  by rewrite (measure_empty hm) in hh.
case: c hc0 hb=> [r| |] hc0 hb; [|exact: leey|by []].
apply: extended_real_reciprocal_upper_bound=> n.
have he : (0 < ((n.+1)%:R : R)^-1)%R by rewrite invr_gt0 ltr0n.
have [K [hK [hKA hk]]] := @radon_compact_approximation R T mu hm hr A _ hA hfin he.
have hKm := @radon_compact_measurable R T mu hm hr K hK.
have hi : A `&` K=K.
  apply/seteqP; split=> [x [_ hx]|x hx] //; split=> //; exact: hKA.
rewrite (hKm A) hi EFinD; apply: leeD; [exact: hb K hK hKA|exact: ltW hk].
Qed.

(** Source for [radon_positive_compact_subset]: the compact set Y used
    against maximality in Federer 2.5.10, p. 101 *)
Lemma radon_positive_compact_subset (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hm : is_measure mu) (hr : is_radon_measure mu) (A : set T) :
  measure_measurable mu A -> mu A < +oo -> 0 < mu A ->
  exists K, compact K /\ K `<=` A /\ 0 < mu K.
Proof.
move=> hA hfin hpos.
case: (pselect (exists K, compact K /\ K `<=` A /\ 0 < mu K))=> hh; first exact: hh.
exfalso; have hz : mu A <= 0.
  apply: (@radon_finite_measurable_inner_least R T mu hm hr A 0 hA hfin)=> K hK hKA.
  rewrite leNgt; apply/negP=> hk; apply: hh; exists K; by split=> //; split.
by have := lt_le_trans hpos hz; rewrite ltxx.
Qed.
