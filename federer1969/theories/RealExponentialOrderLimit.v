(** Federer (1969), 2.4.17, p. 90: scalar continuity used for the norm's
    dependence on the exponent. This supporting exponential continuity
    follows from strict order and the inverse logarithm, using only the
    sealed scalar specification. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import ExtendedRealOrderLimit RealExponentialUP RealExponentialSealed RealExponentialLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [real_exponential_order_limit]: continuity of the elementary
    exponential supporting Federer 2.4.17, p. 90 This is a derived scalar
    background law, not an extra assumption on the sealed object. *)
Lemma real_exponential_order_limit (R : realType) (u : nat -> R) (l : R) :
  extended_order_limit (fun n => (u n)%:E) l%:E ->
  extended_order_limit (fun n => (RealExponential.exponential (u n))%:E)
    (RealExponential.exponential l)%:E.
Proof.
move=> [hlo hup]; split.
- move=> a ha; case: a ha=> [a| |] ha; last first.
  + exists 0%N=> n hn; exact: ltNyr.
  + by move: ha; rewrite ltNge leey.
  have [ha0|ha0] := leP a 0%R.
  + exists 0%N=> n hn; rewrite lte_fin.
    exact: le_lt_trans ha0 (real_exponential_positive (RealExponential.laws R) _).
  have hal : (RealExponential.logarithm a)%:E < l%:E.
    rewrite lte_fin -(real_exponential_strict_order (RealExponential.laws R))
      (real_exponential_logarithm (RealExponential.laws R) ha0); exact ha.
  have [k hk] := hlo _ hal; exists k=> n hn.
  rewrite lte_fin -(real_exponential_logarithm (RealExponential.laws R) ha0)
    (real_exponential_strict_order (RealExponential.laws R)); exact: hk n hn.
- move=> b hb; case: b hb=> [b| |] hb; last first.
  + by move: hb; rewrite ltNge leNye.
  + exists 0%N=> n hn; exact: ltry.
  have hb0 : (0 < b)%R := lt_trans (real_exponential_positive (RealExponential.laws R) l) hb.
  have hlb : l%:E < (RealExponential.logarithm b)%:E.
    rewrite lte_fin -(real_exponential_strict_order (RealExponential.laws R))
      (real_exponential_logarithm (RealExponential.laws R) hb0); exact hb.
  have [k hk] := hup _ hlb; exists k=> n hn.
  rewrite lte_fin -(real_exponential_logarithm (RealExponential.laws R) hb0)
    (real_exponential_strict_order (RealExponential.laws R)); exact: hk n hn.
Qed.
