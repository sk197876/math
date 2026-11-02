(** Federer (1969), 2.3.2(7), p. 75: the finite even/odd band induction. No
    measurability of the bands is assumed; their separation supplies the
    lower additivity bound. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP ExtendedRealOrderTopology MeasureUP MeasureBasic
  MeasurableSeparationUP ReciprocalLevelBands SetSequenceDisjointification NonnegativeSum
  NonnegativeSumNatPrefix NonnegativeSeriesParity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [level_separated_union_bound]: supporting use of
    the hypothesis in Federer 2.3.2(7), p. 75, finite
    induction: sets lying in two separated numerical levels have
    sum of measures bounded by the measure of their union. *)
Lemma level_separated_union_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) :
  is_measure_level_separated mu f -> forall (A B : set X) (a b : R),
  (a < b)%R -> A `<=` partial_function_preimage f [set y | y <= a%:E] ->
  B `<=` partial_function_preimage f [set y | b%:E <= y] ->
  mu A + mu B <= mu (A `|` B).
Proof.
move=> hs A B a b hab hA hB.
apply: le_trans _ (hs (A `|` B) a b hab); apply: leeD.
- apply: (@measure_mono R X mu hm)=> x hx; split; [by left|exact: hA hx].
- apply: (@measure_mono R X mu hm)=> x hx; split; [by right|exact: hB hx].
Qed.

(** Source for [test_reciprocal_level_band]: direct B_i of
    Federer 2.3.2(7), p. 75, with i=n+1 and
    partial inverse images retaining the actual function domain. *)
Definition test_reciprocal_level_band (R : realType) (X : Type)
    (f : partial_function X (extended_real_line R)) (T : set X) (r : R) n : set X :=
  T `&` partial_function_preimage f (reciprocal_level_band r n).

(** Source for [level_band_parity_prefix_bound]: finite parity estimate in
    Federer 2.3.2(7), p. 75 An arbitrary starting offset p is allowed;
    offsets 0 and 1 give the two parities. *)
Lemma level_band_parity_prefix_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) (T : set X) (r : R) p :
  is_measure_level_separated mu f -> forall N,
  nonnegative_sum [set k | (k < N)%N]
    (fun k => mu (test_reciprocal_level_band f T r (k.*2+p)%N)) <=
  mu (set_sequence_prefix (fun k => test_reciprocal_level_band f T r (k.*2+p)%N) N).
Proof.
move=> hs; elim=> [|N IH].
- by rewrite nonnegative_sum_nat_prefix_zero set_sequence_prefix_zero (measure_empty hm).
- rewrite nonnegative_sum_nat_prefix_succ; last by move=> k; exact: (@measure_nonnegative R X mu hm _).
  rewrite set_sequence_prefix_succ.
  apply: le_trans (leeD IH (lexx _)) _.
  case: N IH=> [|n] IH.
  + by rewrite set_sequence_prefix_zero (measure_empty hm) set0U add0e.
  + rewrite addeC setUC.
    apply: (@level_separated_union_bound R X mu hm f hs _ _
      (reciprocal_level_endpoint r (n.+1.*2+p)%N)
      (reciprocal_level_endpoint r (n.*2+p).+1)).
    * apply: reciprocal_level_endpoint_strict_decrease.
      by rewrite doubleS !addSn.
    * move=> x [_ [y [hy [_ hupper]]]]; exists y; by split.
    * move=> x [k hk [_ [y [hy [hlower _]]]]]; exists y; split=> //.
      apply: le_trans _ hlower; rewrite lee_fin.
      apply: reciprocal_level_endpoint_antitone.
      rewrite !ltnS leq_add2r leq_double.
      by move: hk; rewrite /= ltnS.
Qed.

(** Source for [level_band_series_bound]: direct full-series bound by twice
    mu(T) in Federer 2.3.2(7), p. 75, from the two parity estimates *)
Theorem level_band_series_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) (T : set X) (r : R) :
  is_measure_level_separated mu f ->
  nonnegative_sum setT (fun n => mu (test_reciprocal_level_band f T r n)) <= mu T + mu T.
Proof.
move=> hs; apply: nonnegative_series_parity_bound; first by move=> n; exact: (@measure_nonnegative R X mu hm _).
move=> p; apply: nonnegative_series_prefix_bound=> N.
apply: le_trans (@level_band_parity_prefix_bound R X mu hm f T r p hs N) _.
apply: (@measure_mono R X mu hm)=> x [k hk [hx _]]; exact hx.
Qed.
