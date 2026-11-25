(** Federer (1969), 2.6.7, printed p. 121: the finite cumulative functions
    f(r)=alpha{t:t<r} and g(r)=beta{t:t<=r} for a<=r<=b. We specify their
    values only where the book requires finiteness. Values elsewhere do not
    enter the half-open interval integrals. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_cumulative_function_pair]: the two defining
    half-line equations of Federer 2.6.7, p. 121. Real
    values encode exactly the finite-measure hypothesis on [a,b]. *)
Record is_cumulative_function_pair (R : realType)
    (alpha beta : set R -> \bar R) (a b : R) (f g : R -> R) : Prop := {
  (** Source for [cumulative_lower_open_law]: the strict
      half-line convention for f in Federer 2.6.7, p. 121. *)
  cumulative_lower_open_law : forall r, a <= r -> r <= b ->
    alpha [set t | t < r]=(f r)%:E;
  (** Source for [cumulative_lower_closed_law]: the closed
      half-line convention for g in Federer 2.6.7, p. 121. *)
  cumulative_lower_closed_law : forall r, a <= r -> r <= b ->
    beta [set t | t <= r]=(g r)%:E
}.

(** Source for [cumulative_function_pair_exists]: existence of
    the functions defined in Federer 2.6.7, p. 121.
    Monotonicity shows that finiteness at b suffices for all
    r in [a,b]. The construction assigns arbitrary finite
    values outside that interval and exposes only the stated laws. *)
Theorem cumulative_function_pair_exists (R : realType)
    (alpha beta : set R -> \bar R) (ha : is_measure alpha) (hb : is_measure beta)
    (a b : R) :
  (alpha [set t | (t < b)%R] < +oo)%E -> (beta [set t | (t <= b)%R] < +oo)%E ->
  exists f g : R -> R, is_cumulative_function_pair alpha beta a b f g.
Proof.
move=> hA hB.
exists (fun r => fine (alpha [set t | t < r])),(fun r => fine (beta [set t | t <= r])).
constructor=> r har hrb.
- symmetry; apply: fineK.
  rewrite (ge0_fin_numE (measure_nonnegative ha _)).
  apply: le_lt_trans _ hA; apply: (@measure_mono R R alpha ha _ [set t | t < b])=> t ht.
  exact: lt_le_trans ht hrb.
- symmetry; apply: fineK.
  rewrite (ge0_fin_numE (measure_nonnegative hb _)).
  apply: le_lt_trans _ hB; apply: (@measure_mono R R beta hb _ [set t | t <= b])=> t ht.
  exact: le_trans ht hrb.
Qed.
