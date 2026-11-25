(** Federer (1969), 2.10.44, printed p. 202: the scalar infimum envelope
    agrees with the original map and has the same supplied Lipschitz bound.
    Derive these conclusions from its abstract order laws, independently of
    an infimum witness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets topology lra.
From Federer Require Import RealMetricBackground LipschitzUP McShaneEnvelopeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [mcshane_envelope_unique]: supporting
    uniqueness of the infimum envelope in 2.10.44,
    p. 202. The comparison uses only the
    greatest-lower-bound laws, not an implementation. *)
Lemma mcshane_envelope_unique (R : realType) (X : metricType R) S f L g h :
  @is_mcshane_envelope R X S f L g -> is_mcshane_envelope S f L h -> g=h.
Proof.
move=> hg hh; apply: funext=> x; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (@mcshane_envelope_greatest_law R X S f L h hh x (g x)).
  move=> a ha; exact (@mcshane_envelope_upper_law R X S f L g hg x a ha).
- apply: (@mcshane_envelope_greatest_law R X S f L g hg x (h x)).
  move=> a ha; exact (@mcshane_envelope_upper_law R X S f L h hh x a ha).
Qed.

(** Source for [mcshane_envelope_infimum]: direct infimum formula in
    2.10.44, p. 202, derived from the order specification for a nonempty
    source. *)
Theorem mcshane_envelope_infimum (R : realType) (X : metricType R) S f L g :
  S !=set0 -> @is_mcshane_envelope R X S f L g ->
  forall x, g x=inf (mcshane_costs_at S f L x).
Proof.
move=> hne hg x.
pose C := mcshane_costs_at S f L x.
have hCne : C !=set0.
  have [a ha] := hne; exists (f a+L*mdist x a); by exists a.
have hlow : lbound C (g x).
  move=> r [a [ha ->]]; exact (@mcshane_envelope_upper_law R X S f L g hg x a ha).
have hhas : has_lbound C by exists (g x).
apply/eqP; rewrite eq_le; apply/andP; split.
- exact: lb_le_inf hCne hlow.
- apply: (@mcshane_envelope_greatest_law R X S f L g hg x (inf C)).
  move=> a ha; apply: (@ge_inf R C hhas (f a+L*mdist x a)); by exists a.
Qed.

(** Source for [mcshane_envelope_agreement]: direct g restricted to S equals
    f in 2.10.44, p. 202 *)
Theorem mcshane_envelope_agreement (R : realType) (X : metricType R) S (f : X -> R) L g :
  is_metric_lipschitz_bound S (f : X -> real_line_metric R) L ->
  is_mcshane_envelope S f L g -> forall x, S x -> g x=f x.
Proof.
move=> hSf hg x hx.
have hup := @mcshane_envelope_upper_law R X S f L g hg x x hx.
rewrite mdistxx mulr0 addr0 in hup.
have hlow : f x<=g x.
  apply: (@mcshane_envelope_greatest_law R X S f L g hg x (f x)).
  move=> a ha; have hh := hSf.2 x a hx ha.
  rewrite real_line_metric_distanceE in hh.
  have h := le_trans (ler_norm (f x-f a)) hh.
  by move: h; rewrite lerBlDr addrC.
by apply/eqP; rewrite eq_le hup hlow.
Qed.

(** Source for [mcshane_envelope_lipschitz]: direct global Lipschitz bound
    of the infimum envelope in 2.10.44, p. 202 The triangle inequality and
    the envelope order laws suffice once L is nonnegative. *)
Theorem mcshane_envelope_lipschitz (R : realType) (X : metricType R) S f (L : R) g :
  0<=L -> @is_mcshane_envelope R X S f L g ->
  is_metric_lipschitz_bound setT (g : X -> real_line_metric R) L.
Proof.
move=> hL hg.
have hdiff x y : g x-g y<=L*mdist x y.
  have hlo : g x-L*mdist x y<=g y.
    apply: (@mcshane_envelope_greatest_law R X S f L g hg y (g x-L*mdist x y)).
    move=> a ha.
    have hu := @mcshane_envelope_upper_law R X S f L g hg x a ha.
    have ht := ler_wpM2l hL (metric_triangle x y a).
    rewrite mulrDr in ht; nra.
  nra.
split=> // x y _ _.
rewrite real_line_metric_distanceE ler_norml; apply/andP; split.
- have hh := hdiff y x; rewrite metric_sym in hh.
  by rewrite -opprB lerN2.
- exact: hdiff x y.
Qed.
