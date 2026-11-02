(** Private existence witness for Federer (1969), 2.10.44, printed p. 202,
    scalar infimum formula. A nonempty original source gives nonempty cost
    sets; the proved scalar lower bound makes their real infima finite. The
    witness is hidden by opaque sealing. Downstream proofs use only the
    abstract upper and greatest-lower-bound laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import RealMetricBackground LipschitzUP McShaneEnvelopeUP McShaneCostBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [mcshane_envelope_exists]: direct existence of the finite
    scalar infimum envelope in 2.10.44, p. 202. Nonemptiness of S is the
    formula qualification made explicit. No density, completeness or
    boundedness of the source is required. *)
Theorem mcshane_envelope_exists (R : realType) (X : metricType R) S (f : X -> R) L :
  S !=set0 -> is_metric_lipschitz_bound S (f : X -> real_line_metric R) L ->
  exists g, is_mcshane_envelope S f L g.
Proof.
move=> [a0 ha0] hSf.
pose C x := mcshane_costs_at S f L x.
have hne x : C x !=set0.
  exists (f a0+L*mdist x a0); by exists a0.
have hlow x : lbound (C x) (f a0-L*mdist x a0).
  move=> r [a [ha ->]]; exact (@mcshane_cost_lower_bound R X S f L a0 hSf ha0 x a ha).
have hhas x : has_lbound (C x) by exists (f a0-L*mdist x a0).
exists (fun x=>inf (C x)); constructor.
- move=> x a ha; apply: (@ge_inf R (C x) (hhas x) (f a+L*mdist x a)); by exists a.
- move=> x z hz; apply: (@lb_le_inf R (C x) z (hne x)).
  move=> r [a [ha ->]]; exact: hz a ha.
Qed.
