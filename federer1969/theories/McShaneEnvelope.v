(** Public scalar infimum envelope for Federer (1969), 2.10.44, printed p.
    202. Use only the opaque order laws; the printed infimum formula,
    agreement and Lipschitz bound are consequences. Source context:
    McShaneEnvelopeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import RealMetricBackground LipschitzUP McShaneEnvelopeUP
  McShaneEnvelopeLaws McShaneEnvelopeSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [mcshane_envelope]: abstract chosen scalar extension envelope
    in 2.10.44, p. 202. The nonempty-source qualification applies to the
    infimum formula. *)
Definition mcshane_envelope (R : realType) (X : metricType R) S (f : X -> R) L
    (hne : S !=set0) (hSf : is_metric_lipschitz_bound S (f : X -> real_line_metric R) L) :=
  @McShaneEnvelope.value R X S f L hne hSf.

(** Source for [mcshane_envelope_specification]: proved
    abstract infimum laws of 2.10.44, p. 202,
    without exposing the real-infimum implementation. *)
Theorem mcshane_envelope_specification (R : realType) (X : metricType R) S (f : X -> R) L
    (hne : S !=set0) (hSf : is_metric_lipschitz_bound S (f : X -> real_line_metric R) L) :
  is_mcshane_envelope S f L (@mcshane_envelope R X S f L hne hSf).
Proof. exact: McShaneEnvelope.laws. Qed.
