(** Opaque scalar envelope for Federer (1969), 2.10.44, printed p. 202.
    Expose only the chosen finite function and its infimum order laws; the
    private real-infimum witness is hidden. Source context:
    McShaneEnvelopeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets topology.
From Federer Require Import RealMetricBackground LipschitzUP McShaneEnvelopeUP McShaneEnvelopeConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module Type MCSHANE_ENVELOPE.
(** Source for [value]: abstract chosen scalar envelope
    in 2.10.44, p. 202, for a nonempty
    source and a supplied finite Lipschitz bound. *)
Parameter value : forall (R : realType) (X : metricType R) (S : set X) (f : X -> R) (L : R),
  S !=set0 -> is_metric_lipschitz_bound S (f : X -> real_line_metric R) L -> X -> R.
(** Source for [laws]: abstract infimum order laws
    of the scalar envelope in 2.10.44, p. 202.
    Agreement and Lipschitz bounds are derived separately. *)
Parameter laws : forall (R : realType) (X : metricType R) (S : set X) (f : X -> R) (L : R)
  (hne : S !=set0) (hSf : is_metric_lipschitz_bound S (f : X -> real_line_metric R) L),
  is_mcshane_envelope S f L (@value R X S f L hne hSf).
End MCSHANE_ENVELOPE.

Module McShaneEnvelope : MCSHANE_ENVELOPE.
(** Source for [value]: privately proved scalar
    envelope witness for 2.10.44, p. 202,
    hidden by opaque module ascription. *)
Definition value (R : realType) (X : metricType R) (S : set X) (f : X -> R) (L : R)
    (hne : S !=set0) (hSf : is_metric_lipschitz_bound S (f : X -> real_line_metric R) L) :=
  projT1 (cid (@mcshane_envelope_exists R X S f L hne hSf)).
(** Source for [laws]: proved order specification
    of the opaque witness for 2.10.44, p. 202. *)
Lemma laws (R : realType) (X : metricType R) (S : set X) (f : X -> R) (L : R)
    (hne : S !=set0) (hSf : is_metric_lipschitz_bound S (f : X -> real_line_metric R) L) :
  is_mcshane_envelope S f L (@value R X S f L hne hSf).
Proof. exact: (projT2 (cid (@mcshane_envelope_exists R X S f L hne hSf))). Qed.
End McShaneEnvelope.
