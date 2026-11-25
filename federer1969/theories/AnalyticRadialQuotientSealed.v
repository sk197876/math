(** Supporting Federer (1969), 3.4.8(5), p. 328:
    actual analytic radial quotients behind their
    independently specified derivative interface. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP AnalyticGermRing AnalyticRadialQuotientUP AnalyticRadialQuotientExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type AnalyticRadialQuotientSignature.
(** Source for [map]: the radial Taylor quotient
    supporting the expanded ideal-power argument for
    3.4.8(5), p. 328. *)
Parameter map:forall (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX) a,
  @analytic_germ_ring R X NX hNX a->X->@analytic_germ_ring R X NX hNX a.
(** Source for [laws]: the actual derivative contraction
    equations, supporting 3.4.8(5), p. 328, from
    Taylor's formula in 3.1.24, pp. 238–239. *)
Parameter laws:forall (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX) a
  (alpha:@analytic_germ_ring R X NX hNX a) v,
  is_analytic_radial_quotient alpha v (@map R X NX hNX a alpha v).
End AnalyticRadialQuotientSignature.
Module AnalyticRadialQuotient:AnalyticRadialQuotientSignature.
(** Source for [map]: private selection from proved
    actual existence, supporting 3.4.8(5), p. 328. *)
Definition map (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX) a
  (alpha:@analytic_germ_ring R X NX hNX a) v:=
  projT1 (cid (@analytic_radial_quotient_exists R X NX hNX a alpha v)).
(** Source for [laws]: the hidden actual quotient
    satisfies the original independent derivative laws,
    supporting 3.4.8(5), p. 328. *)
Lemma laws (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX) a
  (alpha:@analytic_germ_ring R X NX hNX a) v:
  is_analytic_radial_quotient alpha v (@map R X NX hNX a alpha v).
Proof. exact:(projT2 (cid (@analytic_radial_quotient_exists R X NX hNX a alpha v))). Qed.
End AnalyticRadialQuotient.
