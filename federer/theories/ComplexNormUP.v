(** Federer (1969), 3.4.12, p. 338:
    complex Banach spaces use their original complex
    norm and the same underlying real metric.
    These independent norm laws assume no analyticity,
    derivative, division or dimension conclusion. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP ScalarRestriction ComplexScalarSealed ComplexModulus.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_complex_norm]: the complex norm
    in the original Banach-space hypothesis of 3.4.12,
    p. 338. Its underlying real norm and
    exact complex scalar law are specified independently. *)
Record is_complex_norm (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R):Prop:={
  (** Source for [complex_norm_real]: the underlying real
      norm in the complex Banach spaces of 3.4.12, p. 338. *)
  complex_norm_real:is_real_norm (fun x:restricted_space (ComplexScalars.embed R) X=>NX x);
  (** Source for [complex_norm_scale]: scaling by the
      complex absolute value, in the original normed
      spaces of 3.4.12, p. 338. *)
  complex_norm_scale:forall c x,NX (c*:x)=complex_modulus c*NX x
}.
