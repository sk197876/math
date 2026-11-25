(** Federer (1969), 3.4.12, p. 339: the original scalar
    holomorphic coefficient fields use the established complex modulus
    norm. Align the two proofs of those same norm laws
    by ordinary propositional equality, without changing the carrier. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  ComplexModulus ComplexScalarNorm AnalyticDirectionalCoefficient HolomorphicUP HolomorphicDirectionalCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_scalar_directional_coefficient_exists]: the
    original complex-valued divided derivative field of 3.4.6,
    pp. 322–323, extended in 3.4.12, p. 339. Its
    actual derivative equation and holomorphy are both conclusions. *)
Theorem holomorphic_scalar_directional_coefficient_exists (R:realType)
    (X:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:is_complex_norm NX)
    (A:set X) (f:X->ComplexScalars.C R) k (v:X):
  is_holomorphic (complex_norm_real hNX) (@complex_modulus_real_norm R) A f ->
  exists c:X->ComplexScalars.C R,
    @is_analytic_directional_coefficient R
      (restricted_space (ComplexScalars.embed R) X)
      (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
      NX (@complex_modulus R) (complex_norm_real hNX) (@complex_modulus_real_norm R) A f k v c /\
    is_holomorphic (complex_norm_real hNX) (@complex_modulus_real_norm R) A c.
Proof.
have h:=@holomorphic_directional_coefficient_exists R X (ComplexScalars.C R)^o NX
  (@complex_modulus R) hNX (@complex_modulus_complex_norm R) A f k v.
have hProof:complex_norm_real (@complex_modulus_complex_norm R)=(@complex_modulus_real_norm R).
  exact:Prop_irrelevance.
by rewrite hProof in h.
Qed.
