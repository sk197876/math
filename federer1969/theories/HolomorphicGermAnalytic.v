(** Federer (1969), 3.4.12, pp. 338–339: an original
    holomorphic representative is real analytic at its centre.
    Enlarge only the outer domain of the analytic witness;
    its actual neighbourhood and function stay unchanged. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import RealNormUP ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm
  NormAnalyticUP NormAnalyticDomain HolomorphicGermRepresentatives.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_representative_analytic]: the underlying
    real analyticity required in 3.4.12, p. 338, for every
    original representative of the ring on p. 339. *)
Lemma holomorphic_representative_analytic (R:realType)
    (X:lmodType (ComplexScalars.C R)) (NX:restricted_space (ComplexScalars.embed R) X->R)
    (hNX:is_real_norm NX) a (f:@holomorphic_representative_type R X NX hNX a):
  @norm_analytic_at R (restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
    NX (@complex_modulus R) hNX (@complex_modulus_real_norm R) setT
    (holomorphic_representative_value f) a.
Proof.
have [A [ha [hF _]]]:=holomorphic_representative_holomorphic f.
exact:(@norm_analytic_at_domain_enlargement R
  (restricted_space (ComplexScalars.embed R) X)
  (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) hNX
  (@complex_modulus_real_norm R) A setT (holomorphic_representative_value f) a
  (fun x _=>Logic.I) (hF a ha)).
Qed.
