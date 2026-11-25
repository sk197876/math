(** Federer (1969), 3.4.12, p. 339:
    the actual holomorphic germ carrier is specified by
    original local equality. Reuse the opaque local-germ
    interface of 3.4.5, p. 319, for the
    original complex-valued holomorphic representatives. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP ScalarRestriction ComplexScalarSealed NormMetric
  LocalGermUP LocalGermSealed HolomorphicGermRepresentatives.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section Germs.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Variable NX:XR->R.
Variable hNX:is_real_norm NX.
Variable a:X.

(** Source for [holomorphic_germ_space]: the original
    carrier O^C_a(X) of 3.4.12, p. 339.
    Its quotient implementation remains hidden by the local
    equality and representative laws. *)
Definition holomorphic_germ_space:choiceType:=
  @LocalGerms.space (Topological.clone (real_norm_metric_space hNX) _)
    (ComplexScalars.C R) (@holomorphic_representative_type R X NX hNX a)
    (@holomorphic_representative_value R X NX hNX a) a.

(** Source for [holomorphic_germ]: the actual original
    representative-to-germ map in 3.4.12, p. 339. *)
Definition holomorphic_germ (f:@holomorphic_representative_type R X NX hNX a):
    holomorphic_germ_space:=
  @LocalGerms.germ (Topological.clone (real_norm_metric_space hNX) _)
    (ComplexScalars.C R) (@holomorphic_representative_type R X NX hNX a)
    (@holomorphic_representative_value R X NX hNX a) a f.

(** Source for [holomorphic_germ_laws]: equality means
    exactly original local equality and every actual germ
    has an original holomorphic representative, 3.4.12,
    p. 339. No ring or dimension conclusion
    enters the independent germ specification. *)
Theorem holomorphic_germ_laws:
  @is_local_germ_space (Topological.clone (real_norm_metric_space hNX) _)
    (ComplexScalars.C R) (@holomorphic_representative_type R X NX hNX a)
    (@holomorphic_representative_value R X NX hNX a) a holomorphic_germ_space holomorphic_germ.
Proof. exact:LocalGerms.laws. Qed.
End Germs.
