(** Federer (1969), 3.4.12, pp. 338–339:
    original complex Taylor contractions agree with the
    real contractions of the same symmetric form. Reuse
    the actual repeated-tuple formula of 1.10.4, p. 46,
    including factorial normalization and above-degree zero terms. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import ScalarRestriction ComplexScalarSealed SymmetricForms
  PolynomialTaylorTerms PolynomialTaylorTermContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [complex_symmetric_taylor_restriction]: every
    original Taylor coefficient has the same actual value
    before and after scalar restriction, supporting 3.4.12,
    pp. 338–339. No derivative existence is assumed. *)
Theorem complex_symmetric_taylor_restriction (R:realFieldType)
    (X Y:lmodType (ComplexScalars.C R)) m
    (F:S_m X Y m)
    (G:S_m (restricted_space (ComplexScalars.embed R) X)
      (restricted_space (ComplexScalars.embed R) Y) m):
  (forall t,G t=F t) ->forall i (x:X) (t:i.-tuple X),
    @symmetric_taylor_term R (restricted_space (ComplexScalars.embed R) X)
      (restricted_space (ComplexScalars.embed R) Y) m i G x t=
    @symmetric_taylor_term (ComplexScalars.C R) X Y m i F x t.
Proof.
move=>hValues i x t;case:(leqP i m)=>hi.
- rewrite !symmetric_taylor_term_tuple_value // hValues.
  change (ComplexScalars.embed R ((((m-i)`!)%:R:R)^-1)*:
    F (tcast (subnKC hi) [tuple of t++[tuple x | j<m-i]])=
    (((m-i)`!)%:R:ComplexScalars.C R)^-1*:
    F (tcast (subnKC hi) [tuple of t++[tuple x | j<m-i]])).
  by rewrite fmorphV rmorph_nat.
- by rewrite !symmetric_taylor_term_above_degree // !sform_zeroE.
Qed.
