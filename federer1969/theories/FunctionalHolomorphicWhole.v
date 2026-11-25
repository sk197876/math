(** Federer (1969), 3.4.12, p. 339, extending 3.4.5,
    p. 321: the whole original complex space is a full-dimensional
    functional holomorphic submanifold, including dimension zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import FiniteCoordinates ScalarRestriction ComplexScalarSealed ComplexNormUP
  ComplexModulus ComplexScalarNorm HolomorphicCoordinateNorm HolomorphicUP HolomorphicArithmetic
  NormOpenDomainLaws FunctionalHolomorphicSubmanifoldUP FunctionalHolomorphicFullDimension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [functional_holomorphic_whole]: the empty equation
    family and constant nonzero auxiliary function in the full-dimensional
    convention of 3.4.5, p. 321, under 3.4.12, p. 339. *)
Theorem functional_holomorphic_whole (R:realType) n:
  @is_functional_holomorphic_submanifold R n n setT setT.
Proof.
apply:(@functional_holomorphic_full_dimension R n setT setT).2;split;first exact:openT.
exists (fun _=>1);split.
- exact:(@holomorphic_constant R (coordinate_space (ComplexScalars.C R) n) (ComplexScalars.C R)^o
    (@holomorphic_coordinate_norm R n) (@complex_modulus R)
    (complex_norm_real (@holomorphic_coordinate_norm_laws R n)) (@complex_modulus_real_norm R)
    setT 1 (fun x _=>@norm_full_domain_interior R (restricted_space (ComplexScalars.embed R) (coordinate_space (ComplexScalars.C R) n)) (@holomorphic_coordinate_norm R n) x)).
- move=>x;split;last by move=>_.
  move=>_;split;first exact:Logic.I.
  by move/eqP;rewrite oner_eq0.
Qed.
