(** Federer (1969), 3.4.12, p. 339:
    every original holomorphic variety is real analytic
    in its underlying real space. Use the same
    original equations through their actual squared moduli;
    reuse the real analytic scalar coordinate theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP ScalarRestriction ComplexScalarSealed ComplexScalarLaws
  ComplexModulus ComplexScalarNorm NormMetric NormAnalyticComplexSquareModulus
  FiniteAnalyticVarietyUP FiniteHolomorphicVarietyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory ComplexScalarTheory.
Local Open Scope ring_scope.

(** Source for [holomorphic_variety_real_analytic]: actual
    complex equations define the same original zero set
    as their real squared moduli, supporting the
    real-case component argument in 3.4.12, p. 339. *)
Theorem holomorphic_variety_real_analytic (R:realType)
    (X:lmodType (ComplexScalars.C R))
    (NX:restricted_space (ComplexScalars.embed R) X->R)
    (hNX:is_real_norm NX) (U S:set X):
  is_finite_holomorphic_variety hNX U S ->is_finite_analytic_variety hNX U S.
Proof.
move=>[hU [I [f [hF hZero]]]];split;first exact:hU.
exists I,(fun i x=>norm_square (f i x));split.
- move=>i;exact:norm_analytic_complex_square_modulus (hF i).1.
- move=>x;rewrite hZero;split=>[ [hx hEquations]|[hx hEquations]];split=>// i.
  + by rewrite (hEquations i) /norm_square re_zero im_zero !expr0n add0r.
  + apply/eqP;by rewrite -norm_square_eq0 (hEquations i) eqxx.
Qed.
