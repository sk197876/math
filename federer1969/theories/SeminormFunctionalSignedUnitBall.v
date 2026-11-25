(** Federer (1969), 4.1.19, p. 377: the
    displayed supremum uses the closed J-unit
    ball of the raw L1 pair seminorm.
    The earlier seminorm unit-bound theorem includes
    nonzero null fields and supplies normalization. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals.
From Federer Require Import Hom RealNormUP RealFunctionalNormUP
  SeminormFunctionalUnitBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [seminorm_functional_signed_unit_bound]:
    the signed closed-ball bound in Federer 4.1.19,
    p. 377, implies its full homogeneous
    absolute bound. Negation gives the unsigned
    unit bound; 4.1.12's proved seminorm normalization
    handles the zero-seminorm kernel. *)
Theorem seminorm_functional_signed_unit_bound
    (R : realType) (V : lmodType R) (N : V -> R)
    (hN : is_real_seminorm N) (a : Hom V R^o) (c : R) :
  (forall v, N v <= 1 -> a v <= c) ->
  0 <= c /\ forall v, `|a v| <= c*N v.
Proof.
move=> hSigned.
have hAbsolute (v : V) (hV : N v <= 1) : `|a v| <= c.
  rewrite ler_norml; apply/andP; split; last exact: hSigned v hV.
  have hNeg : N (-v)%R <= 1 by rewrite (real_seminorm_negate hN).
  have h := hSigned (-v)%R hNeg.
  by rewrite linearN lerNl in h.
split.
- exact: (@seminorm_functional_unit_nonnegative R V N hN a c hAbsolute).
- move=> v; exact: (@seminorm_functional_unit_bound R V N hN a c
    hAbsolute v).
Qed.

(** Source for [seminorm_functional_norm_signed_unit_lub]:
    the least homogeneous norm equals the original
    signed closed-unit-ball supremum, Federer 4.1.19,
    p. 377. This is the seminorm
    version of 2.4.12's dual formula and includes
    the raw pair-space null fields. *)
Theorem seminorm_functional_norm_signed_unit_lub
    (R : realType) (V : lmodType R) (N : V -> R)
    (hN : is_real_seminorm N) (a : Hom V R^o) (n : R) :
  is_real_functional_norm N (hom_as_linear a) n ->
  (forall v, N v <= 1 -> a v <= n) /\
  forall c, (forall v, N v <= 1 -> a v <= c) -> n <= c.
Proof.
move=> hNorm; split.
- move=> v hv; apply: (le_trans (ler_norm _) _).
  apply: (le_trans (real_functional_norm_bound hNorm v) _).
  have h := ler_wpM2l (real_functional_norm_nonnegative hNorm) hv.
  by rewrite mulr1 in h.
- move=> c hSigned.
  have [hC hBound] := seminorm_functional_signed_unit_bound hN hSigned.
  exact: (real_functional_norm_least hNorm hC hBound).
Qed.
