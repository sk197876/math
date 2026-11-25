(** Private infimum existence for Federer (1969), 3.1.1, p. 209.
    Nonzero source vectors make the unit sphere nonempty; nonnegative
    image norms give a lower bound. No attainment is asserted. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormUnitSphereBounds NormMinimumModulusUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_minimum_modulus_exists]: existence of the finite
    unit-sphere infimum in Federer 3.1.1, p. 209, for a nonzero source. *)
Theorem norm_minimum_modulus_exists (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (L : Hom X Y) :
  (exists x : X, x != 0) -> exists m, is_norm_minimum_modulus NX NY L m.
Proof.
move=> hX; have [u hu] := norm_unit_direction_exists hNX hX.
pose S := [set r : R | exists v, NX v = 1 /\ r = NY (L v)].
have hs : S !=set0 by exists (NY (L u)); exists u; split.
have hl : lbound S 0.
  move=> r [v [_ ->]]; exact: real_seminorm_nonnegative hNY.1 (L v).
have hb : has_lbound S by exists 0.
exists (inf S); split.
- exact: lb_le_inf hs hl.
- apply: (@norm_unit_lower_bound_extend R X Y NX NY hNX hNY L (inf S)).
  move=> v hv; apply: (ge_inf hb); exists v; by split.
- move=> C hC; apply: (lb_le_inf hs)=> r [v [hv ->]].
  have hh := hC v; by rewrite hv mulr1 in hh.
Qed.
