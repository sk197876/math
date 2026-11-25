(** Public minimum modulus for Federer (1969), 3.1.1, p. 209.
    All consequences use the abstract homogeneous lower-bound laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp lra.
From Federer Require Import Hom RealNormUP NormUnitSphereBounds
  NormMinimumModulusUP NormMinimumModulusSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_minimum_modulus]: the infimum of the differential's
    lengths on the unit sphere, Federer 3.1.1, p. 209. *)
Definition norm_minimum_modulus (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (hX : exists x : X, x != 0) (L : Hom X Y) :=
  @NormMinimumModulus.value R X Y NX NY hNX hNY hX L.

(** Source for [norm_minimum_modulus_specification]: exact infimum
    laws for the value in Federer 3.1.1, p. 209. *)
Theorem norm_minimum_modulus_specification (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (hX : exists x : X, x != 0) (L : Hom X Y) :
  is_norm_minimum_modulus NX NY L (norm_minimum_modulus hNX hNY hX L).
Proof. exact: NormMinimumModulus.laws. Qed.

(** Source for [norm_minimum_unit_approximation]: approximation from
    above of the infimum in Federer 3.1.1, p. 209, without a minimiser. *)
Theorem norm_minimum_unit_approximation (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (L : Hom X Y) m :
  is_norm_minimum_modulus NX NY L m ->
  forall e : R, 0 < e -> exists u, NX u = 1 /\ NY (L u) < m+e.
Proof.
move=> hm e he.
case: (pselect (exists u, NX u = 1 /\ NY (L u) < m+e))=> [h|h]; first exact h.
have hb : forall u, NX u = 1 -> m+e <= NY (L u).
  move=> u hu; case: (leP (m+e) (NY (L u)))=> // hh.
  exfalso; apply: h; exists u; by split.
have hall := @norm_unit_lower_bound_extend R X Y NX NY hNX hNY L (m+e) hb.
have hle := norm_minimum_greatest hm hall.
exfalso; by lra.
Qed.
