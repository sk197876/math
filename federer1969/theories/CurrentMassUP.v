(** Federer (1969), 4.1.7, p. 358: the
    original mass is the supremum of the
    current on compact test forms with global
    comass at most one. This independent
    definition permits infinite mass. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentGlobalComassSealed ExtendedSupremumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentMassUP.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation C := (@current_space R h2 n U hU m).
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation ev := (@current_test_value R h2 n U hU m).
Local Notation action := (@current_value R h2 n U hU m).

(** Source for [current_mass_values]: the original
    set of T(phi) with phi in D^m(U)
    and M(phi)<=1, Federer 4.1.7,
    p. 358, second displayed mass definition. *)
Definition current_mass_values (T:C):set R:=
  [set a|exists phi:DT,(@CurrentGlobalComass.value R h2 n m U (ev phi)<=1)%E /\action T phi=a].

(** Source for [is_current_mass]: the original
    least-upper-bound definition of M(T),
    Federer 4.1.7, p. 358. *)
Definition is_current_mass (T:C) (c: \bar R):Prop:=
  is_extended_supremum (current_mass_values T) c.
End CurrentMassUP.
