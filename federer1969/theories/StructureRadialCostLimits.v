(** Federer (1969), 3.3.4, p. 289:
    the original coordinate-cone upper limits
    have the corrected countable-tail form
    proved in 3.3.2, pp. 287–288.
    This supporting order proof keeps all
    original positive real radii and apertures. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealBounds PositiveRadiusLimits
  ExtendedRealReciprocalBounds StructureLimsupLevels.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_radial_cost_supremum]:
    the literal radius supremum used to
    define B_j and C_j in Federer
    3.3.4, p. 289, for a general
    original radius/aperture cost family. *)
Definition structure_radial_cost_supremum (R:realType) (P:Type)
    (f:P->R->R->\bar R) (delta:R) (x:P) (s:R):=
  extended_real_sup [set v|exists r:R,0<r<delta /\ v=f x r s].

(** Source for [structure_radial_cost_upper_limitE]:
    supporting the Borel B_j/C_j assertion
    in Federer 3.3.4, p. 289, via
    the published corrected 3.3.2 tail
    formula, erratum pp. 5–6. The
    full positive-aperture upper limit equals
    the cofinal countable-tail value exactly. *)
Theorem structure_radial_cost_upper_limitE (R:realType) (P:Type)
    (f:P->R->R->\bar R) (delta:R) (x:P):
  positive_radius_upper_limit (structure_radial_cost_supremum f delta x)=
    structure_tail_upper_limit f delta x.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply:extended_real_inf_greatest=>b [i ->].
  have hi:0<((i.+1)%:R:R)^-1 by rewrite invr_gt0 ltr0n.
  apply:le_trans (positive_radius_upper_le_level (structure_radial_cost_supremum f delta x) hi) _.
  apply:extended_real_sup_least=>v [s [hs ->]].
  apply:extended_real_sup_least=>q [r [hr ->]].
  apply:extended_real_sup_upper; by exists r,s.
- apply:extended_real_inf_greatest=>b [d [hd ->]].
  have [i hi]:=positive_reciprocal_nat_small hd.
  have hLevel:(structure_tail_upper_limit f delta x<=structure_tail_supremum f delta i x)%E.
    apply:extended_real_inf_lower; by exists i.
  apply:le_trans hLevel _.
  apply:extended_real_sup_least=>v [r [s [hr [/andP [hs hsSmall] ->]]]].
  have hValue:(f x r s<=structure_radial_cost_supremum f delta x s)%E.
    apply:extended_real_sup_upper; by exists r.
  apply:le_trans hValue _; apply:extended_real_sup_upper.
  exists s; split=>//; apply/andP; split=>//; exact:lt_trans hsSmall hi.
Qed.
