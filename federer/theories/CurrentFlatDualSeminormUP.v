(** Federer (1969), 4.1.12, p. 367: the
    original dual flat seminorm is a supremum over
    actual compact tests with F_K at most one.
    It is defined for every real linear functional,
    before continuity or support is proved. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces SmoothCompactSet ExtendedSupremumUP
  CurrentFlatFormSeminormLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentFlatDualSeminormUP.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Variable K:smooth_compact_set hNX U.
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation F := (@current_flat_test_seminorm R h2 n m U hU K).

(** Source for [current_flat_dual_values]: the original
    values T(phi) for compact tests with F_K(phi)<=1,
    Federer 4.1.12, p. 367. The functional is
    algebraically linear; continuity is not assumed. *)
Definition current_flat_dual_values (T:Hom DT R^o):set R:=
  [set a|exists phi:DT,F phi<=1 /\ T phi=a].

(** Source for [is_current_flat_dual_seminorm]: exactly
    the original extended supremum definition F_K(T),
    Federer 4.1.12, p. 367. Its possible infinite
    value, support and completeness are not hypotheses. *)
Definition is_current_flat_dual_seminorm (T:Hom DT R^o) (c: \bar R):Prop:=
  is_extended_supremum (current_flat_dual_values T) c.
End CurrentFlatDualSeminormUP.
