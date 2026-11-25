(** Federer (1969), 4.1.14, p. 370: the original F_E
    convergence and Cauchy conditions on actual currents. These
    predicates are independent of a selected sequence or completion;
    finite values and existence are subsequent conclusions. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces SmoothCompactSet CurrentFlatNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentFlatSequenceLimitUP.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set
  (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation F:=(@current_flat_norm R h2 n m U hU K).

(** Source for [is_current_flat_sequence_limit]: the displayed
    condition lim F_E(f#T-g_i#S)=0, Federer 4.1.14, p. 370.
    The original extended flat seminorm is evaluated on actual
    currents, without a prior target-flatness premise. *)
Definition is_current_flat_sequence_limit (u:nat->C) (T:C):Prop:=
  forall epsilon:R,0<epsilon->exists N:nat,forall i:nat,(N<=i)%N->
    (F ((T-u i)%R)<epsilon%:E)%E.

(** Source for [is_current_flat_cauchy_sequence]: the F_E Cauchy
    condition in Federer's first construction paragraph, 4.1.14,
    p. 370. The compact index is fixed; no normality, mass bound
    or chosen limit is included in this independent definition. *)
Definition is_current_flat_cauchy_sequence (u:nat->C):Prop:=
  forall epsilon:R,0<epsilon->exists N:nat,forall i j:nat,
    (N<=i)%N->(N<=j)%N->(F ((u i-u j)%R)<epsilon%:E)%E.
End CurrentFlatSequenceLimitUP.
