(** Federer (1969), 4.1.24, p. 382: mass Cauchy
    sequences and mass limits of the original current
    classes. These definitions specify actual differences
    and their original masses; they choose no limit
    and impose no extra current representation. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal.
From Federer Require Import RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentMassSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section CurrentMassConvergenceUP.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation M:=(@CurrentMass.value R h2 n m U hU).

(** Source for [is_current_mass_cauchy_sequence]: the
    original Cauchy condition for the mass metric,
    used for mass completeness in 4.1.24, p. 382.
    Its two late indices are independent. *)
Definition is_current_mass_cauchy_sequence (u:nat->C):Prop:=
  forall epsilon:R,0<epsilon->exists N,forall i j,
    (N<=i)%N->(N<=j)%N->(M (u i-u j)<epsilon%:E)%E.

(** Source for [is_current_mass_sequence_limit]: the
    actual mass limit on the original current space,
    used in 4.1.24, p. 382. This is the
    same mass convergence already shown to imply
    convergence on every original test. *)
Definition is_current_mass_sequence_limit (u:nat->C) (T:C):Prop:=
  forall epsilon:R,0<epsilon->exists N,forall i,
    (N<=i)%N->(M (T-u i)<epsilon%:E)%E.
End CurrentMassConvergenceUP.
