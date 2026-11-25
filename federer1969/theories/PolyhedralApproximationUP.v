(** Federer (1969), 4.1.23, p. 379: the
    original real polyhedral approximant has its full
    simplex hulls in C and the two separate
    printed bounds. This independent predicate contains no
    existence assumption, smoothing witness or finite-mass premise. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom ModuleQuotient RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces SmoothCompactSet CurrentMassSealed CurrentFlatNorm
  PolyhedralCurrentAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section PolyhedralApproximation.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Local Notation C := (@current_space R h2 n U hU m).
Local Notation M := (@CurrentMass.value R h2 n m U hU).

(** Source for [is_polyhedral_flat_mass_approximation]: the
    literal P in P_(m,C)(U), F_C(T-P)<=epsilon,
    M(P)<=M(T)+epsilon conclusion of Federer
    4.1.23, p. 379. Infinite input mass
    and every original degree are retained. *)
Definition is_polyhedral_flat_mass_approximation
    (K : smooth_compact_set hNX U) (T : C) (epsilon : R) (P : C) : Prop :=
  @polyhedral_current_subspace R h2 n m U hU K P /\
  (@current_flat_norm R h2 n m U hU K (T-P)%R<=epsilon%:E)%E /\
  (M P<=M T+epsilon%:E)%E.
End PolyhedralApproximation.
