(** Federer (1969), 4.1.18, p. 377: the
    smooth graph pairs (div eta,eta) on
    the original open U. Their compact
    support belongs to U, and their
    values are the original Omega representatives. *)
From mathcomp Require Import all_boot all_order all_algebra
  functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading
  CurrentDomain CurrentCoefficientNorms CurrentVectorSpaces SmoothCompactSet
  SmoothFunctionSupport SmoothCurrentDivergence CompactSummableMultivectors
  CurrentLonePairImageUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section SmoothDivergenceGraph.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Local Notation UT := (current_domain R n U).
Local Notation V d := (@current_vector_smooth_space R h2 n U hU d).
Local Notation ev d := (@current_vector_smooth_value R h2 n U hU d).
Local Notation value d := (@compact_summable_multivector_value R h2 n d U hU).
Local Notation P := (@current_lone_pair_space R h2 n m U hU).
Local Notation div := (@smooth_current_divergence R h2 n m U hU).

(** Source for [is_current_compact_smooth_divergence_pair]:
    the exact original-open graph set whose
    J-closure is ker q in Federer
    4.1.18, p. 377. Compact support,
    actual divergence and both literal Omega
    fields are specified before proving existence
    or either kernel-closure inclusion. *)
Definition is_current_compact_smooth_divergence_pair (v : P) : Prop :=
  exists eta : V m.+1, exists K : smooth_compact_set hNX U,
    @smooth_function_support R X (exterior_power X m.+1) NX hNX U
      (V m.+1) (ev m.+1) eta `<=` smooth_compact_carrier K /\
    value m v.1=(fun x : UT => ev m (div eta) (set_val x)) /\
    value m.+1 v.2=(fun x : UT => ev m.+1 eta (set_val x)).
End SmoothDivergenceGraph.
