(** Federer (1969), 4.1.24, p. 382: convergence
    in the original integral-flat distance on actual
    currents. State it independently of a chosen
    sequence, carrier model or completeness construction. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentSpaces IntegralCurrentClassesUP IntegralFlatSizeSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_integral_flat_sequence_limit]: the literal
    eventual smallness of original integral-flat distances,
    4.1.24, p. 382. The difference membership
    evidence is included explicitly, and no finite
    mass is imposed on either endpoint. *)
Definition is_integral_flat_sequence_limit (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (u:nat->@current_space R h2 n U hU m)
    (T:@current_space R h2 n U hU m):Prop:=
  forall epsilon:R,0<epsilon->exists N,forall i,(N<=i)%N->
    exists hDifference:@is_integral_flat_current_supported_in R h2 n U hU m K (T-u i),
      @IntegralFlatSize.value R h2 n m U hU K (T-u i) hDifference<epsilon.
