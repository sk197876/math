(** Federer (1969), 4.1.24, p. 382: choose
    original rectifiable decompositions of a summable
    sequence of integral-flat terms with summable actual
    mass costs. The specification retains all terms,
    the exact same K and the literal cost series.
    It assumes no attaining integral minimum. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentSpaces CurrentBoundary CurrentMassSealed NonnegativeSum
  RectifiableCurrentApproximationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_integral_flat_series_decomposition]: the
    original Ri,Si choice before the two actual
    sums in 4.1.24, p. 382. The numerical
    hypothesis is exactly summability of their actual
    mass costs, without replacing the chosen coefficients. *)
Record is_integral_flat_series_decomposition (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (v A:nat->@current_space R h2 n U hU m)
    (B:nat->@current_space R h2 n U hU m.+1):Prop:={
  (** Source: every original Ri retains R_(m,K), p. 382. *)
  integral_flat_series_rectifiable_first:forall i,
    @is_rectifiable_current_supported_in R h2 n m U hU K (A i);
  (** Source: every original Si retains R_(m+1,K), p. 382. *)
  integral_flat_series_rectifiable_second:forall i,
    @is_rectifiable_current_supported_in R h2 n m.+1 U hU K (B i);
  (** Source: the exact original increment identity, p. 382. *)
  integral_flat_series_decomposition:forall i,
    v i=A i+@current_boundary R h2 n m U hU (B i);
  (** Source: the actual joint mass series is finite, p. 382. *)
  integral_flat_series_cost_summable:
    (nonnegative_sum setT (fun i=>
      @CurrentMass.value R h2 n m U hU (A i)+
      @CurrentMass.value R h2 n m.+1 U hU (B i))< +oo)%E
}.
