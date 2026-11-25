(** Federer (1969), 4.1.24, p. 382: an
    original flat current admits a weak series of
    normal currents with the same K and summable
    flat sizes. Specify the actual partial sums,
    exact support and numerical majorants independently
    before choosing normal approximants. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentSpaces CurrentFlatNorm NormalCurrentsUP
  CurrentWeakSequenceLimit NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_flat_current_normal_series]: the original
    normal approximation and series argument in 4.1.24,
    p. 382, retaining every original compact index.
    It does not assume finite mass of the input. *)
Record is_flat_current_normal_series (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (T:@current_space R h2 n U hU m)
    (v:nat->@current_space R h2 n U hU m) (a:nat->R):Prop:={
  (** Source: each original normal increment retains K,
      4.1.24, p. 382. *)
  flat_current_normal_series_normal:forall i,
    @normal_currents_supported_in R h2 n U hU m K (v i);
  (** Source: the chosen scalar bounds are nonnegative,
      4.1.24, p. 382. *)
  flat_current_normal_series_nonnegative:forall i,0<=a i;
  (** Source: the original flat increment costs are summable,
      4.1.24, p. 382. *)
  flat_current_normal_series_summable:
    (nonnegative_sum setT (fun i=>(a i)%:E)< +oo)%E;
  (** Source: each normal increment is controlled in exactly F_K,
      4.1.24, p. 382. *)
  flat_current_normal_series_bound:forall i,
    (@current_flat_norm R h2 n m U hU K (v i)<=(a i)%:E)%E;
  (** Source: the original current is the weak sum of these
      actual finite normal prefixes, 4.1.24, p. 382. *)
  flat_current_normal_series_limit:
    @is_current_weak_sequence_limit R h2 n m U hU (fun k=>\sum_(i<k) v i) T
}.
