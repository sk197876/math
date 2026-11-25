(** Federer (1969), 4.1.23, p. 379:
    opaque selection of one proved original real
    polyhedral approximant. The independent flat and
    mass bounds are public; every smoothing,
    cell, partition and simplex-family selection stays hidden. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces SmoothCompactSet FlatCurrentsUP PolyhedralApproximationUP
  PolyhedralApproximationExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Module Type PolyhedralApproximationSignature.
(** Source for [value]: one actual approximating real
    polyhedral current of Federer 4.1.23, p. 379. *)
Parameter value : forall (R : realType) (h2 : (1+1:R)!=0) (n m : nat)
    (U : set (R_n R n))
    (hU : forall x, U x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (K C : smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (hKC : forall x, smooth_compact_carrier K x ->
      norm_domain_interior (inner_norm (@euclidean_inner_productP R n))
        (smooth_compact_carrier C) x)
    (T : @current_space R h2 n U hU m)
    (hFlat : @is_flat_current_supported_in R h2 n m U hU K T)
    (epsilon : R) (hEpsilon : 0<epsilon),
  @current_space R h2 n U hU m.
(** Source for [laws]: both independent printed bounds
    and the original full-hull polyhedral membership,
    Federer 4.1.23, p. 379. *)
Parameter laws : forall (R : realType) (h2 : (1+1:R)!=0) (n m : nat)
    (U : set (R_n R n))
    (hU : forall x, U x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (K C : smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (hKC : forall x, smooth_compact_carrier K x ->
      norm_domain_interior (inner_norm (@euclidean_inner_productP R n))
        (smooth_compact_carrier C) x)
    (T : @current_space R h2 n U hU m)
    (hFlat : @is_flat_current_supported_in R h2 n m U hU K T)
    (epsilon : R) (hEpsilon : 0<epsilon),
  @is_polyhedral_flat_mass_approximation R h2 n m U hU C T epsilon (@value R h2 n m U hU K C hKC T hFlat epsilon hEpsilon).
End PolyhedralApproximationSignature.
Module PolyhedralApproximation : PolyhedralApproximationSignature.
(** Source for [value]: hide every selection behind
    the proved existence theorem of 4.1.23, p. 379. *)
Definition value (R : realType) (h2 : (1+1:R)!=0) (n m : nat)
    (U : set (R_n R n))
    (hU : forall x, U x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (K C : smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (hKC : forall x, smooth_compact_carrier K x ->
      norm_domain_interior (inner_norm (@euclidean_inner_productP R n))
        (smooth_compact_carrier C) x)
    (T : @current_space R h2 n U hU m)
    (hFlat : @is_flat_current_supported_in R h2 n m U hU K T)
    (epsilon : R) (hEpsilon : 0<epsilon) :
  @current_space R h2 n U hU m := projT1 (cid (@polyhedral_flat_mass_approximation_exists R h2 n m U hU K C hKC T hFlat epsilon hEpsilon)).
(** Source for [laws]: the selected original current
    satisfies precisely the independent approximation laws,
    Federer 4.1.23, p. 379. *)
Lemma laws (R : realType) (h2 : (1+1:R)!=0) (n m : nat)
    (U : set (R_n R n))
    (hU : forall x, U x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (K C : smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (hKC : forall x, smooth_compact_carrier K x ->
      norm_domain_interior (inner_norm (@euclidean_inner_productP R n))
        (smooth_compact_carrier C) x)
    (T : @current_space R h2 n U hU m)
    (hFlat : @is_flat_current_supported_in R h2 n m U hU K T)
    (epsilon : R) (hEpsilon : 0<epsilon) :
  @is_polyhedral_flat_mass_approximation R h2 n m U hU C T epsilon (@value R h2 n m U hU K C hKC T hFlat epsilon hEpsilon).
Proof. exact: (projT2 (cid (@polyhedral_flat_mass_approximation_exists R h2 n m U hU K C hKC T hFlat epsilon hEpsilon))). Qed.
End PolyhedralApproximation.
