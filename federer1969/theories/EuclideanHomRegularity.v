(** Federer (1969), 3.2.47–48, pp. 282–285:
    regularity of the actual multiplication and adjoint operations
    for the Hilbert Hom metrics. Bounds are derived, not supplied
    as hypotheses in the geometric transformations. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness RealNormUP NormDifferentialUP
  HomCompositionDeterminant EuclideanHomInnerCharts EuclideanRectangularAdjoint
  EuclideanHomCompositionBound NormFiniteLinearBound NormRegularity
  NormRegularityBilinear NormRegularityLinearMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [euclidean_hom_composition_norm_class]: composing
    the two actual operator values preserves every finite class,
    as used through 3.1.11, p. 220, in
    3.2.47–48, pp. 282–285. *)
Lemma euclidean_hom_composition_norm_class (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) a b c (A:X->Prop)
    (f:X->Hom (R_n R b) (R_n R c))
    (g:X->Hom (R_n R a) (R_n R b)) k:
  norm_class hNX (inner_norm_real_norm (@euclidean_hom_inner_productP R b c)) A f k ->
  norm_class hNX (inner_norm_real_norm (@euclidean_hom_inner_productP R a b)) A g k ->
  norm_class hNX (inner_norm_real_norm (@euclidean_hom_inner_productP R a c)) A
    (fun x=>hom_comp (f x) (g x)) k.
Proof.
move=>hf hg.
exact (@norm_class_bilinear R X (Hom (R_n R b) (R_n R c))
  (Hom (R_n R a) (R_n R b)) (Hom (R_n R a) (R_n R c)) NX _ _ _ hNX
  (inner_norm_real_norm (@euclidean_hom_inner_productP R b c))
  (inner_norm_real_norm (@euclidean_hom_inner_productP R a b))
  (inner_norm_real_norm (@euclidean_hom_inner_productP R a c))
  A f g (@hom_comp R _ _ _) k (@euclidean_composition_hilbert_bilinear R a b c) hf hg).
Qed.

(** Source for [euclidean_hom_adjoint_norm_class]: the actual
    adjoint preserves every finite class, giving the inverse
    on orthogonal operators in 3.2.47–48, pp. 282–285.
    Its bound follows from finite-dimensional linearity alone. *)
Lemma euclidean_hom_adjoint_norm_class (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) m n (A:X->Prop)
    (f:X->Hom (R_n R m) (R_n R n)) k:
  norm_class hNX (inner_norm_real_norm (@euclidean_hom_inner_productP R m n)) A f k ->
  norm_class hNX (inner_norm_real_norm (@euclidean_hom_inner_productP R n m)) A
    (fun x=>euclidean_rectangular_adjoint (f x)) k.
Proof.
move=>hf.
pose L:=hom_of_linear (GRing.Linear.clone _ _ _ _ (@euclidean_rectangular_adjoint R m n) _).
have hBound:norm_bounded_linear
    (inner_norm (@euclidean_hom_inner_productP R m n))
    (inner_norm (@euclidean_hom_inner_productP R n m)) L.
  exact (@norm_finite_linear_bounded R (Hom (R_n R m) (R_n R n)) _ _ _
    (inner_norm_real_norm (@euclidean_hom_inner_productP R m n))
    (inner_norm_real_norm (@euclidean_hom_inner_productP R n m)) _ _
    (@hom_rank_one_baseP R (R_n R m) (R_n R n) m n
      (@coordinate_basis R m) (@coordinate_basisP R m)
      (@coordinate_basis R n) (@coordinate_basisP R n)) L).
exact (@norm_class_postcompose_linear R X (Hom (R_n R m) (R_n R n))
  (Hom (R_n R n) (R_n R m)) NX _ _ hNX
  (inner_norm_real_norm (@euclidean_hom_inner_productP R m n))
  (inner_norm_real_norm (@euclidean_hom_inner_productP R n m)) A f L k hBound hf).
Qed.
