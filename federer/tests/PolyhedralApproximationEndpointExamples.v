(** Actual-space boundary checks for Federer (1969),
    4.1.23, pp. 379–380: the opaque
    approximant of the nonzero R^0 point
    cannot vanish at error below one.
    Empty opens and above-dimensional degrees retain
    their actual zero-current endpoint. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentDirac CurrentMassSealed CurrentMassFiniteAlgebra
  CurrentFlatNorm CurrentAboveDimension SmoothCompactSet FlatCurrentsUP
  PolyhedralApproximationUP PolyhedralApproximationEndpoints PolyhedralApproximationSealed.
From FedererTests Require Import FlatCurrentEndpointExamples.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section PointEndpoint.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Local Notation X := (R_n R 0%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 0%N)).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) => norm_full_domain_interior NX x).
Local Notation K := (@flat_point_singleton_index R).
Local Notation Point := (@dirac_current R h2 0%N Full hFull (0:X)).

(** Source for [polyhedral_point_index_interior]:
    the actual singleton compact is
    an ambient neighbourhood in R^0,
    checking the original K contained
    in Int C hypothesis of
    Federer 4.1.23, p. 379. *)
Lemma polyhedral_point_index_interior x :
  smooth_compact_carrier K x -> norm_domain_interior NX (smooth_compact_carrier K) x.
Proof.
move=> hx; exists 1; split; first exact: ltr01.
move=> v _; change (x+v=(0:X)).
apply/ffunP=> i; have h := ltn_ord i; by rewrite ltn0 in h.
Qed.

(** Source for [polyhedral_nonzero_point_opaque_approximation]:
    the actual opaque approximant of
    the mass-one flat point in
    R^0 is nonzero at every
    positive error below one, checking
    that the scalar and empty-product
    construction in 4.1.23 is nonvacuous. *)
Example polyhedral_nonzero_point_opaque_approximation epsilon
    (hEpsilon : 0<epsilon) (hSmall : epsilon<1) :
  let Q := @PolyhedralApproximation.value R h2 0%N 0%N Full hFull K K
    polyhedral_point_index_interior Point (@zero_dimensional_point_flat R h2)
    epsilon hEpsilon in
  @CurrentMass.value R h2 0%N 0%N Full hFull Point= 1%:E /\
    Q!=0 /\ @is_polyhedral_flat_mass_approximation R h2 0%N 0%N Full hFull
      K Point epsilon Q.
Proof.
move=> Q.
have hLaws := @PolyhedralApproximation.laws R h2 0%N 0%N Full hFull K K
  polyhedral_point_index_interior Point (@zero_dimensional_point_flat R h2)
  epsilon hEpsilon.
change (@is_polyhedral_flat_mass_approximation R h2 0%N 0%N Full hFull
  K Point epsilon Q) in hLaws.
have hNonzero : Q!=0.
  apply/eqP=> hZero; have hError := hLaws.2.1.
  rewrite hZero subr0 (@zero_dimensional_point_flat_norm_one R h2) lee_fin in hError.
  have hImpossible := lt_le_trans hSmall hError.
  by move: hImpossible; rewrite ltxx.
split; first exact: zero_dimensional_point_mass_one.
by split.
Qed.
End PointEndpoint.

(** Source for [polyhedral_empty_open_zero_approximation]:
    empty U and empty compacts
    have the literal zero approximant
    in every degree, checking the
    no-point-selection endpoint of Federer
    4.1.23, p. 379. *)
Example polyhedral_empty_open_zero_approximation (R : realType)
    (h2 : (1+1:R)!=0) n m epsilon (hEpsilon : 0<=epsilon) :
  let X := R_n R n in
  let U := (set0 : set X) in
  let hU : forall x, U x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x :=
    fun (x : X) (hx : U x) => False_rect _ hx in
  let K := @smooth_compact_empty R X (inner_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) U in
  @is_polyhedral_flat_mass_approximation R h2 n m U hU K 0 epsilon 0.
Proof.
move=> X U hU K; exact: (@polyhedral_zero_flat_mass_approximation R h2 n m U hU
  K epsilon hEpsilon).
Qed.

(** Source for [polyhedral_above_degree_opaque_zero]:
    the actual opaque value is zero
    above the ambient dimension, checking
    every natural-degree endpoint of
    Federer 4.1.23, p. 379.
    This applies the original current-space
    theorem to the sealed value itself. *)
Example polyhedral_above_degree_opaque_zero (R : realType)
    (h2 : (1+1:R)!=0) n m (hDegree : (n<m)%N)
    (U : set (R_n R n))
    (hU : forall x, U x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (K C : smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (hKC : forall x, smooth_compact_carrier K x ->
      norm_domain_interior (inner_norm (@euclidean_inner_productP R n))
        (smooth_compact_carrier C) x)
    (T : @current_space R h2 n U hU m)
    (hFlat : @is_flat_current_supported_in R h2 n m U hU K T)
    epsilon (hEpsilon : 0<epsilon) :
  @PolyhedralApproximation.value R h2 n m U hU K C hKC T hFlat epsilon hEpsilon=0.
Proof. exact: current_above_dimension. Qed.
