(** Federer (1969), 3.1.11, p. 223: continuous
    reconstruction of a higher differential from its coordinate
    partials. The maps are specified by evaluation and bounds;
    their existence is proved using the multilinear universal laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom RealNormUP NormDifferentialUP GrassmannAbbreviations
  FiniteCoordinates EuclideanInnerProduct InnerNorm InnerNormInequalities HilbertFormCompactness
  SymmetricForms SymmetricMultiIndices SymmetricIndexBounds SymmetricDividedMonomials
  SymmetricCoordinateDualBasis ContinuousMultilinearUP ContinuousSymmetricFormAdapter
  ContinuousMultilinearScalarLift FiniteInnerSymmetricFormBounds
  NormHigherDifferentialUP NormHigherDifferentialUnique NormHigherSymmetricFormUP
  NormHigherMultiPartialUP NormHigherCoordinateExpansion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_higher_coordinate_reconstruction_exists]:
    the expansion D^k f=sum_alpha D^alpha f omega^alpha/alpha!
    yields bounded linear reconstruction maps, Federer 3.1.11,
    p. 223. Only the source is Euclidean. The target
    need not have finite dimension or be complete. *)
Theorem norm_higher_coordinate_reconstruction_exists (R : realType) n
    (Y : lmodType R) (NY : Y->R) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->R_n R n}->Hom (Z i) Y) (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space
      (inner_norm (@euclidean_inner_productP R n)) NY (@ev i) (@ZN i)) k :
  exists L : symmetric_indices n k->Hom Y (Z k),
    (forall alpha, norm_bounded_linear NY (@ZN k) (L alpha)) /\
    forall (A : R_n R n->Prop) (f : R_n R n->Y) a (z : Z k)
      (c : symmetric_indices n k->Y),
      has_norm_higher_differential (inner_norm (@euclidean_inner_productP R n))
        ev ZN A f k a z ->
      (forall alpha, has_norm_multi_partial (inner_norm (@euclidean_inner_productP R n))
        ev ZN A f alpha a (c alpha)) -> z=\sum_alpha L alpha (c alpha).
Proof.
pose NX := inner_norm (@euclidean_inner_productP R n).
have hNX := inner_norm_real_norm (@euclidean_inner_productP R n).
pose phi (alpha : symmetric_indices n k) : S_m (R_n R n) R^o k :=
  ((symmetric_multi_factorial (symmetric_indices_unbound alpha))%:R)^-1*:
    (symmetric_coordinate_basis_form (@coordinate_basisP R n) k alpha).
have hb alpha : @norm_bounded_symmetric_form R k (R_n R n) R^o NX (fun r=>`|r|) (phi alpha).
  exact (@finite_inner_symmetric_form_bounded R (R_n R n) R^o
    (@euclidean_inner_product R n) (@euclidean_inner_productP R n)
    (fun r=>`|r|) (scalar_absolute_value_norm R).1 n (@coordinate_basis R n)
    (@coordinate_basisP R n) k (phi alpha)).
have hex alpha := @continuous_multilinear_scalar_lift_exists R k (R_n R n) Y (Z k)
  NX NY hNY (@ev k) (@ZN k) (@hZ k)
  (fun u=>phi alpha [tuple u i | i<k]) (bounded_sform_finite_family (hb alpha)).
have [L hL] := choice hex.
exists L; split; first by move=>alpha; exact: (hL alpha).2.
move=>A f a z c hz hc.
have [psi hp] := norm_higher_differential_form_exists hNX hNY hZ hz.
have heval u : @ev k u z=psi [tuple u i | i<k].
  have [w [hw he]] := hp.
  by rewrite (norm_higher_differential_unique hNX hNY hZ hz hw) he.
apply: (continuous_multilinear_extensional (@hZ k))=>u.
rewrite heval linear_sum.
rewrite (@norm_higher_coordinate_expansion R n Y NX NY hNX hNY Z ev ZN hZ
  A f k a psi c hp hc).
apply: eq_bigr=>alpha _.
change (((symmetric_multi_factorial (symmetric_indices_unbound alpha))%:R)^-1*:
  ((symmetric_coordinate_basis_form (@coordinate_basisP R n) k alpha
    [tuple u i | i<k] : R)*:c alpha)=@ev k u (L alpha (c alpha))).
rewrite (hL alpha).1 /phi sform_scaleE.
change (((symmetric_multi_factorial (symmetric_indices_unbound alpha))%:R)^-1*:
  ((symmetric_coordinate_basis_form (@coordinate_basisP R n) k alpha
    [tuple u i | i<k] : R)*:c alpha)=
  (((symmetric_multi_factorial (symmetric_indices_unbound alpha))%:R)^-1*
    (symmetric_coordinate_basis_form (@coordinate_basisP R n) k alpha
      [tuple u i | i<k] : R))*:c alpha).
by rewrite scalerA.
Qed.
