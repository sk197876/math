(** Federer (1969), 4.1.23, p. 379:
    the original flat-current polyhedral approximation
    theorem on every open U, with the
    stated separate flat and mass bounds.
    Normal approximation and all subsequent density,
    cell and box constructions are proved prerequisites. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormRegularityOperations InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces SmoothCompactSet
  FlatCurrentsUP NormalCurrentsUP PolyhedralApproximationUP
  PolyhedralNormalReduction NormalPolyhedralApproximation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [polyhedral_flat_mass_approximation_exists]:
    T in F_(m,K)(U), K contained
    in Int C and epsilon>0 imply
    an actual P in P_(m,C)(U)
    with F_C(T-P)<=epsilon and
    M(P)<=M(T)+epsilon, Federer
    4.1.23, p. 379.
    There is no finite-mass,
    normality or convexity premise. *)
Theorem polyhedral_flat_mass_approximation_exists (R : realType)
    (h2 : (1+1:R)!=0) n m (U : set (R_n R n))
    (hU : forall x, U x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (K C : smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (hKC : forall x, smooth_compact_carrier K x ->
      norm_domain_interior (inner_norm (@euclidean_inner_productP R n))
        (smooth_compact_carrier C) x)
    (T : @current_space R h2 n U hU m)
    (hFlat : @is_flat_current_supported_in R h2 n m U hU K T)
    epsilon (hEpsilon : 0<epsilon) :
  exists P : @current_space R h2 n U hU m,
    @is_polyhedral_flat_mass_approximation R h2 n m U hU C T epsilon P.
Proof.
have hInclusion : smooth_compact_carrier K `<=` smooth_compact_carrier C.
  move=> x hx; exact: (@norm_domain_interior_member R (R_n R n)
    (inner_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R n))
    (smooth_compact_carrier C) x (@hKC x hx)).
apply: (@flat_current_polyhedral_normal_reduction R h2 n m U hU K C hInclusion
  _ T hFlat epsilon hEpsilon).
move=> Q hNormal delta hDelta.
exact: (@normal_polyhedral_flat_mass_approximation R h2 n m U hU K C hKC
  Q hNormal delta hDelta).
Qed.
