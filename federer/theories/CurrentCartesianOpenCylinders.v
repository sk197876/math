(** Federer (1969), 4.1.8, p. 360: open annihilation
    cylinders in the two original factors are open on
    A x B. Reuse the original bounded-linear preimage
    and intersection laws of 3.1.18, pp. 229–230. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLinear
  NormFiniteLinearBound NormRegularity NormRegularityOperations
  NormMetric NormOpenTopology NormBoundedLinearTopology NormLinearDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct EuclideanBlockLinearMaps EuclideanCartesianMap
  CurrentCartesianDomain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCartesianOpenCylinders.
Variable R:realType.
Variables m n:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (m+n))).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (m+n))).
Local Notation p := (@euclidean_first_block_map R m n).
Local Notation q := (@euclidean_last_block_map R m n).
Variable A:set X.
Variable B:set Y.
Hypothesis hA:forall a,A a->norm_domain_interior NX A a.
Hypothesis hB:forall b,B b->norm_domain_interior NY B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).

(** Source for [current_cartesian_first_cylinder_open]: the
    inverse image of a first-factor annihilation region is
    open within the original Cartesian domain, supporting
    the support identity of Federer 4.1.8, p. 360.
    This uses the original bounded-linear coordinate map. *)
Theorem current_cartesian_first_cylinder_open (W:set X):
  norm_open_family hNX W->norm_open_family hNZ (AB `&` [set z|W (p z)]).
Proof.
move=>hW.
have hBound:=@norm_finite_linear_bounded R Z X NZ NX hNZ hNX (m+n)%N
  (@coordinate_basis R (m+n)) (@coordinate_basisP R (m+n)) p.
rewrite /norm_open_family openE=>z [hz hWz].
apply:(@norm_domain_interior_neighbourhood R Z NZ hNZ
  (AB `&` [set z|W (p z)]) z).1.
apply:(@norm_domain_intersection_interior R Z NZ AB (fun z=>W (p z)) z (@hAB z hz)).
apply:(@norm_bounded_linear_preimage_interior R Z X NZ NX hNZ p W z hBound).
apply:(@norm_domain_interior_neighbourhood R X NX hNX W (p z)).2.
exact:(@open_nbhs_nbhs (real_norm_metric_space hNX) (p z) W (conj hW hWz)).
Qed.

(** Source for [current_cartesian_second_cylinder_open]: the
    inverse image of a second-factor annihilation region is
    open within the original Cartesian domain, supporting
    the support identity of Federer 4.1.8, p. 360.
    Empty factor domains and zero coordinate blocks are retained. *)
Theorem current_cartesian_second_cylinder_open (W:set Y):
  norm_open_family hNY W->norm_open_family hNZ (AB `&` [set z|W (q z)]).
Proof.
move=>hW.
have hBound:=@norm_finite_linear_bounded R Z Y NZ NY hNZ hNY (m+n)%N
  (@coordinate_basis R (m+n)) (@coordinate_basisP R (m+n)) q.
rewrite /norm_open_family openE=>z [hz hWz].
apply:(@norm_domain_interior_neighbourhood R Z NZ hNZ
  (AB `&` [set z|W (q z)]) z).1.
apply:(@norm_domain_intersection_interior R Z NZ AB (fun z=>W (q z)) z (@hAB z hz)).
apply:(@norm_bounded_linear_preimage_interior R Z Y NZ NY hNZ q W z hBound).
apply:(@norm_domain_interior_neighbourhood R Y NY hNY W (q z)).2.
exact:(@open_nbhs_nbhs (real_norm_metric_space hNY) (q z) W (conj hW hWz)).
Qed.
End CurrentCartesianOpenCylinders.
