(** Federer (1969), 3.4.10, p. 338:
    connect the original surface coordinates (x,y,z)
    to the prescribed implicit coordinates (x,z).
    This is only a coordinate connection; boundedness
    follows from the existing finite-dimensional linear theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormFiniteLinearBound
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  HilbertFormCompactness EuclideanBlockLinearMaps EuclideanThreeBlockCoordinates
  BruhatWhitneyAuxiliaryEquation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [bruhat_whitney_physical_projection]:
    the (x,z) coordinates of the graph used
    in the example cited by 3.4.10, p. 338. *)
Definition bruhat_whitney_physical_projection (R:realType):Hom (R_n R 3) (R_n R 2).
Proof.
apply:(@HomMap R (R_n R 3) (R_n R 2)
  (fun v=>[ffun i=>if i==ord0 then v ord0 else v ord_max])).
apply/asboolP=>c x y;apply/ffunP=>i;rewrite !ffunE.
by case:(i==ord0).
Defined.

(** Source for [bruhat_whitney_physical_projection_bounded]:
    the selected coordinate map is bounded,
    supporting 3.4.10, p. 338. Reuse finite
    linear boundedness with the original coordinate basis. *)
Lemma bruhat_whitney_physical_projection_bounded (R:realType):
  norm_bounded_linear (inner_norm (@euclidean_inner_productP R 3))
    (inner_norm (@euclidean_inner_productP R 2))
    (@bruhat_whitney_physical_projection R).
Proof.
exact:(@norm_finite_linear_bounded R (R_n R 3) (R_n R 2) _ _
  (inner_norm_real_norm (@euclidean_inner_productP R 3))
  (inner_norm_real_norm (@euclidean_inner_productP R 2))
  3 (@coordinate_basis R 3) (@coordinate_basisP R 3)
  (@bruhat_whitney_physical_projection R)).
Qed.

(** Source for [bruhat_whitney_physical_projection_vertical]:
    the selected coordinates kill the omitted y direction,
    supporting the graph in 3.4.10, p. 338. *)
Lemma bruhat_whitney_physical_projection_vertical (R:realType):
  @bruhat_whitney_physical_projection R
    (@coordinate_basis R 3 (Ordinal (isT:(1<3)%N)))=0.
Proof.
apply/ffunP=>i;rewrite /bruhat_whitney_physical_projection /= !ffunE
  /coordinate_basis ?ffunE /=.
by case:(i==ord0).
Qed.

(** Source for [bruhat_whitney_physical_projection_auxiliary]:
    projecting the auxiliary parametrisation gives its exact
    first block, supporting 3.4.10, p. 338. *)
Lemma bruhat_whitney_physical_projection_auxiliary (R:realType) (v:R_n R 3):
  @bruhat_whitney_physical_projection R
    (@bruhat_whitney_auxiliary_projection R v)=@euclidean_first_block_map R 2 1 v.
Proof.
apply/ffunP=>i;have hi:(i=ord0)\/(i=ord_max).
  case: i=>[i hi];case:i hi=>[|[|i]] hi.
  - left;exact:val_inj.
  - right;exact:val_inj.
  - by move:hi.
rewrite /bruhat_whitney_physical_projection /= ffunE.
case:hi=>->.
- by rewrite eqxx euclidean_three_prefix_first
    /bruhat_whitney_auxiliary_projection ffunE /=.
- by rewrite /= euclidean_three_prefix_second
    /bruhat_whitney_auxiliary_projection ffunE /=.
Qed.
