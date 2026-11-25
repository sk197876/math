(** Federer (1969), 4.1.10, p. 364: smoothness of the
    original affine contraction. Reuse the bounded linear and bilinear
    calculus of 3.1.11 and the original Euclidean block maps. The target
    is the whole ambient space, including for an arbitrary open source. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  NormRegularity NormRegularityOperations NormRegularityBilinear NormFiniteLinearBound
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct EuclideanOneCoordinate EuclideanBlockCoordinates
  EuclideanBlockLinearMaps EuclideanScalarCoordinateMaps
  CurrentCartesianDomain CurrentHomotopyUP CurrentHomotopyDomain
  CurrentConeHomotopyUP CurrentConeHomotopySealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section CurrentConeHomotopyClass.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation Z := (R_n R (1+n)%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (1+n)%N)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N)).
Local Notation hAbs := (@scalar_absolute_value_norm R).
Local Notation p := (@euclidean_first_block_map R 1%N n).
Local Notation q := (@euclidean_last_block_map R 1%N n).
Local Notation time := (hom_comp (@euclidean_scalar_coordinate_map R 1%N ord0) p).
Variable u : X.
Local Notation h := (@CurrentConeHomotopy.value R n u).

(** Source for [current_cone_homotopy_coordinates]: the affine
    formula of Federer 4.1.10, p. 364, at an arbitrary point of the
    original time-space product. This follows from the public law. *)
Lemma current_cone_homotopy_coordinates z :
  h z = (1-time z) *: u + time z *: q z.
Proof.
have hz : @euclidean_block_join R 1%N n
    (@euclidean_one_embed R (time z), q z) = z.
  change (@euclidean_block_join R 1%N n
    (@euclidean_one_embed R (@euclidean_one_project R (p z)),q z)=z).
  by rewrite euclidean_one_projectK; exact: euclidean_block_splitK.
by rewrite -{1}hz CurrentConeHomotopy.laws.
Qed.

Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Local Notation A := (fun _ : R => True).
Local Notation AU := (@current_homotopy_product_domain R n A U).

(** Source for [current_cone_time_interval]: all real times form
    an admissible original interval for the ambient contraction,
    supporting Federer 4.1.10, p. 364. *)
Lemma current_cone_time_interval : @is_homotopy_parameter_interval R A.
Proof. constructor; first exact: openT; by []. Qed.

(** Source for [current_cone_homotopy_smooth]: the original affine
    contraction is smooth on R times U, supporting Federer 4.1.10,
    p. 364. No assertion that all real-time images lie in U is made. *)
Theorem current_cone_homotopy_smooth :
  norm_class_all_orders hNZ hNX AU h.
Proof.
have hAU := @current_cartesian_domain_open R 1%N n
  (@current_homotopy_time_domain R A) U
  (@current_homotopy_time_domain_open R A current_cone_time_interval) hU.
have hTime : norm_bounded_linear NZ (fun t : R^o => `|t|) time.
  exact: (@norm_finite_linear_bounded R Z R^o NZ (fun t : R^o => `|t|)
    hNZ hAbs (1+n)%N (@coordinate_basis R (1+n)%N)
    (@coordinate_basisP R (1+n)%N) time).
have hLast : norm_bounded_linear NZ NX q.
  exact: (@norm_finite_linear_bounded R Z X NZ NX hNZ hNX (1+n)%N
    (@coordinate_basis R (1+n)%N) (@coordinate_basisP R (1+n)%N) q).
move=> k.
have ht := @norm_class_linear R Z R^o NZ (fun t : R^o => `|t|)
  hNZ hAbs AU time k hAU hTime.
have hx := @norm_class_linear R Z X NZ NX hNZ hNX AU q k hAU hLast.
have hOne := @norm_class_constant R Z R^o NZ (fun t : R^o => `|t|)
  hNZ hAbs AU 1 k hAU.
have hu := @norm_class_constant R Z X NZ NX hNZ hNX AU u k hAU.
have hLeft := norm_class_scalar_product (norm_class_subtract hOne ht) hu.
have hRight := norm_class_scalar_product ht hx.
apply: (norm_class_domain_agreement _ (norm_class_add hLeft hRight)).
by move=> z _; rewrite current_cone_homotopy_coordinates.
Qed.

(** Source for [current_cone_ambient_homotopy]: the original
    smooth homotopy from the constant map u to inclusion into R^n,
    Federer 4.1.10, p. 364. It is valid for every open source U. *)
Definition current_cone_ambient_homotopy :
  @is_smooth_current_homotopy R n n A U (fun _ => True)
    (fun _ => u) (fun x => x) h.
Proof.
split; last exact: current_cone_homotopy_smooth.
constructor.
- exact: current_cone_time_interval.
- exact: hU.
- move=> x _; exact: norm_full_domain_interior.
- by move=> z _.
- move=> x _; exact: (current_cone_homotopy_start (CurrentConeHomotopy.laws u)).
- move=> x _; exact: (current_cone_homotopy_end (CurrentConeHomotopy.laws u)).
Defined.
End CurrentConeHomotopyClass.
