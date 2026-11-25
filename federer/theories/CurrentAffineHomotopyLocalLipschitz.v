(** Federer (1969), 4.1.14, p. 371: the affine deformation
    between locally Lipschitz maps is locally Lipschitz on
    each open time-space product. Its image condition is
    established separately by shrinking near the support. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormRegularity NormRegularityOperations NormFiniteLinearBound
  InnerNorm HilbertFormCompactness GrassmannAbbreviations
  FiniteCoordinates EuclideanInnerProduct EuclideanBlockLinearMaps
  EuclideanScalarCoordinateMaps LipschitzUP
  NormLocalLipschitzLinearMaps NormLocalLipschitzScalarProduct
  CurrentCartesianDomain CurrentHomotopyUP CurrentHomotopyDomain
  CurrentAffineHomotopySealed CurrentAffineHomotopyClass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentAffineHomotopyLocalLipschitz.
Variable R : realType.
Variables n nu : nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation Z := (R_n R (1+n)%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (1+n)%N)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N)).
Local Notation hAbs := (@scalar_absolute_value_norm R).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation YT := (real_norm_metric_space hNY).
Local Notation ZT := (real_norm_metric_space hNZ).
Local Notation p := (@euclidean_first_block_map R 1%N n).
Local Notation q := (@euclidean_last_block_map R 1%N n).
Local Notation time := (hom_comp (@euclidean_scalar_coordinate_map R 1%N ord0) p).
Variables f g : X -> Y.
Variable A : set R.
Hypothesis hA : @is_homotopy_parameter_interval R A.
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Hypothesis hf : @is_locally_metric_lipschitz R XT YT U f.
Hypothesis hg : @is_locally_metric_lipschitz R XT YT U g.
Local Notation AU := (@current_homotopy_product_domain R n A U).
Local Notation H := (@CurrentAffineHomotopy.value R n nu f g).

(** Source for [current_affine_homotopy_locally_lipschitz]: apply
    the local Lipschitz calculus of 2.2.7, p. 64, to the
    original affine formula in Federer 4.1.14, p. 371.
    No whole-domain image or global Lipschitz bound is required. *)
Theorem current_affine_homotopy_locally_lipschitz :
  @is_locally_metric_lipschitz R ZT YT AU H.
Proof.
have hAU := @current_cartesian_domain_open R 1%N n
  (@current_homotopy_time_domain R A) U
  (@current_homotopy_time_domain_open R A hA) hU.
have hTime : norm_bounded_linear NZ (fun t:R^o => `|t|) time.
  exact: (@norm_finite_linear_bounded R Z R^o NZ (fun t:R^o => `|t|)
    hNZ hAbs (1+n)%N (@coordinate_basis R (1+n)%N)
    (@coordinate_basisP R (1+n)%N) time).
have hLast : norm_bounded_linear NZ NX q.
  exact: (@norm_finite_linear_bounded R Z X NZ NX hNZ hNX (1+n)%N
    (@coordinate_basis R (1+n)%N) (@coordinate_basisP R (1+n)%N) q).
have ht := @norm_class_linear R Z R^o NZ (fun t:R^o => `|t|)
  hNZ hAbs AU time 1%N hAU hTime.
have hOne := @norm_class_constant R Z R^o NZ (fun t:R^o => `|t|)
  hNZ hAbs AU 1 1%N hAU.
have hLeftTime := @norm_class_one_locally_metric_lipschitz R Z R^o
  NZ (fun t:R^o => `|t|) hNZ hAbs AU (fun z => 1-time z)
  ((@norm_class_firstP R Z R^o NZ (fun t:R^o => `|t|)
    hNZ hAbs AU (fun z => 1-time z)).1 (norm_class_subtract hOne ht)).
have hRightTime := @norm_class_one_locally_metric_lipschitz R Z R^o
  NZ (fun t:R^o => `|t|) hNZ hAbs AU time
  ((@norm_class_firstP R Z R^o NZ (fun t:R^o => `|t|)
    hNZ hAbs AU time).1 ht).
have hF := @norm_local_lipschitz_linear_precompose R Z X Y NZ NX NY
  hNZ hNX hNY AU U q f hLast (fun z hz => hz.2) hf.
have hG := @norm_local_lipschitz_linear_precompose R Z X Y NZ NX NY
  hNZ hNX hNY AU U q g hLast (fun z hz => hz.2) hg.
have hLeft := @norm_locally_lipschitz_scalar_product R Z Y NZ NY hNZ hNY
  AU (fun z => 1-time z) (fun z => f (q z)) hLeftTime hF.
have hRight := @norm_locally_lipschitz_scalar_product R Z Y NZ NY hNZ hNY
  AU time (fun z => g (q z)) hRightTime hG.
have hSum := norm_local_lipschitz_add hLeft hRight.
move=> z hz.
have [W [hW [L [hL hBound]]]] := hSum z hz.
exists W; split; first exact: hW.
exists L; split; first exact: hL.
split; first exact: hBound.1.
move=> x y hx hy.
change (is_true (NY (H x-H y) <= L*NZ (x-y))).
rewrite !current_affine_homotopy_coordinates.
exact: hBound.2 x y hx hy.
Qed.
End CurrentAffineHomotopyLocalLipschitz.
