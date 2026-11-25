(** Federer (1969), 4.1.13, pp. 369–370: the original
    affine homotopy of two smooth maps is smooth on an
    open time-space product. Reuse the composition, linear,
    scalar-product and sum calculus of 3.1.11, p. 220. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  NormRegularity NormRegularityOperations NormRegularityBilinear NormFiniteLinearBound
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct EuclideanOneCoordinate EuclideanBlockCoordinates
  EuclideanBlockLinearMaps EuclideanScalarCoordinateMaps
  CurrentCartesianDomain CurrentHomotopyUP CurrentHomotopyDomain
  CurrentAffineHomotopyUP CurrentAffineHomotopySealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section CurrentAffineHomotopyClass.
Variable R:realType.
Variables n nu:nat.
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
Local Notation p := (@euclidean_first_block_map R 1%N n).
Local Notation q := (@euclidean_last_block_map R 1%N n).
Local Notation time := (hom_comp (@euclidean_scalar_coordinate_map R 1%N ord0) p).
Variables f g:X->Y.
Local Notation h := (@CurrentAffineHomotopy.value R n nu f g).

(** Source for [current_affine_homotopy_coordinates]: the original
    affine path in the coordinates of 2.6.5, p. 120,
    supporting Federer 4.1.13, pp. 369–370. *)
Lemma current_affine_homotopy_coordinates z:
  h z=(1-time z)*:f (q z)+time z*:g (q z).
Proof.
have hz:@euclidean_block_join R 1%N n
    (@euclidean_one_embed R (time z),q z)=z.
  change (@euclidean_block_join R 1%N n
    (@euclidean_one_embed R (@euclidean_one_project R (p z)),q z)=z).
  by rewrite euclidean_one_projectK;exact:euclidean_block_splitK.
by rewrite -{1}hz CurrentAffineHomotopy.laws.
Qed.

Variable A:set R.
Hypothesis hA:@is_homotopy_parameter_interval R A.
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hf:norm_class_all_orders hNX hNY U f.
Hypothesis hg:norm_class_all_orders hNX hNY U g.
Local Notation AU := (@current_homotopy_product_domain R n A U).

(** Source for [current_affine_homotopy_smooth]: the affine
    homotopy used in Federer 4.1.13, pp. 369–370,
    is smooth wherever the two original maps are smooth.
    This regularity assertion imposes no image condition. *)
Theorem current_affine_homotopy_smooth:
  norm_class_all_orders hNZ hNY AU h.
Proof.
have hAU:=@current_cartesian_domain_open R 1%N n
  (@current_homotopy_time_domain R A) U
  (@current_homotopy_time_domain_open R A hA) hU.
have hTime:norm_bounded_linear NZ (fun t:R^o=>`|t|) time.
  exact:(@norm_finite_linear_bounded R Z R^o NZ (fun t:R^o=>`|t|)
    hNZ hAbs (1+n)%N (@coordinate_basis R (1+n)%N)
    (@coordinate_basisP R (1+n)%N) time).
have hLast:norm_bounded_linear NZ NX q.
  exact:(@norm_finite_linear_bounded R Z X NZ NX hNZ hNX (1+n)%N
    (@coordinate_basis R (1+n)%N) (@coordinate_basisP R (1+n)%N) q).
move=>k.
have ht:=@norm_class_linear R Z R^o NZ (fun t:R^o=>`|t|)
  hNZ hAbs AU time k hAU hTime.
have hq:=@norm_class_linear R Z X NZ NX hNZ hNX AU q k hAU hLast.
have hOne:=@norm_class_constant R Z R^o NZ (fun t:R^o=>`|t|)
  hNZ hAbs AU 1 k hAU.
have hF:=@norm_class_compose_on R Z X Y NZ NX NY hNZ hNX hNY AU U q f k
  (fun z hz=>hz.2) hq (hf k).
have hG:=@norm_class_compose_on R Z X Y NZ NX NY hNZ hNX hNY AU U q g k
  (fun z hz=>hz.2) hq (hg k).
have hLeft:=norm_class_scalar_product (norm_class_subtract hOne ht) hF.
have hRight:=norm_class_scalar_product ht hG.
apply:(norm_class_domain_agreement _ (norm_class_add hLeft hRight)).
by move=>z _;rewrite current_affine_homotopy_coordinates.
Qed.
End CurrentAffineHomotopyClass.
