(** Federer (1969), 3.2.33, p. 270: analytic
    coordinate expressions detect the rank of the actual
    relative differential, by 3.1.22(3), p. 235. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  RealNormUP NormDifferentialUP NormDifferentialDirectional NormRegularity NormClassOneUP
  NormCoordinateSystemUP RelativeDifferentialUP RelativeCoordinateDifferential
  RelativeDifferentialUniqueness PartialFunctionUP PartialImageDimensionUP
  ParametricPartialImageDimension LinearRankUP NormAnalyticUP NormAnalyticLocal
  NormAnalyticRelativeUP RelativeAnalyticDifferentialExistence RelativeLowImageLocus
  EuclideanExteriorGramRank EuclideanExteriorGramLowRank.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section CoordinateRank.
Variable R:realType.
Variables n m v mu:nat.
Local Notation X:=(R_n R n).
Local Notation Z:=(R_n R m).
Local Notation Y:=(R_n R v).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NZ:=(inner_norm (@euclidean_inner_productP R m)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R v)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ:=(inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R v)).
Variables (W T:set X) (V:set Z) (phi:X->Z) (psi:Z->X) (F:X->Y)
  (D:Z->Hom Z Y).
Hypothesis hc:is_norm_coordinate_system hNX hNZ W T V phi psi 1%N.
Hypothesis hPhi:@norm_analytic R X Z NX NZ hNX hNZ T phi.
Hypothesis hPsi:@norm_analytic R Z X NZ NX hNZ hNX V psi.
Hypothesis hF:@norm_analytic_relative R X Y NX NY hNX hNY setT W F.
Hypothesis hD:forall u,V u ->has_norm_differential NZ NY V (fun z=>F (psi z)) u (D u).

(** Source for [analytic_coordinate_low_image_iff]: coordinate
    rank tests describe the actual relative differential in
    Federer 3.2.33, p. 270. The exact relative
    graph criterion and both differential uniqueness laws prove
    both directions, without an assumed field for the original
    map or values outside its tangent domain. *)
Theorem analytic_coordinate_low_image_iff x:
  W x ->T x ->
  (relative_low_image_locus mu W F x <->
    exists r,has_linear_rank (D (phi x)) r /\(r<=mu)%N).
Proof.
move=>hx ht.
have [E hE]:=(norm_class_firstP hNX hNZ T phi).1
  (norm_analytic_class_all_orders hPhi 1%N).
have [J hJ]:=(norm_class_firstP hNZ hNX V psi).1
  (norm_analytic_class_all_orders hPsi 1%N).
have hv:V (phi x):=norm_coordinate_forward_range hc ht.
have hPhiD:=norm_class_one_differential hE ht.
have hPsiD:=norm_class_one_differential hJ hv.
have [d hRel]:=relative_analytic_differential_exists hF hx.
have [Q [hQ hParam]]:=(@relative_coordinate_differential_criterion R X Z Y
  NX NZ NY hNX hNZ hNY setT W T V phi psi F x (E x) (J (phi x)) d
  hc hx ht (fun y hy=>Logic.I) hPhiD hPsiD).1 hRel.
have hEqual:Q=D (phi x):=norm_differential_unique hNZ hNY hQ (@hD (phi x) hv).
have hLow:=parametric_partial_low_image_iff mu hParam.
rewrite hEqual in hLow.
split.
- move=>[_ [e [hRelE hDim]]].
  have he:e=d:=@relative_norm_differential_unique R X Y NX NY hNX hNY setT W F x e d hRelE hRel.
  apply:hLow.1; by rewrite -he.
- move=>hRank; split; first exact hx.
  exists d; split; first exact hRel.
  exact:hLow.2 hRank.
Qed.

(** Source for [analytic_coordinate_low_image_gram]: the
    higher exterior Gram zero locus detecting dim im Df<=mu
    in Federer 3.2.33, p. 270. Coordinate changes
    preserve the exact image, so vanishing of this actual
    coordinate polynomial is intrinsic even though the value
    of its Hilbert square depends on the chart metric. *)
Theorem analytic_coordinate_low_image_gram x:
  W x ->T x ->
  (relative_low_image_locus mu W F x <->
    euclidean_exterior_gram mu.+1 (D (phi x))= 0).
Proof.
move=>hx ht.
exact:(iff_trans (analytic_coordinate_low_image_iff hx ht)
  (iff_sym (euclidean_exterior_gram_low_rank mu (D (phi x))))).
Qed.
End CoordinateRank.
