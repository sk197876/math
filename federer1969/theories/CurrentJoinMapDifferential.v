(** Federer (1969), 4.1.11, p. 365: the actual
    differential of F(x,t,y)=(1-t)x+ty used in the
    sharp join mass estimate. The scalar product rule of
    3.1.11 and the existing block coordinates determine it. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP
  NormDifferentialLinear NormDifferentialLocal NormDifferentialArithmetic
  NormDifferentialScalarProduct NormHigherCurveDerivativeUP NormedPrimitiveCell
  NormFiniteLinearBound NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanOneCoordinate
  EuclideanBlockCoordinates EuclideanBlockLinearMaps EuclideanScalarCoordinateMaps
  CurrentMapDifferential CurrentJoinMapSealed CurrentJoinMapClass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentJoinMapDifferential.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation Z := (R_n R (n+(1+n))%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (n+(1+n))%N)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (n+(1+n))%N)).
Local Notation Abs := (fun t:R^o=>`|t|).
Local Notation hAbs := (@scalar_absolute_value_norm R).
Local Notation first := (@euclidean_first_block_map R n (1+n)%N).
Local Notation rest := (@euclidean_last_block_map R n (1+n)%N).
Local Notation middle := (hom_comp (@euclidean_first_block_map R 1%N n) rest).
Local Notation last := (hom_comp (@euclidean_last_block_map R 1%N n) rest).
Local Notation time := (hom_comp (@euclidean_scalar_coordinate_map R 1%N ord0) middle).
Local Notation F := (@CurrentJoinMap.value R n).

(** Source for [current_join_linear_differential]: the sum
    of the two original scalar-product differentials,
    supporting Federer 4.1.11, p. 365. This formula uses
    only the already specified coordinate linear maps. *)
Definition current_join_linear_differential (z:Z):Hom Z X:=
  @scalar_vector_product_linear_term R Z X (1-time z) (first z) (-time) first+
  @scalar_vector_product_linear_term R Z X (time z) (last z) time last.

Variable U:set Z.
Hypothesis hU:forall z,U z->norm_domain_interior NZ U z.
Arguments hU : clear implicits.

(** Source for [current_join_map_differential]: the actual
    DF is the original product-rule differential at every
    point of its open domain, supporting the first mass
    display in Federer 4.1.11, p. 365. *)
Theorem current_join_map_differential z:U z->
  @current_map_differential R (n+(1+n))%N n U F z=current_join_linear_differential z.
Proof.
move=>hz.
have hTimeBound:=@norm_finite_linear_bounded R Z R^o NZ Abs hNZ hAbs
  (n+(1+n))%N (@coordinate_basis R (n+(1+n))%N)
  (@coordinate_basisP R (n+(1+n))%N) time.
have hFirstBound:=@norm_finite_linear_bounded R Z X NZ NX hNZ hNX
  (n+(1+n))%N (@coordinate_basis R (n+(1+n))%N)
  (@coordinate_basisP R (n+(1+n))%N) first.
have hLastBound:=@norm_finite_linear_bounded R Z X NZ NX hNZ hNX
  (n+(1+n))%N (@coordinate_basis R (n+(1+n))%N)
  (@coordinate_basisP R (n+(1+n))%N) last.
have ht:=@norm_differential_linear R Z R^o NZ Abs hNZ hAbs U z time (hU z hz) hTimeBound.
have hx:=@norm_differential_linear R Z X NZ NX hNZ hNX U z first (hU z hz) hFirstBound.
have hy:=@norm_differential_linear R Z X NZ NX hNZ hNX U z last (hU z hz) hLastBound.
have hOne:=@norm_differential_constant R Z R^o NZ Abs hNZ hAbs U z 1 (hU z hz).
have hNegative:=@norm_differential_scale R Z R^o NZ Abs hNZ hAbs U time z time (-1) ht.
have hMinus:=@norm_differential_add R Z R^o NZ Abs hAbs U
  (fun _=>1) (fun s=>(-1)*time s) z 0 ((-1)*:time) hOne hNegative.
have hTimeMinus:has_norm_differential NZ Abs U (fun s=>1-time s) z (-time).
  have hLinear:0+(-1)*:time= -time by rewrite add0r scaleN1r.
  rewrite hLinear in hMinus.
  apply:(@norm_differential_domain_agreement R Z R^o NZ Abs hNZ U
    (fun s=>1+(-1)*time s) (fun s=>1-time s) z (-time) _ hMinus)=>s hs.
  by rewrite mulN1r.
have hLeft:=@norm_differential_scalar_product R Z X NZ NX hNZ hNX U
  (fun s=>1-time s) first z (-time) first hTimeMinus hx.
have hRight:=@norm_differential_scalar_product R Z X NZ NX hNZ hNX U
  time last z time last ht hy.
apply:(@current_map_differential_unique R (n+(1+n))%N n U F z).
apply:(@norm_differential_domain_agreement R Z X NZ NX hNZ U
  (fun s=>(1-time s)*:first s+time s*:last s) F z
  (current_join_linear_differential z) _
  (@norm_differential_add R Z X NZ NX hNX U _ _ z _ _ hLeft hRight))=>s hs.
exact:esym (@current_join_map_coordinates R n s).
Qed.

(** Source for [current_join_map_differential_value]: DF(x,t,y)
    sends (a,s,b) to (1-t)a+s(y-x)+tb, supporting the
    original exterior-image mass in Federer 4.1.11, p. 365.
    No endpoint, dimension or positive-degree exception is needed. *)
Theorem current_join_map_differential_value z:U z->forall w,
  @current_map_differential R (n+(1+n))%N n U F z w=
    (1-time z)*:first w+time w*:(last z-first z)+time z*:last w.
Proof.
move=>hz w;rewrite (current_join_map_differential hz) /current_join_linear_differential
  /scalar_vector_product_linear_term !hom_addE !hom_compE !hom_scaleE
  /scalar_coefficient_linear_map /=.
change ((-time w)*:first z+(1-time z)*:first w+
  (time w*:last z+time z*:last w)=
  (1-time z)*:first w+time w*:(last z-first z)+time z*:last w).
by rewrite scaleNr scalerBr !addrA
  [(- (time w*:first z))+((1-time z)*:first w)]addrC
  (addrAC ((1-time z)*:first w) (-(time w*:first z)) (time w*:last z)).
Qed.
End CurrentJoinMapDifferential.
