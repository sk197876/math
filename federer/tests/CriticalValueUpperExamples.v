(** Federer (1969), 3.4.3, pp. 316–317: actual
    regressions of the complete critical-value upper theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness RealNormUP NormMetric NormDifferentialUP NormDifferentialLinear
  NormOpenDomainLaws NormRegularity NormRegularityOperations NormRegularityBilinear NormFiniteLinearBound
  NormDifferentialScalarProduct NormHigherCurveDerivativeUP NormedPrimitiveCell
  LinearRankUP EuclideanBlockLinearMaps CriticalValueUpperTheorem CriticalValueUpper
  CriticalRankDegreeComparison RealHausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_upper_nonzero_constant_line]: a
    rank-zero, class-two instance of 3.4.3, pp. 316–317.
    The original unbounded whole line maps to the nonzero
    singleton, with zero actual Hausdorff mass in degree one half. *)
Example critical_upper_nonzero_constant_line (R:realType)
    (hp:0<=(0%:R+(1-0)%:R/2%:R:R)):
  @real_hausdorff_measure R (real_norm_metric_space (@scalar_absolute_value_norm R))
    (0%:R+(1-0)%:R/2%:R) hp ((fun _:R_n R 1=>(1:R)) @` setT)=0%E /\
  ((fun _:R_n R 1=>(1:R)) @` setT)=[set 1].
Proof.
pose X:=R_n R 1.
pose NX:=inner_norm (@euclidean_inner_productP R 1).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R 1).
pose hNY:=@scalar_absolute_value_norm R.
have hOpen x (_:setT x):norm_domain_interior NX setT x:=norm_full_domain_interior NX x.
have hClass:=@norm_class_constant R X R^o NX (fun t:R^o=>`|t|) hNX hNY setT 1 2 hOpen.
have hRank x (_:setT x):exists D:Hom X R^o,
    has_norm_differential NX (fun t:R^o=>`|t|) setT (fun _=>1) x D /\
    exists r,has_linear_rank D r /\(r<=0)%N.
  exists 0;split;first exact:(@norm_differential_constant R X R^o NX (fun t:R^o=>`|t|)
    hNX hNY setT x 1 (hOpen x I)).
  exists 0%N;split;last exact:leqnn.
  apply:(linear_rank_zeroP (0:Hom X R^o)).2;by move=>v;rewrite hom_zeroE.
split.
- exact:(@federer_3_4_3 R 1 0 2 R^o (fun t:R^o=>`|t|) hNY setT setT (fun _=>1)
    hp (erefl true) (erefl true) hOpen (fun x hx=>hx) hClass hRank).
- apply/seteqP;split;first by move=>y [x _ <-].
  move=>y ->;exists (0:X);by [].
Qed.

(** Source for [critical_upper_full_projection_plane]: a
    nonconstant rank-one, class-three instance of 3.4.3,
    pp. 316–317. The original whole plane projects onto
    the entire line, whose actual Hausdorff measure in degree
    1+1/3 is zero. No finite mass or bounded source is supplied. *)
Example critical_upper_full_projection_plane (R:realType)
    (hp:0<=(1%:R+(2-1)%:R/3%:R:R)):
  let P:=@euclidean_first_block_map R 1 1 in
  @real_hausdorff_measure R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R 1)))
    (1%:R+(2-1)%:R/3%:R) hp (P @` setT)=0%E /\P @` setT=setT.
Proof.
move=>P.
pose X:=R_n R 2;pose Y:=R_n R 1.
pose NX:=inner_norm (@euclidean_inner_productP R 2).
pose NY:=inner_norm (@euclidean_inner_productP R 1).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R 2).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R 1).
have hOpen x (_:setT x):norm_domain_interior NX setT x:=norm_full_domain_interior NX x.
have hBound:=@norm_finite_linear_bounded R X Y NX NY hNX hNY 2
  (@coordinate_basis R 2) (@coordinate_basisP R 2) P.
have hClass:=@norm_class_linear R X Y NX NY hNX hNY setT P 3 hOpen hBound.
have [r [hRank hr]]:=linear_rank_exists P (@coordinate_basisP R 1).
have hActual x (_:setT x):exists D:Hom X Y,
    has_norm_differential NX NY setT P x D /\exists r,has_linear_rank D r /\(r<=1)%N.
  exists P;split;first exact:(@norm_differential_linear R X Y NX NY hNX hNY setT x P (hOpen x I) hBound).
  by exists r.
split.
- exact:(@federer_3_4_3 R 2 1 3 Y NY hNY setT setT P hp
    (erefl true) (erefl true) hOpen (fun x hx=>hx) hClass hActual).
- apply/seteqP;split;first by move=>y _.
  move=>y _;exists (@euclidean_first_injection R 1 1 y);first by [].
  exact:euclidean_first_block_injectionK.
Qed.

(** Source for [critical_upper_quadratic_origin]: a nonlinear
    class-two instance of 3.4.3, pp. 316–317. The
    square of the line coordinate has genuine zero differential
    on the original singleton at the origin. Its nonempty image
    has zero actual Hausdorff measure in degree one half. *)
Example critical_upper_quadratic_origin (R:realType)
    (hp:0<=(0%:R+(1-0)%:R/2%:R:R)):
  @real_hausdorff_measure R (real_norm_metric_space (@scalar_absolute_value_norm R))
    (0%:R+(1-0)%:R/2%:R) hp
    ((fun x:R_n R 1=>x ord0*x ord0) @` [set 0])=0%E /\
  ((fun x:R_n R 1=>x ord0*x ord0) @` [set 0])=[set 0].
Proof.
pose X:=R_n R 1.
pose NX:=inner_norm (@euclidean_inner_productP R 1).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R 1).
pose hNY:=@scalar_absolute_value_norm R.
have hLinear:linear (fun x:X=>x ord0) by move=>a x y;rewrite !ffunE.
pose E:Hom X R^o:=@HomMap R X R^o (fun x=>x ord0) (introT (asboolP _) hLinear).
have hOpen x (_:setT x):norm_domain_interior NX setT x:=norm_full_domain_interior NX x.
have hBound:=@norm_finite_linear_bounded R X R^o NX (fun t:R^o=>`|t|) hNX hNY 1
  (@coordinate_basis R 1) (@coordinate_basisP R 1) E.
have hE:=@norm_class_linear R X R^o NX (fun t:R^o=>`|t|) hNX hNY setT E 2 hOpen hBound.
have hSquare:=norm_class_scalar_product hE hE.
have hActual x (hx:[set 0] x):exists D:Hom X R^o,
    has_norm_differential NX (fun t:R^o=>`|t|) setT (fun x=>x ord0*x ord0) x D /\
    exists r,has_linear_rank D r /\(r<=0)%N.
  have hX:x=0:=hx;subst x.
  have hD:=@norm_differential_linear R X R^o NX (fun t:R^o=>`|t|) hNX hNY setT 0 E
    (hOpen 0 I) hBound.
  pose M:=scalar_vector_product_linear_term (E 0) (E 0) E E.
  exists M;split;first exact:(norm_differential_scalar_product hNX hNY hD hD).
  exists 0%N;split;last exact:leqnn.
  apply:(linear_rank_zeroP M).2=>v.
  rewrite /M /scalar_vector_product_linear_term linear0 hom_addE hom_compE hom_scaleE.
  change ((E v)*(0:R)+0*(E v)=0);by rewrite mulr0 mul0r add0r.
split.
- exact:(@federer_3_4_3 R 1 0 2 R^o (fun t:R^o=>`|t|) hNY setT [set 0]
    (fun x=>x ord0*x ord0) hp (erefl true) (erefl true) hOpen (fun x _=>I) hSquare hActual).
- apply/seteqP;split.
  + move=>y [x hx <-];have hX:x=0:=hx;by rewrite hX ffunE mul0r.
  + move=>y ->;exists (0:X);first by [].
    by rewrite ffunE mul0r.
Qed.
