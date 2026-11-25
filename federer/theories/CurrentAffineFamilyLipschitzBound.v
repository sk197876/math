(** Federer (1969), 4.1.14, pp. 371–372: compatible
    smooth endpoint families give a uniformly bounded smooth
    affine homotopy family on a fixed bounded time interval.
    Reuse the original linear-coordinate Lipschitz laws and
    the proved scalar-product estimate. This finite common
    bound supports the original approximation specification;
    it does not replace the sharp sigma mass weight. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals topology lra ring.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP
  NormFiniteLinearBound InnerNorm HilbertFormCompactness GrassmannAbbreviations
  FiniteCoordinates EuclideanInnerProduct EuclideanBlockLinearMaps
  EuclideanScalarCoordinateMaps CurrentHomotopyUP CurrentAffineHomotopySealed
  CurrentAffineHomotopyClass LipschitzUP MetricLipschitzComposition
  NormLocalLipschitzScalarProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentAffineFamilyLipschitzBound.
Variable R:realType.
Variables n nu:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation Z:=(R_n R (1+n)%N).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation NZ:=(inner_norm (@euclidean_inner_productP R (1+n)%N)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation hNZ:=(inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N)).
Local Notation hAbs:=(@scalar_absolute_value_norm R).
Local Notation p:=(@euclidean_first_block_map R 1%N n).
Local Notation q:=(@euclidean_last_block_map R 1%N n).
Local Notation time:=(hom_comp (@euclidean_scalar_coordinate_map R 1%N ord0) p).
Variables (A:set R) (W:set X).
Hypothesis hTime:forall t,A t->`|t|<=2 /\`|1-t|<=2.
Arguments hTime : clear implicits.
Variables a b:nat->X->Y.
Variables Lf Lg M:R.
Hypothesis hM:0<=M.
Hypothesis hA:forall i,@is_metric_lipschitz_bound R (real_norm_metric_space hNX)
  (real_norm_metric_space hNY) W (a i) Lf.
Hypothesis hB:forall i,@is_metric_lipschitz_bound R (real_norm_metric_space hNX)
  (real_norm_metric_space hNY) W (b i) Lg.
Hypothesis hValuesA:forall i x,W x->NY (a i x)<=M.
Hypothesis hValuesB:forall i x,W x->NY (b i x)<=M.
Arguments hValuesA : clear implicits.
Arguments hValuesB : clear implicits.
Local Notation AU:=(@current_homotopy_product_domain R n A W).
Local Notation H i:=(@CurrentAffineHomotopy.value R n nu (a i) (b i)).

(** Source for [current_affine_family_lipschitz_bound]: one
    finite common Lipschitz bound for the actual smooth affine
    maps on their entire chosen open source, supporting Federer
    4.1.14, pp. 371–372. The endpoint constants may vanish. *)
Theorem current_affine_family_lipschitz_bound:
  exists C:R,forall i,@is_metric_lipschitz_bound R (real_norm_metric_space hNZ)
    (real_norm_metric_space hNY) AU (H i) C.
Proof.
have[Ct [hCt hTBound]]:=@norm_finite_linear_bounded R Z R^o NZ
  (fun t:R^o=>`|t|) hNZ hAbs (1+n)%N (@coordinate_basis R (1+n)%N)
  (@coordinate_basisP R (1+n)%N) time.
have[Cq [hCq hQBound]]:=@norm_finite_linear_bounded R Z X NZ NX hNZ hNX
  (1+n)%N (@coordinate_basis R (1+n)%N) (@coordinate_basisP R (1+n)%N) q.
have hQLip:@is_metric_lipschitz_bound R (real_norm_metric_space hNZ)
    (real_norm_metric_space hNX) AU q Cq.
  split;first exact:hCq.
  move=>z w _ _;change (is_true (NX (q z-q w)<=Cq*NZ (z-w))).
  by rewrite -(linB (hom_linear q));exact:hQBound.
have hTLip:@is_metric_lipschitz_bound R (real_norm_metric_space hNZ)
    (real_norm_metric_space hAbs) AU time Ct.
  split;first exact:hCt.
  move=>z w _ _;change (is_true (`|time z-time w|<=Ct*NZ (z-w))).
  by rewrite -(linB (hom_linear time));exact:hTBound.
have hLeftLip:@is_metric_lipschitz_bound R (real_norm_metric_space hNZ)
    (real_norm_metric_space hAbs) AU (fun z=>1-time z) Ct.
  split;first exact:hCt.
  move=>z w hz hw.
  change (is_true (`|(1-time z)-(1-time w)|<=Ct*NZ (z-w))).
  have hDifference:(1-time z)-(1-time w)=time w-time z by ring.
  rewrite hDifference distrC;exact:hTLip.2 z w hz hw.
pose costF:=2*(Lf*Cq)+Ct*M.
pose costG:=2*(Lg*Cq)+Ct*M.
exists (costF+costG)=>i.
have hPullF:=@metric_lipschitz_composition_bound R (real_norm_metric_space hNZ)
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) AU W q (a i) Cq Lf
  (fun z hz=>hz.2) hQLip (hA i).
have hPullG:=@metric_lipschitz_composition_bound R (real_norm_metric_space hNZ)
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) AU W q (b i) Cq Lg
  (fun z hz=>hz.2) hQLip (hB i).
have hTwo:0<=(2:R) by rewrite ler0n.
have hLeft:=@norm_scalar_product_lipschitz_bound R Z Y NZ NY hNZ hNY AU
  (fun z=>1-time z) (fun z=>a i (q z)) 2 M Ct (Lf*Cq)
  hTwo hM hLeftLip hPullF
  (fun z hz=>(hTime (time z) hz.1).2) (fun z hz=>hValuesA i (q z) hz.2).
have hRight:=@norm_scalar_product_lipschitz_bound R Z Y NZ NY hNZ hNY AU
  time (fun z=>b i (q z)) 2 M Ct (Lg*Cq)
  hTwo hM hTLip hPullG
  (fun z hz=>(hTime (time z) hz.1).1) (fun z hz=>hValuesB i (q z) hz.2).
split;first exact:addr_ge0 hLeft.1 hRight.1.
move=>z w hz hw.
change (is_true (NY (H i z-H i w)<=(costF+costG)*NZ (z-w))).
have hCoordinates v:H i v=(1-time v)*:a i (q v)+time v*:b i (q v).
  exact:current_affine_homotopy_coordinates.
rewrite !hCoordinates.
have hDifference:
    ((1-time z)*:a i (q z)+time z*:b i (q z))-
      ((1-time w)*:a i (q w)+time w*:b i (q w))=
    ((1-time z)*:a i (q z)-(1-time w)*:a i (q w))+
      (time z*:b i (q z)-time w*:b i (q w)).
  by rewrite opprD addrACA.
rewrite hDifference mulrDl.
exact:(le_trans (real_seminorm_triangle hNY.1 _ _)
  (lerD (hLeft.2 z w hz hw) (hRight.2 z w hz hw))).
Qed.
End CurrentAffineFamilyLipschitzBound.
