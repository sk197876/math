(** Federer (1969), 4.1.14, pp. 371–372: the actual
    affine homotopies of compatible smooth endpoint families
    are original allowed approximants on the exact time cylinder.
    Their whole-source image and one finite Lipschitz bound
    are proved before applying this consequence. The original
    universal image condition is not strengthened. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanBlockLinearMaps SmoothCompactSet
  CurrentHomotopyUP CurrentHomotopyDomain CurrentCartesianDomain
  CurrentAffineHomotopySealed CurrentAffineHomotopyClass CurrentCompactTimeCylinder
  CurrentSmoothApproximationUP CurrentMapDifferential EuclideanHomOperator
  HomSpaceTopology CriticalLocalDerivativeBound LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentAffineSmoothApproximation.
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
Variables (A:set R) (U:set X) (V:set Y).
Hypothesis hA:@is_homotopy_parameter_interval R A.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Variable K:smooth_compact_set hNX U.
Variables f g:X->Y.
Variables a b:nat->X->Y.
Hypothesis hFirst:@is_current_smooth_approximation R n nu U V K f a.
Hypothesis hSecond:@is_current_smooth_approximation R n nu U V K g b.
Local Notation AU:=(@current_homotopy_product_domain R n A U).
Local Notation H:=(@CurrentAffineHomotopy.value R n nu f g).
Local Notation Hi i:=(@CurrentAffineHomotopy.value R n nu (a i) (b i)).
Hypothesis hImages:forall i z,AU z->V (Hi i z).
Variable C:R.
Hypothesis hLipschitz:forall i,@is_metric_lipschitz_bound R
  (real_norm_metric_space hNZ) (real_norm_metric_space hNY) AU (Hi i) C.

(** Source for [current_affine_smooth_approximation]: the genuine
    affine H_i is an allowed original smooth approximation
    of H on [0,1] times K, supporting Federer 4.1.14,
    pp. 371–372. In particular its actual derivative cap
    is proved, and the compact index is the exact cylinder. *)
Theorem current_affine_smooth_approximation:
  @is_current_smooth_approximation R (1+n)%N nu AU V
    (@current_compact_time_cylinder R n A U hA K) H (fun i=>Hi i).
Proof.
have hAU:=@current_cartesian_domain_open R 1%N n
  (@current_homotopy_time_domain R A) U
  (@current_homotopy_time_domain_open R A hA) hU.
have hSmooth:forall i,norm_class_all_orders hNZ hNY AU (Hi i).
  move=>i;exact:(@current_affine_homotopy_smooth R n nu (a i) (b i)
    A hA U hU (current_smooth_approximation_class hFirst i)
    (current_smooth_approximation_class hSecond i)).
constructor.
- exact:hImages.
- exact:hSmooth.
- exists C;split;first exact:(hLipschitz 0%N).1.
  move=>i z hz.
  have hzAU:AU z:=smooth_compact_in_domain
    (@current_compact_time_cylinder R n A U hA K) z hz.
  have hActual:=@current_map_differential_actual R (1+n)%N nu AU (Hi i)
    (hSmooth i) z hzAU.
  apply:hom_operator_norm_least;first exact:(hLipschitz i).1.
  exact:(@critical_local_lipschitz_differential_bound R Z Y NZ NY hNZ hNY
    AU AU (Hi i) z (@current_map_differential R (1+n)%N nu AU (Hi i) z)
    C hActual (hAU z hzAU) (hLipschitz i).2).
- move=>eps hEps.
  have hHalf:0<eps/2 by lra.
  have[N hN]:=current_smooth_approximation_uniform hFirst hHalf.
  have[M hM]:=current_smooth_approximation_uniform hSecond hHalf.
  exists (maxn N M)=>i hi z [ht hx].
  pose t:=@euclidean_one_project R (@euclidean_first_block_map R 1%N n z).
  pose x:=@euclidean_last_block_map R 1%N n z.
  have /andP[htZero htOne]:0<=t<=1:=ht.
  have hFirstError:=hN i (leq_trans (leq_maxl N M) hi) x hx.
  have hSecondError:=hM i (leq_trans (leq_maxr N M) hi) x hx.
  have hDifference:Hi i z-H z=(1-t)*:(a i x-f x)+t*:(b i x-g x).
    rewrite !current_affine_homotopy_coordinates /t /x !scalerBr.
    by rewrite opprD addrACA.
  rewrite hDifference.
  have hTriangle:=real_seminorm_triangle hNY.1
    ((1-t)*:(a i x-f x)) (t*:(b i x-g x)).
  have hLeft:0<=1-t by lra.
  rewrite !(real_seminorm_scale hNY.1) (ger0_norm hLeft) (ger0_norm htZero) in hTriangle.
  have hCoeff:1-t<=1 by lra.
  have hFirstBound:=ler_wpM2r (real_seminorm_nonnegative hNY.1 (a i x-f x)) hCoeff.
  have hSecondBound:=ler_wpM2r (real_seminorm_nonnegative hNY.1 (b i x-g x)) htOne.
  rewrite !mul1r in hFirstBound hSecondBound.
  apply:(le_lt_trans (le_trans hTriangle (lerD hFirstBound hSecondBound))).
  have hSum:=ltrD hFirstError hSecondError.
  by rewrite -splitr in hSum.
Qed.
End CurrentAffineSmoothApproximation.
