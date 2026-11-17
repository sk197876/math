(** Federer (1969), 3.4.8(11), p. 333:
    the origin is a zero-dimensional functional
    analytic stratum in every open neighbourhood.
    Use the actual coordinate equations and
    their already proved independent differentials. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness NormDifferentialUP NormDifferentialLinear NormBoundedLinearTopology
  NormAnalyticUP NormAnalyticOperations NormAnalyticConstant FunctionalAnalyticSubmanifoldUP
  EuclideanScalarCoordinateMaps EuclideanScalarCoordinateAnalytic EuclideanCoordinateCovectorsIndependent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [functional_analytic_point]:
    the actual point stratum in the
    m=0 base of 3.4.8(11), p. 333.
    Every ambient dimension, including zero,
    and the original neighbourhood are retained. *)
Theorem functional_analytic_point (R:realType) n (U:set (R_n R n)):
  @open (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) U ->
  U 0 ->@is_functional_analytic_submanifold R n 0 U [set 0].
Proof.
move=>hU hU0.
pose X:=R_n R n;pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose NR:=fun z:R^o=>`|z|;pose hNR:=@scalar_absolute_value_norm R.
have hInterior x (hx:U x):norm_domain_interior NX U x.
  have hOpen:=hU;rewrite openE in hOpen.
  exact:(@norm_domain_interior_neighbourhood R X NX hNX U x).2 (hOpen x hx).
rewrite /is_functional_analytic_submanifold subn0.
split;first exact:leq0n.
split;first exact:hU.
exists (fun (i:'I_n) (x:X)=>x i),(fun _=>(1:R));split.
- move=>i;exact:(@norm_analytic_open_restriction R X R^o NX NR hNX hNR setT U (fun x=>x i)
    (fun _ _=>Logic.I) hInterior (@euclidean_scalar_coordinate_analytic R n i)).
split;first exact:(@norm_constant_analytic R X R^o NX NR hNX hNR U hInterior 1).
split.
- move=>x;split.
  + move=>->;split;first exact:hU0.
    split;first by move=>i;rewrite ffunE.
    by move/eqP;rewrite oner_eq0.
  + move=>[_ [hCoordinates _]];apply/ffunP=>i;by rewrite ffunE hCoordinates.
- move=>x hx;have hUx:U x by rewrite hx.
  exists (fun i=>@euclidean_scalar_coordinate_map R n i);split.
  + move=>i;exact:(@norm_differential_linear R X R^o NX NR hNX hNR U x
      (@euclidean_scalar_coordinate_map R n i) (hInterior x hUx)
      (@euclidean_scalar_coordinate_bounded R n i)).
  + exact:euclidean_coordinate_covectors_independent.
Qed.
