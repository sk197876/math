(** Federer (1969), 3.4.2(8), p. 311, proved on
    pp. 315–316: flatness along Z gives zero image measure
    at the original real degree nu+(mu-nu)/lambda. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets
  constructive_ereal topology.
From Federer Require Import ModuleQuotient SubspaceCarrier GrassmannSubspaces
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  RealNormUP NormMetric RelativeClassUP EuclideanProjectionSpace
  CriticalManifoldFamilyUP CriticalCodimensionChart CriticalProjectedSubspace
  CriticalProjectionChartNullity CriticalOscillation PositiveRightOrderLimit
  RealHausdorffNormalisation RealHausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_flat_image_degree_nonnegative]: the
    real degree sigma=nu+(mu-nu)/lambda in 3.4.2(8), p. 311.
    Its nonnegativity follows from the printed positive lambda
    and natural dimensions. This supplies the type parameter of
    the actual Gamma-normalized real Hausdorff measure. *)
Lemma critical_flat_image_degree_nonnegative (R:realType) m mu d (lambda:R):
  0<lambda ->0<=(m-d)%:R+(mu-(m-d))%:R/lambda.
Proof.
move=>hLambda;apply:addr_ge0;first exact:ler0n.
exact:divr_ge0 (ler0n R _) (ltW hLambda).
Qed.

(** Source for [critical_flat_image_nullity]: the complete
    assertion (8) in 3.4.2, p. 311, with the proof on
    pp. 315–316. For the original compact C in an original
    Omega(mu,1) manifold, eta of positive real order lambda
    tending to zero implies H^sigma(f(C))=0 when mu>nu.
    The projection image dimension and adapted coordinates are
    derived from the original chart. The target is arbitrary
    normed; the source and image need not be measurable.
    The parameter hp is the already proved nonnegativity of
    sigma, not an additional mathematical hypothesis. *)
Theorem critical_flat_image_nullity (R:realType) m d
    (Z:G (R_n R m) d) mu (S C:set (R_n R m))
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY) (f:R_n R m->Y)
    (lambda:R) (hp:0<=(m-d)%:R+(mu-(m-d))%:R/lambda):
  critical_manifold_family Z mu 1 S ->(m-d<mu)%N ->C `<=` S ->
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m))) C ->
  norm_class_relative (inner_norm_real_norm (@euclidean_inner_productP R m)) hNY S S f 1 ->
  0<lambda ->positive_right_extended_order_limit
    (fun delta=>critical_eta NY (grassmann_val Z) S C f lambda delta) 0%E ->
  @real_hausdorff_measure R (real_norm_metric_space hNY)
    ((m-d)%:R+(mu-(m-d))%:R/lambda) hp (f @` C)=0%E.
Proof.
move=>hOmega hDim hCS hC hf hLambda hEta.
have hD:=critical_subspace_dimension_bound Z.
have [p [g hChart]]:exists (p:euclidean_projection_space R m mu) g,
    is_critical_manifold_chart 1 (grassmann_val Z) S p g.
  case:hOmega.2.2.2=>[hZero|hChart];last exact:hChart.
  by rewrite hZero ltn0 in hDim.
have [A hA]:=@critical_projected_subspace_exists R m d mu Z p hD (critical_chart_kernel hChart).
have hSum:(mu-(m-d)+(m-d)=mu)%N:=subnK (ltnW hDim).
have hPositive:(0<mu-(m-d))%N by rewrite subn_gt0.
set a:=(mu-(m-d))%N in A hA hSum hPositive *.
set b:=(m-d)%N in A hA hSum hPositive *.
have hAll:forall (q:euclidean_projection_space R m (a+b))
    (g0:R_n R (a+b)->R_n R m) (B:G (R_n R (a+b)) a),
    is_critical_manifold_chart 1 (grassmann_val Z) S q g0 ->
    (forall y,grassmann_val B y <->exists z,grassmann_val Z z /\
      euclidean_projection_linear q z=y) ->
    @real_hausdorff_measure R (real_norm_metric_space hNY)
      (b%:R+a%:R/lambda) hp (f @` C)=0%E.
  move=>q g0 B hChart0 hB.
  exact:(@critical_projection_chart_image_nullity R m a b (grassmann_val Z) S C q g0 B
    Y NY hNY f lambda (real_hausdorff_normalisation hp) hPositive hLambda
    (ltW (real_hausdorff_normalisation_positive hp)) hChart0 hB hCS hC hf hEta).
have hReindexed:forall (q:euclidean_projection_space R m mu)
    (g0:R_n R mu->R_n R m) (B:G (R_n R mu) a),
    is_critical_manifold_chart 1 (grassmann_val Z) S q g0 ->
    (forall y,grassmann_val B y <->exists z,grassmann_val Z z /\
      euclidean_projection_linear q z=y) ->
    @real_hausdorff_measure R (real_norm_metric_space hNY)
      (b%:R+a%:R/lambda) hp (f @` C)=0%E.
  rewrite -hSum;exact:hAll.
exact:hReindexed p g A hChart hA.
Qed.
