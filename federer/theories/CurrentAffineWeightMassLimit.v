(** Federer (1969), 4.1.14, p. 371: pass the
    exact affine weights of smooth endpoint approximations
    to the original weight |g-f|sigma^m. Uniform convergence
    is needed only on the compact carrying set of the
    original finite Radon variation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology num_normedtype
  pseudometric_normed_Zmodule normed_module.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentMassSealed CurrentWeakSequenceLimit
  MeasureUP RadonMeasureUP MeasureIntegralUP MeasureIntegralBounds
  MeasureIntegralUniqueness SummableRealFunctionUP
  RealMetricBackground MetricProductBackground TopologicalProductMaps
  CompactCarriedContinuousIntegral CurrentAffineWeightUniform
  CurrentAffineWeightContinuity CurrentWeightedApproximationMassLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory
  numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentAffineWeightMassLimit.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables nu j : nat.
Variable V : set (R_n R nu).
Hypothesis hV : forall y, V y -> norm_domain_interior
  (inner_norm (@euclidean_inner_productP R nu)) V y.
Local Notation C := (@current_space R h2 nu V hV j).
Local Notation M := (@CurrentMass.value R h2 nu j V hV).
Variables (P : nat -> C) (Q : C).
Hypothesis hWeak : @is_current_weak_sequence_limit R h2 nu j V hV P Q.
Variable X : metricType R.
Variable mu : set X -> \bar R.
Hypotheses (hm : is_measure mu) (hr : is_radon_measure mu).
Variable mass : R.
Hypothesis hMass : mu setT=mass%:E.
Variable K : set X.
Hypotheses (hK : compact K) (hCarried : mu (~` K)=0).
Variable Y : lmodType R.
Variable NY : Y -> R.
Hypothesis hNY : is_real_norm NY.
Local Notation YT := (real_norm_metric_space hNY).
Variables (f g : X -> YT) (a b : nat -> X -> YT).
Variable sigma : X -> R^o.
Variable eta : nat -> R.
Variable m : nat.
Hypotheses (hF : continuous f) (hG : continuous g) (hSigma : continuous sigma).
Hypotheses (hA : forall i, continuous (a i)) (hB : forall i, continuous (b i)).
Hypothesis hAF : forall eps:R, 0<eps -> exists N:nat, forall i:nat, (N<=i)%N ->
  forall x, K x -> NY (a i x-f x)<eps.
Hypothesis hBG : forall eps:R, 0<eps -> exists N:nat, forall i:nat, (N<=i)%N ->
  forall x, K x -> NY (b i x-g x)<eps.
Hypothesis hError : forall eps:R, 0<eps -> exists N:nat, forall i:nat, (N<=i)%N ->
  `|eta i|<eps.
Local Notation Weight := (fun x:X => (NY (g x-f x)*(sigma x)^+m:R^o)).
Local Notation wi := (fun i (x:X) =>
  (NY (b i x-a i x)*(sigma x+eta i)^+m:R^o)).

(** Source for [current_affine_weight_mass_limit]: the preceding
    smooth affine-chain mass estimates imply the exact original
    |g-f|sigma^m variation integral of Federer 4.1.14,
    p. 371. No normality or representation is required of
    the limit current, and no integral witness is a caller premise. *)
Theorem current_affine_weight_mass_limit :
  (forall i, (M (P i)<=measure_lower_integral mu
    (real_total_integrand (wi i)))%E) ->
  (M Q<=measure_lower_integral mu (real_total_integrand Weight))%E.
Proof.
move=> hBound.
have hWeight := @current_affine_weight_continuous R X Y NY hNY f g sigma m
  hF hG hSigma.
have [c hC] := @compact_carried_continuous_integral_exists
  R X mu hm hr mass hMass K hK hCarried Weight hWeight.
have hValue := @measure_lower_integral_unique R X mu _ _ _
  (measure_lower_integral_specification mu (real_total_integrand Weight)) hC.2.2.
rewrite hValue.
apply: (@current_weighted_approximation_mass_limit R h2 nu j V hV P Q hWeak
  X mu hm hr mass hMass K hK hCarried wi Weight c _ hC _ hBound).
- move=> i.
  have hShift : continuous (fun x:X => (sigma x+eta i:R^o)).
    have hConstant:continuous (fun _:X => (eta i:R^o)).
      by move=>x;exact:cvg_cst.
    move=> x.
    exact: (@cvgD R _ X (nbhs x) (@nbhs_filter X x) sigma
      (fun _:X => eta i) (sigma x) (eta i) (@hSigma x) (@hConstant x)).
  exact: (@current_affine_weight_continuous R X Y NY hNY (a i) (b i)
    (fun x:X => sigma x+eta i) m (@hA i) (@hB i) hShift).
- pose Pair := metric_product YT YT.
  have hPair : continuous (fun x:X => ((g x,f x):Pair)).
    exact: topological_pair_continuous hG hF.
  have hTriple : continuous (fun x:X => (((g x,f x),sigma x):
      metric_product Pair (real_line_metric R))).
    exact: topological_pair_continuous hPair hSigma.
  have hImage := continuous_compact (continuous_subspaceT hTriple) hK.
  exact: (@current_affine_weight_uniform R X Y NY hNY K f g a b sigma eta m
    hImage hAF hBG hError).
Qed.
End CurrentAffineWeightMassLimit.
