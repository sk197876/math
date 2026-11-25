(** Federer (1969), 4.1.5, p. 350:
    the original M-bounded gauge set equals
    the intersection of the printed evaluation
    inequalities. Monotonicity and finite values
    of M suffice; no homogeneity is used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP FunctionLatticeUP CompactSupportFunctionUP
  DistributionVariationUP DistributionVariationSealed DistributionVariationBasic DistributionVariationBoundedExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DistributionMonotoneGaugeBounds.
Variable R:realType.
Variable X:topologicalType.
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable E:lmodType R.
Variable values:Hom E (GRing.Lmodule.clone R (X->Y) _).
Hypothesis hNormTest:forall phi:E,compactly_supported_continuous_functions (fun x=>NY (values phi x)).
Variable M:(X->R)->R.
Local Notation Kplus := (positive_function_lattice (@compactly_supported_continuous_functions R X)).
Hypothesis hMonotone:forall f g,Kplus f ->Kplus g ->function_le f g ->M f<=M g.

(** Source for [is_original_distribution_gauge_bounded]: the
    original ||S||(f)<=M(f) set in Federer
    4.1.5, p. 350, on K(U)+.
    No Borel variation is substituted. *)
Definition is_original_distribution_gauge_bounded (S:Hom E R^o):Prop:=
  forall f (hf:Kplus f),
    (@DistributionVariation.value R X Y NY hNY E values S f hf.2<=(M f)%:E)%E.

(** Source for [original_distribution_gauge_test_bounds_iff]: the
    equality of the two displayed bounded sets
    in Federer 4.1.5, p. 350. M
    is only monotone and finite-valued. *)
Theorem original_distribution_gauge_test_bounds_iff (S:Hom E R^o):
  is_original_distribution_gauge_bounded S <->
  forall phi:E,S phi<=M (fun x=>NY (values phi x)).
Proof.
have hPositive phi:Kplus (fun x=>NY (values phi x)).
  split; first exact:hNormTest; move=>x; exact:real_seminorm_nonnegative hNY.1 _.
split.
- move=>hBound phi.
  have hGauge:=@DistributionVariation.laws R X Y NY hNY E values S
    (fun x=>NY (values phi x)) (hPositive phi).2.
  have hUpper:=@distribution_variation_upper R X Y NY E values S _ _ hGauge phi (fun x=>lexx _).
  have hM:=@hBound _ (hPositive phi).
  have hFinal:=le_trans hUpper hM; by move:hFinal; rewrite lee_fin.
- move=>hBound f hf.
  have hGauge:=@DistributionVariation.laws R X Y NY hNY E values S f hf.2.
  apply:(@distribution_variation_least_finite_bound R X Y NY E values S f _ (M f) hGauge)=>phi hNorm.
  exact:le_trans (hBound phi) (@hMonotone _ _ (hPositive phi) hf hNorm).
Qed.

(** Source for [original_distribution_test_bounds_finite]: the
    original evaluation inequalities force finite
    gauge on every positive compact test,
    Federer 4.1.5, p. 350. *)
Theorem original_distribution_test_bounds_finite (S:Hom E R^o):
  (forall phi:E,S phi<=M (fun x=>NY (values phi x))) ->
  forall f,Kplus f ->exists b:R,is_distribution_variation_value NY values S f b%:E.
Proof.
move=>hBound f hf.
apply:(@distribution_variation_bounded_value_exists R X Y NY hNY E values S f (M f) hf.2)=>phi hNorm.
have hPositive:Kplus (fun x=>NY (values phi x)).
  split; first exact:hNormTest; move=>x; exact:real_seminorm_nonnegative hNY.1 _.
exact:le_trans (hBound phi) (@hMonotone _ _ hPositive hf hNorm).
Qed.
End DistributionMonotoneGaugeBounds.
