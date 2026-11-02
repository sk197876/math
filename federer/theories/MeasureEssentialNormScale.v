(** Federer (1969), 2.4.12, pp. 86–87: absolute homogeneity at the infinity
    endpoint, using zero times infinity equal to zero. The theorem below
    retains exact partial domains; Source context and conventions:
    MeasureEssentialNormUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import RealNormUP PartialFunctionUP PartialNormedArithmetic MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureEssentialNorm MeasureEssentialNormAttainment MeasureEssentialNormComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_essential_norm_scale_bound]: one-sided
    homogeneity estimate for phi_(infinity) in Federer 2.4.12,
    pp. 86–87. It includes the zero scalar. *)
Lemma measure_essential_norm_scale_bound (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_seminorm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (c : R) (f : partial_function X V) :
  measure_almost_everywhere mu (partial_function_domain f) ->
  measure_essential_norm mu N (partial_vector_scale c f) <= `|c|%:E * measure_essential_norm mu N f.
Proof.
move=> hf; apply: (@measure_essential_norm_of_almost_bound R X V mu hm N (partial_vector_scale c f) _).
- apply: mule_ge0; first by rewrite lee_fin normr_ge0.
  exact: measure_essential_norm_nonnegative.
- have hb := @measure_essential_norm_almost_bound R X V mu hm N f hf.
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hb).
  move=> x [y [hy hny]]; exists (c *: y)%R; split.
  + apply/partial_vector_scale_graph; exists y; by split.
  + rewrite (real_seminorm_scale hN) EFinM.
    apply: lee_wpmul2l _ hny; by rewrite lee_fin normr_ge0.
Qed.

(** Source for [measure_essential_norm_scale]: absolute
    homogeneity at p=infinity in Federer 2.4.12,
    pp. 86–87, for all real scalars with the
    stipulated zero-times-infinity convention. *)
Theorem measure_essential_norm_scale (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_seminorm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (c : R) (f : partial_function X V) :
  measure_almost_everywhere mu (partial_function_domain f) ->
  measure_essential_norm mu N (partial_vector_scale c f) = `|c|%:E * measure_essential_norm mu N f.
Proof.
move=> hf; apply/eqP; rewrite eq_le; apply/andP; split.
- exact (@measure_essential_norm_scale_bound R X V N hN mu hm c f hf).
- case: (eqVneq c 0%R)=> [->|hc].
  + rewrite normr0 mul0e; exact: measure_essential_norm_nonnegative.
  + have hcf : measure_almost_everywhere mu (partial_function_domain (partial_vector_scale c f)).
      apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hf).
      move=> x [y hy]; exists (c *: y)%R; apply/partial_vector_scale_graph; exists y; by split.
    have he : measure_almost_equal mu (partial_vector_scale (c^-1)%R (partial_vector_scale c f)) f.
      apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hf).
      move=> x [y hy]; exists y; split=> //.
      apply/partial_vector_scale_graph; exists (c *: y)%R; split.
      * apply/partial_vector_scale_graph; exists y; by split.
      * by rewrite scalerA mulVf // scale1r.
    have heN := @measure_essential_norm_almost_equal R X V mu hm N _ f he.
    have hb := @measure_essential_norm_scale_bound R X V N hN mu hm (c^-1)%R (partial_vector_scale c f) hcf.
    rewrite heN normrV ?unitfE // in hb.
    have hcpos : 0 <= `|c|%:E by rewrite lee_fin normr_ge0.
    have hm' := @lee_wpmul2l R `|c|%:E hcpos _ _ hb.
    rewrite muleA -EFinM mulfV ?normr_eq0 // mul1e in hm'.
    exact hm'.
Qed.
