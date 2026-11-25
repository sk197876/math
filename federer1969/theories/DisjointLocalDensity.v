(** Federer (1969), 2.5.10, p. 101, first paragraph: gluing the local
    representing densities on disjoint measurable pieces. The theorem below
    proves measurability, a common pointwise bound, and the integral formula
    on every individual piece; passing to arbitrary summable tests is a
    separate step. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric MeasureUP MeasureRestriction MeasurableFunctionUP
  FunctionLatticeSeminormUP TotalScalarLpUP TotalScalarLpFiniteSeminorm
  MeasureIntegralUP SummableRealFunctionUP LpFunctionalDensityUP
  FiniteMeasureDecompositionUP DisjointFunctionGluingUP DisjointFunctionGluing
  DisjointDensityMeasurability TotalScalarCutoff RestrictedTotalLone RestrictedLoneFunctional
  FinitePieceBoundedDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [disjoint_local_density_exists]: supporting gluing step for
    Federer 2.5.10, p. 101 The resulting density need not have countably
    measurable support, which is exactly the relaxation discussed in the
    book. *)
Theorem disjoint_local_density_exists (R : realType) (X J : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (D : set J) (B : J -> set X)
    (A : (X -> R) -> R) (M : R) :
  is_finite_measure_decomposition mu D B -> (0 <= M)%R ->
  is_linear_functional_on_functions (total_scalar_lp mu 1) A ->
  (forall f, total_scalar_lp mu 1 f -> (`|A f| <= M * finite_total_scalar_lp_norm mu 1 f)%R) ->
  exists k : X -> R, is_measure_measurable_function mu (total_scalar_function k) /\
    (forall x, (`|k x| <= M)%R) /\
    forall j, D j -> forall f, total_scalar_lp mu 1 f ->
      is_measure_integral mu (real_total_integrand (fun x => (total_scalar_cutoff (B j) f x * k x)%R))
        (A (total_scalar_cutoff (B j) f))%:E.
Proof.
move=> hD hM hA hb.
have hp j : exists k : X -> R,
    (D j -> is_lp_functional_density (measure_restrict mu (B j)) 1 +oo
      (restricted_total_lone_functional (B j) A) k) /\ forall x, (`|k x| <= M)%R.
  case: (pselect (D j))=> hj.
  - have [k [hk hbound]] := @finite_piece_bounded_functional_density R X mu hm (B j) A M
      (hD.1 j hj).1 (hD.1 j hj).2 hM hA hb.
    exists k; by split.
  - exists (fun _ => 0%R); split; first by move=> hx; exfalso; exact: hj hx.
    by move=> x; rewrite normr0.
pose f j := projT1 (cid (hp j)).
have hf j := projT2 (cid (hp j)).
pose k := @disjoint_function_gluing R X J D B f hD.2.1.
have hk := @disjoint_function_gluing_specification R X J D B f hD.2.1.
exists k; split.
- apply: (@disjoint_density_gluing_measurable R X J mu hm D B f k hD hk)=> j hj.
  exact: ((hf j).1 hj).1.2.1.
- split.
  + move=> x; case: (pselect ((\bigcup_(j in D) B j) x))=> [[j hj hx]|hx].
    * rewrite /k (hk.1 j x hj hx); exact: (hf j).2.
    * by rewrite /k (hk.2 x hx) normr0.
  + move=> j hj u hu.
    have hul := @total_lone_for_restricted_measure R X mu hm (B j) u (hD.1 j hj).1 hu.
    have hi := ((hf j).1 hj).2 u hul.
    have hglobal := (proj1 (@restricted_real_integral_cutoff_iff R X mu hm (B j)
      (fun x => (u x * f j x)%R) _ (hD.1 j hj).1)) hi.
    have he : total_scalar_cutoff (B j) (fun x => (u x * f j x)%R)=
        (fun x => (total_scalar_cutoff (B j) u x * k x)%R).
      apply: funext=> x; case: (pselect (B j x))=> hx.
      * by rewrite !total_scalar_cutoff_on // /k (hk.1 j x hj hx).
      * by rewrite !total_scalar_cutoff_off // mul0r.
    by rewrite he in hglobal.
Qed.
