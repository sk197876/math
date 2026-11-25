(** Federer (1969), 2.6.4, pp. 118–119: L1 density of the canonical tensor
    embedding for arbitrary measures. The total-domain convention follows
    erratum p. 2, book p. 119 lines 3, 4, 6. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal.
From Federer Require Import CharacteristicFunctionUP ModuleQuotient MeasureUP MeasureIntegralUP ProductMeasure
  SummableRealFunctionUP SummableTensorImage SummableRectangleIndicators ProductCharacteristicDensity
  SubspaceLoneApproximationUP SubspaceLoneDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Density.
Variable R : realType.
Variables X Y : choiceType.
Variables (alpha : set X -> \bar R) (beta : set Y -> \bar R).
Variables (ha : is_measure alpha) (hb : is_measure beta).
Local Notation F := (GRing.Lmodule.clone R ((X*Y) -> R^o) _).

(** Source for [summable_tensor_image_subspace]: supporting
    linear-subspace laws for the density assertion of Federer
    2.6.4, pp. 118–119. *)
Definition summable_tensor_image_subspace : subspace F.
Proof.
refine (@Subspace R F (separated_summable_image ha hb) _ _ _).
- exact: separated_summable_image_zero.
- move=> f g hf hg; exact (@separated_summable_image_add R X Y alpha beta ha hb f g hf hg).
- move=> c f hf; exact (@separated_summable_image_scale R X Y alpha beta ha hb c f hf).
Defined.

(** Source for [summable_tensor_image_dense]: density of the
    monomorphism's image in Federer 2.6.4, pp. 118–119,
    with arbitrary positive error measured by the actual absolute
    integral. No sigma-finiteness of either measure is required. *)
Theorem summable_tensor_image_dense f e :
  summable_real_functions (product_measure ha hb) f -> 0<e ->
  exists (h : (X*Y) -> R) (q : R), separated_summable_image ha hb h /\
    is_measure_integral (product_measure ha hb)
      (real_total_integrand (fun p => `|h p-f p|)) q%:E /\ q<e.
Proof.
move=> hf he.
have hLs g : summable_tensor_image_subspace g -> summable_real_functions (product_measure ha hb) g.
  exact (@separated_summable_image_summable R X Y alpha beta ha hb g).
have hchar A s : measure_measurable (product_measure ha hb) A ->
    (product_measure ha hb A < +oo)%E -> is_characteristic_function A s ->
    is_subspace_lone_approximable (product_measure ha hb) summable_tensor_image_subspace s.
  move=> hA hfin hs; split.
  - exact (@finite_characteristic_summable R (Choice.clone (X*Y)%type _) _
      (product_measure_is_measure ha hb) A s hs hA hfin).
  - move=> d hd; exact (@product_characteristic_lone_dense R X Y alpha beta ha hb A s d hA hfin hs hd).
have hd := @subspace_summable_total_density R (Choice.clone (X*Y)%type _) _
  (product_measure_is_measure ha hb) summable_tensor_image_subspace hLs hchar f hf.
exact: hd.2 e he.
Qed.
End Density.
