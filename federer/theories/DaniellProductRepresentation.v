(** Federer (1969), 2.6.4, p. 119, final assertion as corrected in the May
    1987 erratum, p. 2, book p. 119 line 19: nu(h) equals the integral of h
    against alpha times beta for every h in K(X times Y). We prove this
    through the actual product measure and uniqueness of the Daniell
    product. The proof works for any measures representing the two factor
    functionals, so K-regularity is unnecessary for this formula. No
    regularity of the product is asserted. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import CompactSupportFunctionUP CompactSupportFunctionLattice CompactSeparatedProduct
  CompactProductIntegrability DaniellIntegralUP DaniellProductUP DaniellProductUniqueness
  RealIntegralFunctionalUP RealIntegralFunctional MonotoneDaniellIntegralSum
  MeasureUP MeasureIntegralUP MeasureIntegralUniqueness SummableRealFunctionUP ProductMeasure SeparatedProductIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [daniell_product_measure_representation]: exact
    corrected formula in Federer 2.6.4, p. 119,
    erratum p. 2, book p. 119 line 19. The
    factor regularity hypotheses can be dropped for this representation
    formula once actual representing measures are supplied. *)
Theorem daniell_product_measure_representation (R : realType) (X Y : topologicalType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta)
    (A : (X -> R) -> R) (B : (Y -> R) -> R) (C : ((X*Y) -> R) -> R) :
  hausdorff_space X -> locally_compact (@setT X) -> hausdorff_space Y -> locally_compact (@setT Y) ->
  is_real_integral_functional alpha (@compactly_supported_continuous_functions R X) A ->
  is_real_integral_functional beta (@compactly_supported_continuous_functions R Y) B ->
  is_daniell_product A B C ->
  forall h, compactly_supported_continuous_functions h ->
    is_measure_integral (product_measure ha hb) (real_total_integrand h) (C h)%:E.
Proof.
move=> hX hlX hY hlY hA hB hC.
have hAs f : compactly_supported_continuous_functions f -> summable_real_functions alpha f.
  move=> hf; exists (A f); exact: hA f hf.
have hBs g : compactly_supported_continuous_functions g -> summable_real_functions beta g.
  move=> hg; exists (B g); exact: hB g hg.
pose L := @compactly_supported_continuous_functions R (X*Y)%type.
have hLs : L `<=` summable_real_functions (product_measure ha hb).
  move=> h hh; exact (@compact_product_function_summable R X Y alpha beta ha hb h hX hlX hY hlY hAs hBs hh).
pose J := @lattice_measure_integral R (Choice.clone (X*Y)%type _) _ L hLs.
have hJi := @lattice_measure_integral_specification R (Choice.clone (X*Y)%type _) _ L hLs.
have hlat := @compactly_supported_continuous_functions_lattice R (X*Y)%type.
have hJm := @real_integral_functional_is_monotone_daniell R (Choice.clone (X*Y)%type _) _
  (product_measure_is_measure ha hb) L J hlat hJi.
have hJ : is_daniell_product A B J.
  split; first exact: monotone_daniell_integral_is_daniell hJm.
  move=> f g hf hg.
  have hi := @separated_product_integral R X Y alpha beta ha hb f g (A f) (B g) (hA f hf) (hB g hg).
  have hj := hJi _ (@compactly_supported_separated_product R X Y f g hf hg).
  exact: EFin_inj (measure_integral_unique hj hi).
move=> h hh; have he := @daniell_product_unique R X Y A B C J hX hlX hY hlY hC hJ h hh.
rewrite he; exact: hJi h hh.
Qed.
