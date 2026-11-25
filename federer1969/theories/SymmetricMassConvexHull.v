(** Federer (1969), 1.10.5, p. 48: supporting convex-hull argument for the
    optimal finite-dimensional decomposition. The positive-degree mass unit
    ball is the convex hull of products of unit-ball factors. The local
    proof reuses the general finite-convex-combination and nearest-point
    arguments of 1.8.1 and 1.7.13, rather than importing a separation
    theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import LinearBasis FiniteOrdinalBasis InnerProductUP InnerProductLaws
  InnerMetric InnerNormedTopology OrthonormalFamilies InnerNearestUP InnerConvex
  CompactNearest NearestConvexVariational SubconvexCombinations SubconvexCompact
  SymmetricAlgebra SymmetricGrading SymmetricMonomialBasis InnerSymmetric
  InnerSymmetricPositivity RealNormUP RealSeminormOperations SymmetricDecompositionCosts
  SymmetricProjectiveMass SymmetricProjectiveSeminorm SymmetricProjectiveMaximality
  SymmetricMassNormingForm SymmetricUnitProducts SymmetricUnitProductsCompact.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Hull.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable N : V -> R.
Hypothesis hN : is_real_norm N.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Variable m : nat.
Hypothesis hm : (0<m)%N.
Local Notation E := (symmetric_power V m).
Local Notation BE := (@symmetric_inner_form R V B hB m).
Local Notation hE := (@symmetric_inner_productP R V B hB m).
Local Notation M := (inner_metric_space hE).
Local Notation S := (@symmetric_unit_products R V N m).
Local Notation C := (@subconvex_combinations R E S).
Local Notation mass := (symmetric_projective_mass (proj1 hN) hm).

(** Source for [symmetric_unit_product_mass_bound]: Federer
    1.10.5, p. 48, a product of unit-ball factors has mass
    at most one, by its one-term decomposition. *)
Lemma symmetric_unit_product_mass_bound x : S x -> mass x<=1.
Proof.
move=> [t [ht ->]]; apply: le_trans (symmetric_projective_mass_tuple_bound (proj1 hN) hm t) _.
apply: (@symmetric_unit_tuple_cost_bound R V N (proj1 hN) m t)=> i; apply: ht; exact: mem_tnth.
Qed.

(** Source for [symmetric_subconvex_mass_bound]: Federer 1.10.5,
    p. 48, supporting triangle inequality for convex combinations
    of unit-factor products. *)
Lemma symmetric_subconvex_mass_bound x : C x -> mass x<=1.
Proof.
move=> [k [u [a [hu [ha [hs ->]]]]]].
have hM := symmetric_projective_mass_seminorm (proj1 hN) hm.
apply: le_trans (real_seminorm_sum hM (fun i => a i *: u i)) _.
apply: le_trans _ hs; apply: ler_sum=> i _.
rewrite (real_seminorm_scale hM) (ger0_norm (ha i)).
have hh := ler_wpM2l (ha i) (symmetric_unit_product_mass_bound (hu i)).
by rewrite mulr1 in hh.
Qed.

(** Source for [symmetric_subconvex_compact]: Federer 1.10.5,
    p. 48, supporting compactness of the unit-product hull.
    The locally proved finite-combination reduction bounds the number
    of terms by the dimension of the symmetric power. *)
Lemma symmetric_subconvex_compact : compact (C : set M).
Proof.
have hs := @symmetric_unit_products_compact R V B hB N hN n e he m.
have hb := finite_ordinal_basis (@symmetric_finite_monomial_basis R V n e he m).
exact (@subconvex_combinations_compact R E BE hE S hs _ _ hb).
Qed.

(** Source for [symmetric_mass_unit_ball_iff_subconvex]: Federer
    1.10.5, p. 48, supporting hull characterization for the
    attained infimum. An excluded point is separated by the linear
    functional associated with its residual from a nearest point.
    The mass maximality estimate contradicts that separation. *)
Theorem symmetric_mass_unit_ball_iff_subconvex x : mass x<=1 <-> C x.
Proof.
split; last exact: symmetric_subconvex_mass_bound.
move=> hx1; apply: contrapT=> hnot.
have hn : C !=set0 by exists 0; exact: subconvex_combinations_zero.
have [c hc] := @compact_inner_nearest_exists R E BE hE x C hn symmetric_subconvex_compact.
pose f := inner_coordinate hE (x-c).
have hupper y : S y -> f y<=f c.
  move=> hy; have hyC : C y := subconvex_combinations_include hy.
  have hv := @inner_nearest_convex_variational R E BE hE C
    (@subconvex_combinations_convex R E S) x c hc y hyC.
  rewrite (inner_symmetric hE) in hv.
  have hh : f (y-c)<=0 by rewrite /f inner_coordinateE.
  by rewrite linearB subr_le0 in hh.
have hd : 0<=f c.
  have hh := hupper 0 (symmetric_unit_products_zero hN hm).
  by rewrite linear0 in hh.
have habs y : S y -> `|f y|<=f c.
  move=> hy; rewrite ler_norml; apply/andP; split; last exact: hupper hy.
  have hh := hupper (-y) (symmetric_unit_products_negate hN hm hy).
  by rewrite linearN lerNl in hh.
have hQ := @real_seminorm_linear_precompose R E R^o (fun r:R=>`|r|)
  (proj1 (scalar_absolute_value_norm R)) f (linearP f).
have hword t : `|f (SymmetricFormIsomorphism.symmetric_tuple_component t)| <=
    f c * symmetric_tuple_cost N t.
  have [y [hy hyE]] := symmetric_product_normalized hN t.
  rewrite hyE linearZ normrM (ger0_norm (symmetric_tuple_cost_nonnegative (proj1 hN) t)) mulrC.
  exact (ler_wpM2r (symmetric_tuple_cost_nonnegative (proj1 hN) t) (habs y hy)).
have hb := @symmetric_projective_mass_maximal R V N (proj1 hN) m hm
  (fun z => `|f z|) hQ (f c) hd hword x.
have hmul := ler_wpM2l hd hx1; rewrite mulr1 in hmul.
have heval := le_trans (ler_norm (f x)) (le_trans hb hmul).
have hr : x-c!=0.
  apply/eqP=> hz; apply: hnot.
  have hxc : x=c by apply/eqP; rewrite -subr_eq0 hz.
  rewrite hxc; exact: inner_nearest_member_law hc.
have hp : 0 < f (x-c) by rewrite /f inner_coordinateE (inner_positive hE).
rewrite linearB subr_gt0 in hp.
have hh := lt_le_trans hp heval; by rewrite ltxx in hh.
Qed.
End Hull.
