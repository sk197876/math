(** Federer (1969), 2.5.9, p. 100: "therefore mu has a unique phi_(1)
    continuous extension mu_1 to L_1(phi)". The erratum p. 2, book p. 100
    lines 21–24, replaces L_1(phi) by the total space and records that L+ is
    dense in its positive cone. Two maps with the laws of
    [is_dominated_lone_extension] are linear and bounded by phi_(1), hence
    1-Lipschitz for phi_(1); they agree on L+, which is dense in the
    positive cone, and every function is the difference of its positive and
    negative parts. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP FunctionLatticeUP FunctionLatticeRegularityUP
  RealIntegralFunctionalUP FunctionLatticeSeminormUP VectorFunctionLattice
  TotalScalarLpUP TotalScalarLpLattice TotalScalarLpFiniteSeminorm
  FunctionSeminormDistance ScalarLipschitzExtensionUP DenseScalarExtensionUniqueness
  RegularLatticeLoneDensity PositiveDifferenceFunctional DominatedLoneExtensionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [dominated_lone_extension_lipschitz]: supporting
    lemma for the uniqueness of mu_1 in Federer 2.5.9, p. 100:
    linearity and the bound |mu_1(f)| <= phi_(1)(f) give
    |mu_1(f)-mu_1(g)| <= phi_(1)(f-g) for f, g in the total
    space. *)
Lemma dominated_lone_extension_lipschitz (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (L : set (X -> R)) (A S : (X -> R) -> R) :
  is_dominated_lone_extension mu L A S ->
  is_scalar_lipschitz_on_set (total_scalar_lp mu 1)
    (function_seminorm_distance (finite_total_scalar_lp_norm mu 1)) S.
Proof.
move=> [hS [_ hb]] f g hf hg.
have hV := @total_scalar_lp_vector_lattice R X mu hm 1 (lexx _).
rewrite -(@vector_lattice_additive_difference R X _ S hV hS.1 f g hf hg).
exact: hb _ (@vector_function_lattice_difference R X _ hV f g hf hg).
Qed.

(** Source for [dominated_lone_extension_unique]: the uniqueness
    of the continuous extension mu_1 in Federer 2.5.9, p. 100,
    with the total-domain space and the positive-cone density of
    the erratum p. 2, book p. 100 lines 21–24. Only the
    representation of F by the L regular measure is used; neither
    monotonicity of F nor the Daniell property of A is needed. *)
Theorem dominated_lone_extension_unique (R : realType) (X : choiceType)
    (L : set (X -> R)) (hL : is_function_lattice L) (F A : (X -> R) -> R)
    (mu : set X -> \bar R) (hm : is_measure mu) (S T : (X -> R) -> R) :
  is_real_integral_functional mu L F -> is_function_lattice_regular L mu ->
  is_dominated_lone_extension mu L A S -> is_dominated_lone_extension mu L A T ->
  forall f, total_scalar_lp mu 1 f -> S f = T f.
Proof.
move=> hF hr hS hT.
have hV := @total_scalar_lp_vector_lattice R X mu hm 1 (lexx _).
have hN := @finite_total_scalar_lp_norm_laws R X mu hm 1.
pose W := positive_function_lattice (total_scalar_lp mu 1).
pose D := positive_function_lattice L.
pose d := function_seminorm_distance (finite_total_scalar_lp_norm mu 1).
have [hd0 [hdiag [hsym htri]]] := @function_seminorm_distance_laws R X _ _ hV hN.
have hpm : is_pseudometric_on_set W d.
  split; first by move=> f g hf hg; exact: hd0 _ _ hf.1 hg.1.
  split; first by move=> f hf; exact: hdiag _ hf.1.
  split; first by move=> f g hf hg; exact: hsym _ _ hf.1 hg.1.
  by move=> f g h hf hg hh; exact: htri _ _ _ hf.1 hg.1 hh.1.
have hDW : forall f, D f -> W f.
  move=> f [hf hf0]; split=> //.
  exact: (@represented_lattice_in_total_lone R X mu hm L F hF f hf).
have hdense := @regular_positive_lattice_lone_dense R X L F hL mu hm hF hr.
have hlip : forall U, is_dominated_lone_extension mu L A U ->
    is_scalar_lipschitz_extension W D d A U.
  move=> U hU; split; first by move=> f [hf _]; exact: hU.2.1 f hf.
  move=> f g hf hg; exact: (@dominated_lone_extension_lipschitz R X mu hm L A U hU f g hf.1 hg.1).
have hpos : forall f, W f -> S f = T f.
  exact: (@dense_scalar_lipschitz_extension_unique R _ W D d A S T hpm hDW hdense (hlip S hS) (hlip T hT)).
move=> f hf.
have [hp hq] := @positive_parts_membership R X _ hV.1 f hf.
rewrite -(positive_parts_difference f).
rewrite (@vector_lattice_additive_difference R X _ S hV hS.1.1 _ _ hp.1 hq.1).
rewrite (@vector_lattice_additive_difference R X _ T hV hT.1.1 _ _ hp.1 hq.1).
by rewrite (hpos _ hp) (hpos _ hq).
Qed.
