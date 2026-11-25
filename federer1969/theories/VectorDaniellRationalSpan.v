(** Federer (1969), 2.5.12, p. 104, third paragraph of the proof: a
    countable dense subset D of E which is a vector space over the rational
    field, and the statement that phi almost all points x of X satisfy
    k_{ry+sz}(x) = r k_y(x) + s k_z(x) and |k_y(x)| <= nu(y) for all y, z in
    D and r, s in Q. The rational subspace is the set of finite rational
    combinations of an enumeration of a countable dense set, which exists by
    hypothesis (1). The densities k_y are specified by the conclusions of
    2.5.9 for every y in E; the almost everywhere statement holds for every
    countable D and is derived from the almost uniqueness of the densities
    of mu_{ry+sz}. The extension of y -> k_y(x) to a member k(x) of the unit
    ball of E*, the measurability statements and the final representation of
    T are not formalised here. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From mathcomp Require Import ring lra.
From Federer Require Import RealNormUP NormMetric RealMetricBackground FunctionLatticeUP
  MeasureUP RealIntegralFunctionalUP FunctionLatticeRegularityUP CountablyMeasurableUP
  SummableRealFunctionUP SummableRealArithmetic MeasureIntegralUP TotalScalarLpUP
  TotalScalarLpClosure RealLatticeDensityUP MeasureAlmostUP MeasureAlmostBasic
  VectorDaniellHypotheses VectorDaniellVariationIntegral VectorDaniellDensities.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section RationalSpan.
Variable R : realType.
Variable E : lmodType R.
Variable N : E -> R.
Hypothesis hN : is_real_norm N.

(** Source for [is_rational_dense_subspace]: the countable dense subset
    D of E which is a vector space over the rational field, Federer
    2.5.12, p. 104. *)
Definition is_rational_dense_subspace (D : set E) : Prop :=
  countable D /\ dense (D : set (real_norm_metric_space hN)) /\ D 0 /\
  forall (r s : rat) (y z : E), D y -> D z -> D (ratr r *: y + ratr s *: z).

(** Source for [rational_combination]: the finite rational combination
    sum_i r_i e(n_i) of terms of a sequence e in E, used to obtain the
    rational vector space D of Federer 2.5.12, p. 104. *)
Definition rational_combination (e : nat -> E) (s : seq (rat * nat)) : E :=
  \sum_(p <- s) ratr p.1 *: e p.2.

(** Source for [rational_combination_cat]: the combination of a
    concatenation is the sum of the combinations, Federer 2.5.12,
    p. 104. *)
Lemma rational_combination_cat (e : nat -> E) (s1 s2 : seq (rat * nat)) :
  rational_combination e (s1 ++ s2) = rational_combination e s1 + rational_combination e s2.
Proof. by rewrite /rational_combination big_cat. Qed.

(** Source for [rational_combination_scale]: a rational multiple of a
    combination is a combination, Federer 2.5.12, p. 104. *)
Lemma rational_combination_scale (e : nat -> E) (r : rat) (s : seq (rat * nat)) :
  ratr r *: rational_combination e s = rational_combination e [seq (r * p.1, p.2) | p <- s].
Proof.
rewrite /rational_combination big_map scaler_sumr; apply: eq_bigr=> p _ /=.
by rewrite scalerA rmorphM.
Qed.

(** Source for [dense_superset]: a set containing a dense set is dense,
    used for the density of D in Federer 2.5.12, p. 104. *)
Lemma dense_superset (A B : set (real_norm_metric_space hN)) : dense A -> A `<=` B -> dense B.
Proof.
move=> hA hAB O hO hOo; have [x [hx1 hx2]] := hA O hO hOo.
by exists x; split=> //; exact: hAB.
Qed.

(** Source for [rational_dense_subspace_exists]: a separable normed
    space contains a countable dense subset which is a vector space over
    the rational field, Federer 2.5.12, p. 104, "we choose a countable
    dense subset D of E such that D is a vectorspace over the rational
    field Q". *)
Theorem rational_dense_subspace_exists :
  is_separable_normed_space hN -> exists D, is_rational_dense_subspace D.
Proof.
move=> [D0 [hc hd]].
have /countable_injP [f hf] := hc.
pose e (n : nat) : E := xget 0 [set x : E | D0 x /\ f x = n].
have he : forall x : E, D0 x -> e (f x) = x.
  move=> x hx; have hex : exists u : E, D0 u /\ f u = f x by exists x.
  have [hu hfu] := xgetPex 0 hex.
  exact: hf (mem_set hu) (mem_set hx) hfu.
pose D := [set rational_combination e s | s in [set: seq (rat * nat)]].
exists D; split.
  by apply: sub_countable (card_image_le _ _) _; exact: countableP.
split.
  apply: (dense_superset hd) => x hx.
  exists [:: ((1 : rat), f x)] => //.
  by rewrite /rational_combination big_seq1 /= rmorph1 scale1r he.
split.
  by exists [::] => //; rewrite /rational_combination big_nil.
move=> r s y z [s1 _ <-] [s2 _ <-].
exists ([seq (r * p.1, p.2) | p <- s1] ++ [seq (s * p.1, p.2) | p <- s2]) => //.
by rewrite rational_combination_cat -!rational_combination_scale.
Qed.

End RationalSpan.

Section RationalLinearity.
Variable R : realType.
Variable X : choiceType.
Variable E : lmodType R.
Variable N : E -> R.
Hypothesis hN : is_real_norm N.
Variable L : set (X -> R).
Variable Q : set (X -> E).
Variable T : (X -> E) -> R.
Hypothesis hL : is_function_lattice L.
Hypothesis hQ : is_vector_function_space Q.
Hypothesis hM : is_vector_lattice_module hN L Q.
Hypothesis hT : is_vector_variation_functional N L Q T.

Local Notation Lp := (positive_function_lattice L).
Local Notation lam := (variation_integral N Q T).

Variable phi : set X -> \bar R.
Hypothesis hphi : is_measure phi.
Hypothesis hrep : is_real_integral_functional phi Lp lam.
Hypothesis hreg : is_function_lattice_regular Lp phi.
Hypothesis hX : measure_countably_measurable phi setT.

(** Source for [is_component_density_family]: a choice of the functions
    k_y in L_oo(phi) with mu_y(f) = int f k_y dphi for f in L+ and
    phi_(oo)(k_y) <= nu(y), one for each y, Federer 2.5.12, p. 104. *)
Definition is_component_density_family (k : E -> X -> R) : Prop :=
  forall y, is_real_lattice_density phi Lp (component_integral T y) (k y) /\
    total_scalar_lp phi +oo (k y) /\ (total_scalar_lp_norm phi +oo (k y) <= (N y)%:E)%E.

(** Source for [component_density_family_exists]: such a choice exists,
    by 2.5.9 applied for every y, Federer 2.5.12, p. 104. *)
Lemma component_density_family_exists : exists k, is_component_density_family k.
Proof.
pose h := fun y => component_density hL hQ hM hT hphi hrep hreg y hX.
by exists (fun y => sval (cid (h y))) => y; exact: (svalP (cid (h y))).
Qed.

(** Source for [component_integral_combination]: the identity
    mu_{ay+bz} = a mu_y + b mu_z on L+, from the linearity of T,
    Federer 2.5.12, p. 104. *)
Lemma component_integral_combination (a b : R) (y z : E) (f : X -> R) :
  Lp f -> component_integral T (a *: y + b *: z) f
    = a * component_integral T y f + b * component_integral T z f.
Proof.
move=> hf; rewrite /component_integral.
have hy := vector_lattice_module_product hM y hf.1.
have hz := vector_lattice_module_product hM z hf.1.
rewrite -(vector_variation_homogeneous hT a hy) -(vector_variation_homogeneous hT b hz).
rewrite -(vector_variation_additive hT (vector_function_space_scale hQ a hy)
  (vector_function_space_scale hQ b hz)).
by congr T; apply/funext=> x; rewrite scalerDr !scalerA (mulrC (f x) a) (mulrC (f x) b).
Qed.

(** Source for [component_density_combination]: a k_y + b k_z is a
    density of mu_{ay+bz}, Federer 2.5.12, p. 104. *)
Lemma component_density_combination (a b : R) (y z : E) (ky kz : X -> R) :
  is_real_lattice_density phi Lp (component_integral T y) ky -> total_scalar_lp phi +oo ky ->
  is_real_lattice_density phi Lp (component_integral T z) kz -> total_scalar_lp phi +oo kz ->
  is_real_lattice_density phi Lp (component_integral T (a *: y + b *: z))
    (fun x => a * ky x + b * kz x).
Proof.
move=> hy hly hz hlz; split.
  exact: (total_scalar_lp_add hphi (total_scalar_lp_scale hphi a hly)
    (total_scalar_lp_scale hphi b hlz)).2.1.
move=> f hf; rewrite component_integral_combination //.
have hi := real_total_integral_add hphi (real_total_integral_scale hphi a (hy.2 f hf))
  (real_total_integral_scale hphi b (hz.2 f hf)).
have -> : (fun x => f x * (a * ky x + b * kz x)) = (fun x => a * (f x * ky x) + b * (f x * kz x)).
  by apply/funext=> x; ring.
exact: hi.
Qed.

(** Source for [component_density_rational_linear]: phi almost all x
    satisfy k_{ry+sz}(x) = r k_y(x) + s k_z(x) and |k_y(x)| <= nu(y) for
    all y, z in D and r, s in Q, for every countable D, Federer 2.5.12,
    p. 104. *)
Theorem component_density_rational_linear (k : E -> X -> R) (D : set E) :
  is_component_density_family k -> countable D ->
  measure_almost_everywhere phi [set x | forall (y z : E) (r s : rat), D y -> D z ->
    k (ratr r *: y + ratr s *: z) x = ratr r * k y x + ratr s * k z x /\ `|k y x| <= N y].
Proof.
move=> hk hD.
pose J := D `*` D `*` [set: rat] `*` [set: rat].
pose P (j : E * E * rat * rat) := [set x | k (ratr j.1.2 *: j.1.1.1 + ratr j.2 *: j.1.1.2) x
  = ratr j.1.2 * k j.1.1.1 x + ratr j.2 * k j.1.1.2 x /\ `|k j.1.1.1 x| <= N j.1.1.1].
have hJ : countable J := countableX (countableX (countableX hD hD) (countableP _)) (countableP _).
have ha : forall j, J j -> measure_almost_everywhere phi (P j).
  move=> [[[y z] r] s] _.
  have [hky [hly hny]] := hk y; have [hkz [hlz _]] := hk z.
  have [hkc _] := hk (ratr r *: y + ratr s *: z).
  have h1 := component_density_unique hL hphi hrep hreg hX hkc
    (component_density_combination (ratr r) (ratr s) hky hly hkz hlz).
  have h2 := component_density_bound hphi hly hny.
  exact: (measure_almost_everywhere_and hphi h1 h2).
have hall := measure_almost_everywhere_countable hphi hJ ha.
apply: (measure_almost_everywhere_mono hphi _ hall) => x hx y z r s hy hz.
exact: (hx (((y, z), r), s) (conj (conj (conj hy hz) I) I)).
Qed.

End RationalLinearity.
