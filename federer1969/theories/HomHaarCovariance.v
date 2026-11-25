(** Federer (1969), 2.7.16, example (2), printed p. 136: "Suppose U and V
    are vectorspaces with dim U = m <= dim V = n < oo. The linear group G of
    V acts (by functional composition) on the vectorspace X = Hom(U, V) of
    all linear maps of U into V. If phi is a Haar measure of the additive
    group of X, then phi is |det|^{-m} covariant with respect to the action
    of G. In fact, using a base e_1, ..., e_m of U we construct a G action
    preserving isomorphism X ~ V^m by mapping f in X onto (f(e_1), ...,
    f(e_m)) in V^m." Here U and V carry inner products and finite bases, X =
    Hom(U, V) carries the topology of the inner product of 1.7.9
    (HomSpaceTopology.v), and G is the linear group of V of
    LinearGroupTopology.v with the sealed operations of LinearGroupSealed.v;
    g in G acts on X by A(g, f) = g o f (hom_linear_group_action). The
    determinant of g is det g of 1.3.4, p. 16 (linear_group_det), a
    continuous homomorphism of G into R ~ {0}. The isomorphism X ~ V^m is
    hom_base_values; it is linear, bijective and carries g o f to
    (g(f(e_1)), ..., g(f(e_m))). The covariance means, in the sense of
    2.7.1, p. 122, that mu(u o A_g) = |det g|^{-m} mu(u) for u in K(X), g in
    G, for the integral mu associated with phi (hom_haar_integral_covariant,
    hom_haar_measure_covariant). X is not a homogeneous space of G (the
    orbit of 0 is {0}); the definitions of 2.7.1 only require the action A,
    and the covariance identity is stated for it. The proof uses the base of
    X corresponding to the base of V^m: the determinant of f |-> g o f is
    (det g)^m (HomCompositionDeterminant.v), and every Haar integral of X
    satisfies mu(u o T) = |det T|^{-1} mu(u) for linear automorphisms T
    (FiniteHaarLinear.v), the identity of 2.7.16, p. 135, transported to X.
    The hypothesis m <= n is not needed for the covariance. The same
    argument gives mu(u o R_h) = |det h|^{-p} mu(u) for right composition
    R_h(f) = f o h on Hom(V, W), p = dim W (hom_haar_integral_right), used
    for "phi is right |det|^n covariant" on p. 137. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module.
From mathcomp Require Import fingroup perm.
From Federer Require Import RealMetricBackground InnerProductUP InnerNorm InnerMetric InnerNormedTopology
  LinearBasis FiniteDualDimension Annihilator OrthonormalFamilies OrthonormalisationUP GramSchmidt
  InnerFiniteSynthesis InnerCoordinateContinuity TensorUP Hom HomInner CoefficientCoordinates
  ExteriorDeterminant ExteriorLeibniz InversionCount TopExteriorInjectivity EuclideanLinearMaps
  MeasureUP CompactSupportFunctionUP FunctionLatticeRegularityUP RealIntegralFunctionalUP
  MonotoneDaniellIntegralUP CovariantIntegralUP HaarIntegralUP TopologicalGroupUP
  TopologicalProductMaps IsotropyGroupTopology HomSpaceTopology LinearGroupTopology LinearGroupSealed
  BlockDeterminant HomCompositionDeterminant FiniteHaarLinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [det_nonzero_injective]: det f <> 0 if and only if f is
    univalent, Federer 1.3.4, p. 16, with the top exterior power
    criterion of 1.7.6, p. 34 (top_exterior_nonzero_iff_injective);
    the general form of euclidean_det_injective, supporting "the linear
    group G of V", 2.7.16, p. 136. Supporting lemma. *)
Lemma det_nonzero_injective (K : fieldType) (h2 : (1 + 1 : K) != 0) (V : lmodType K) n
    (b : 'I_n -> V) (hb : is_basis b) (f : {linear V -> V}) :
  det h2 hb f != 0 <-> injective f.
Proof.
have h := @top_exterior_nonzero_iff_injective K h2 V V n b hb f.
rewrite -h; split.
- move=> hd; exists (top_vector b); rewrite (detE h2 hb).
  apply/eqP=> h0; move/eqP: hd; apply.
  apply: (@top_scalar_injective K h2 n V b hb).
  by rewrite /= h0 scale0r.
- move=> [x]; rewrite (detE h2 hb); apply: contraNneq=> ->.
  by rewrite scale0r.
Qed.

Section LinearGroupDeterminant.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Local Notation H := (inner_metric_space (hom_inner_productP hB hB hb)).
Local Notation VT := (inner_metric_space hB).
Local Notation GL := (set_type (linear_group hB hb)).
Local Notation mul := (linear_group_mul hB hb).
Local Notation inv := (linear_group_inv hB hb).
Local Notation unit := (linear_group_unit hB hb).
Local Notation hG := (linear_group_operations hB hb).

(** Source for [hom_det]: det f for f in Hom(V, V), Federer 1.3.4,
    p. 16, as used in "|det|" in 2.7.16, pp. 136–137. Definition. *)
Definition hom_det (f : Hom V V) : R := det (euclidean_two_nonzero R) hb (hom_as_linear f).

(** Source for [linear_group_det]: det g for g in the linear group G of
    V, Federer 2.7.16, pp. 136–137, with det of 1.3.4, p. 16.
    Definition; for V = R^n with the standard base it is
    general_linear_det of GeneralLinearPunctured.v. *)
Definition linear_group_det (g : GL) : R := hom_det (set_val g).

(** Source for [linear_group_det_nonzero]: det g <> 0 for g in G,
    Federer 1.3.4, p. 16; supporting 2.7.16, p. 136. *)
Lemma linear_group_det_nonzero (g : GL) : linear_group_det g != 0.
Proof. by apply/(det_nonzero_injective _ _ _).2; exact: set_valP g. Qed.

(** Source for [linear_group_det_mul]: det(g h) = det g . det h for g, h
    in G, Federer 1.3.4, p. 16, so that |det|^{-m} is a homomorphism of
    G, as required in 2.7.1, p. 122, and used in 2.7.16, p. 136.
    Supporting lemma. *)
Lemma linear_group_det_mul (g h : GL) :
  linear_group_det (mul g h) = linear_group_det g * linear_group_det h.
Proof.
rewrite /linear_group_det /hom_det -det_comp; apply: det_ext=> x.
by rewrite /= (linear_group_mulE hG).
Qed.

(** Source for [linear_group_det_unit]: det 1_V = 1, Federer 1.3.4,
    p. 16. Supporting lemma. *)
Lemma linear_group_det_unit : linear_group_det unit = 1.
Proof.
rewrite /linear_group_det /hom_det -(det_id (euclidean_two_nonzero R) hb); apply: det_ext=> x.
by rewrite /= (linear_group_unitE hG).
Qed.

(** Source for [linear_group_det_inv]: det(g^{-1}) = (det g)^{-1},
    Federer 1.3.4, p. 16. Supporting lemma. *)
Lemma linear_group_det_inv (g : GL) : linear_group_det (inv g) = (linear_group_det g)^-1.
Proof.
apply: (mulIf (linear_group_det_nonzero g)).
rewrite -linear_group_det_mul (group_mulVg (linear_group_group_laws hG)) linear_group_det_unit.
by rewrite mulVf // linear_group_det_nonzero.
Qed.

(** Source for [hom_evaluation_point_continuous]: f |-> f(a) is
    continuous on Hom(V, V), Federer 1.7.6, p. 33, the continuity of
    evaluation of HomSpaceTopology.v at a fixed point; supporting the
    continuity of det, 2.7.16, p. 135. Supporting lemma. *)
Lemma hom_evaluation_point_continuous (a : VT) : continuous (fun f : H => ((f : Hom V V) a : VT)).
Proof.
have -> : (fun f : H => ((f : Hom V V) a : VT)) =
    (fun q : H * VT => ((q.1 : Hom V V) q.2 : VT)) \o (fun f : H => (f, a)) by [].
move=> f; apply: continuous_comp.
  apply: (@topological_pair_continuous H H VT id (fun _ => a)); first by move=> f'; exact: cvg_id.
  exact: cst_continuous.
exact: (@hom_evaluation_continuous R V V _ _ hB hB n _ hb).
Qed.

(** Source for [hom_det_continuous]: det is continuous on Hom(V, V):
    for an orthonormal base e of V, det f = sum over the permutations s
    of index(s) prod_i f(e_i) . e_{s(i)} by the permutation formula of
    Federer 1.3.4, p. 16, and each f(e_i) . e_j depends continuously on
    f; supporting "a continuous homomorphism chi" in 2.7.9, p. 126, for
    chi = |det|^{-n}, 2.7.16, p. 136. Supporting lemma. *)
Lemma hom_det_continuous : continuous (fun f : H => (hom_det f : R^o)).
Proof.
have [e [he hoe]] := orthonormal_basis_exists hB hb.
have ho := orthonormalisation_orthonormal hoe.
have hf : (fun f : H => (hom_det f : R^o)) =
    (fun f : H => \sum_(s : 'S_n) FedererPermutation.index R s *
      \prod_(i < n) (B ((f : Hom V V) (e i)) (e (s i)) : R^o)).
  apply: funext=> f; rewrite /hom_det (det_basis_independent _ hb he).
  rewrite (det_formula (euclidean_two_nonzero R) he (f := hom_as_linear (f : Hom V V))
    (b := fun i j => B ((f : Hom V V) (e i)) (e j))) // => i.
  have h := @inner_finite_synthesis_coordinates R V B hB n e he ho ((f : Hom V V) (e i)).
  rewrite /inner_finite_synthesis in h; rewrite hom_as_linearE -[in LHS]h.
  by apply: eq_bigr=> j _; rewrite inner_coordinateE.
rewrite hf; apply: continuous_big; first exact: add_continuous.
move=> s _ f; apply: (@continuous_comp _ _ _
  (fun f : H => \prod_(i < n) (B ((f : Hom V V) (e i)) (e (s i)) : R^o))
  ( *%R (FedererPermutation.index R s))); last exact: mulrl_continuous.
apply: continuous_big; first exact: mul_continuous.
move=> i _ g; apply: (@continuous_comp _ _ _ (fun f : H => ((f : Hom V V) (e i) : VT))
  (fun x : VT => (B x (e (s i)) : R^o))); first exact: hom_evaluation_point_continuous.
have -> : (fun x : VT => (B x (e (s i)) : R^o)) = (fun x : VT => inner_coordinate hB (e (s i)) x).
  by apply: funext=> x; rewrite inner_coordinateE.
exact: inner_coordinate_continuous.
Qed.

(** Source for [linear_group_det_continuous]: det is continuous on G,
    Federer 2.7.16, pp. 135–136; with values in the real line metric
    of the modular function, 2.7.8, p. 126. Supporting lemma. *)
Lemma linear_group_det_continuous : continuous (linear_group_det : GL -> real_line_metric R).
Proof.
move=> g; apply: (@continuous_comp _ _ _ (set_val : GL -> H) (fun f : H => (hom_det f : R^o))).
  exact: set_type_val_continuous.
exact: hom_det_continuous.
Qed.

(** Source for [linear_group_det_power_continuous]: |det|^{-k} is a
    continuous function on G, Federer 2.7.16, pp. 136–137, as required
    of chi in 2.7.9, p. 126. Supporting lemma. *)
Lemma linear_group_det_power_continuous (k : nat) :
  continuous ((fun g => `|linear_group_det g| ^- k) : GL -> real_line_metric R).
Proof.
have ha : continuous ((fun g => `|linear_group_det g|) : GL -> R^o).
  move=> g; apply: (@continuous_comp _ _ _ (linear_group_det : GL -> R^o) (fun x : R^o => `|x|)).
    exact: linear_group_det_continuous.
  exact: norm_continuous.
have hp : forall j, continuous ((fun g => `|linear_group_det g| ^+ j) : GL -> R^o).
  elim=> [|j ih] g.
    have -> : (fun g => `|linear_group_det g| ^+ 0) = (fun _ : GL => (1 : R^o)).
      by apply: funext=> h; rewrite expr0.
    exact: cst_continuous.
  have -> : (fun g => `|linear_group_det g| ^+ j.+1) =
      (fun g => (`|linear_group_det g| : R^o) * `|linear_group_det g| ^+ j).
    by apply: funext=> h; rewrite exprS.
  exact: (@continuousM R GL _ _ g (ha g) (ih g)).
move=> g.
have h0 : `|linear_group_det g| ^+ k != 0 by rewrite expf_neq0 // normr_eq0 linear_group_det_nonzero.
exact: (@continuousV R GL (fun g => `|linear_group_det g| ^+ k : R^o) g h0 (hp k g)).
Qed.

End LinearGroupDeterminant.

Arguments hom_det {R V n b} hb f.
Arguments linear_group_det {R V B} hB {n b} hb g.

Section HomCovariance.
Variable R : realType.
Variables U V : lmodType R.
Variable C : U -> U -> R.
Hypothesis hC : is_inner_product C.
Variable m : nat.
Variable c : 'I_m -> U.
Hypothesis hc : is_basis c.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Local Notation X := (inner_metric_space (hom_inner_productP hC hB hc)).
Local Notation GL := (set_type (linear_group hB hb)).
Local Notation mul := (linear_group_mul hB hb).
Local Notation unit := (linear_group_unit hB hb).
Local Notation hG := (linear_group_operations hB hb).
Local Notation KX := (@compactly_supported_continuous_functions R X).

(** Source for [hom_base_values]: "a G action preserving isomorphism
    X ~ V^m by mapping f in X onto (f(e_1), ..., f(e_m)) in V^m",
    Federer 2.7.16, p. 136. Definition, with V^m the space of functions
    of 'I_m into V. *)
Definition hom_base_values (f : Hom U V) : {ffun 'I_m -> V} := [ffun k => f (c k)].

(** Source for [hom_base_values_linear]: f |-> (f(e_1), ..., f(e_m)) is
    linear, Federer 2.7.16, p. 136. Supporting lemma. *)
Lemma hom_base_values_linear : linear hom_base_values.
Proof. by move=> a f g; apply/ffunP=> k; rewrite !ffunE hom_addE hom_scaleE. Qed.

(** Source for [hom_base_values_bijective]: f |-> (f(e_1), ..., f(e_m))
    is an isomorphism of X onto V^m, Federer 2.7.16, p. 136; its inverse
    is (v_1, ..., v_m) |-> sum_k (x |-> e_k*(x) v_k), by 1.4.5, p. 21.
    Direct formalisation of "isomorphism". *)
Lemma hom_base_values_bijective : bijective hom_base_values.
Proof.
exists (fun v : {ffun 'I_m -> V} => \sum_k hom_with_coefficient (v k) (dual_basis hc k)).
  move=> f; rewrite [RHS](finite_Hom_coefficients hc f).
  by apply: eq_bigr=> k _; rewrite /hom_base_values ffunE.
move=> v; apply/ffunP=> k; rewrite /hom_base_values ffunE hom_sum_coefficientsE.
under eq_bigr do rewrite hom_with_coefficientE dual_basisE.
rewrite (bigD1 k) //= eqxx scale1r big1 ?addr0 // => l hl.
by rewrite eq_sym (negbTE hl) scale0r.
Qed.

(** Source for [hom_base_values_equivariant]: the isomorphism
    X ~ V^m is "G action preserving", Federer 2.7.16, p. 136: g o f is
    mapped onto (g(f(e_1)), ..., g(f(e_m))). Direct formalisation. *)
Lemma hom_base_values_equivariant (g : Hom V V) (f : Hom U V) :
  hom_base_values (hom_comp g f) = [ffun k => g (hom_base_values f k)].
Proof. by apply/ffunP=> k; rewrite !ffunE hom_compE. Qed.

(** Source for [hom_linear_group_action]: "The linear group G of V acts
    (by functional composition) on the vectorspace X = Hom(U, V)",
    Federer 2.7.16, p. 136: A(g, f) = g o f, curried as in 2.7.1,
    p. 121. Definition. *)
Definition hom_linear_group_action (g : GL) (f : X) : X := hom_comp (set_val g : Hom V V) f.

(** Source for [hom_linear_group_action_compatible]: A(g h, f) =
    A(g, A(h, f)), Federer 2.7.1, p. 121, for the action of 2.7.16,
    p. 136. Supporting lemma. *)
Lemma hom_linear_group_action_compatible (g h : GL) (f : X) :
  hom_linear_group_action (mul g h) f = hom_linear_group_action g (hom_linear_group_action h f).
Proof.
rewrite /hom_linear_group_action (linear_group_mulE hG).
by apply: hom_ext=> x; rewrite !hom_compE.
Qed.

(** Source for [hom_linear_group_action_unit]: A(1_V, f) = f, Federer
    2.7.1, p. 121, for the action of 2.7.16, p. 136. Supporting lemma. *)
Lemma hom_linear_group_action_unit (f : X) : hom_linear_group_action unit f = f.
Proof.
rewrite /hom_linear_group_action (linear_group_unitE hG).
by apply: hom_ext=> x; rewrite hom_compE.
Qed.

(** Source for [hom_haar_integral_covariant]: "If phi is a Haar measure
    of the additive group of X, then phi is |det|^{-m} covariant with
    respect to the action of G", Federer 2.7.16, p. 136, for the
    integral: every left Haar integral mu of the additive group of X
    satisfies mu(u o A_g) = |det g|^{-m} mu(u) whenever u in K(X),
    g in G, the identity of 2.7.1, p. 122. Direct formalisation; the
    hypothesis m <= n is not needed. *)
Theorem hom_haar_integral_covariant (mu : (X -> R) -> R) :
  is_left_haar_integral (fun f g : X => f + g) mu ->
  is_covariant_integral hom_linear_group_action (fun g => `|linear_group_det hB hb g| ^- m) mu.
Proof.
move=> hmu; split; first exact: (covariant_integral_daniell (nonzero_invariant_integral_invariant hmu)).
move=> u g hu.
have hdet := hom_left_composition_det (euclidean_two_nonzero R) hc hb (set_val g).
have hT : det (euclidean_two_nonzero R) (hom_rank_one_baseP hc hb)
    (hom_left_composition U (set_val g)) != 0.
  by rewrite hdet expf_neq0 // linear_group_det_nonzero.
have := @finite_haar_integral_linear R (Hom U V) _ (hom_inner_productP hC hB hc) _ _
  (hom_rank_one_baseP hc hb) mu _ hmu hT u hu.
by rewrite hdet normrX.
Qed.

(** Source for [hom_haar_measure_covariant]: "If phi is a Haar measure
    of the additive group of X, then phi is |det|^{-m} covariant with
    respect to the action of G", Federer 2.7.16, p. 136, in the sense of
    2.7.1, p. 122: phi is the K(X) regular measure associated with a
    monotone Daniell integral satisfying the covariance identity.
    Direct formalisation. *)
Theorem hom_haar_measure_covariant (phi : set X -> \bar R) :
  is_left_haar_measure (fun f g : X => f + g) phi ->
  is_covariant_measure hom_linear_group_action (fun g => `|linear_group_det hB hb g| ^- m) phi.
Proof.
move=> [mu [hmu hm hi hr]]; exists mu; split=> //.
- exact: nonzero_invariant_integral_monotone hmu.
- exact: covariant_integral_law (hom_haar_integral_covariant hmu).
Qed.

End HomCovariance.

Section RightComposition.
Variable R : realType.
Variables V W : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Variable D : W -> W -> R.
Hypothesis hD : is_inner_product D.
Variable p : nat.
Variable w : 'I_p -> W.
Hypothesis hw : is_basis w.
Local Notation Y := (inner_metric_space (hom_inner_productP hB hD hb)).
Local Notation KY := (@compactly_supported_continuous_functions R Y).

(** Source for [hom_haar_integral_right]: for a univalent h in
    Hom(V, V) and a left Haar integral mu of the additive group of
    Hom(V, W), mu(u o R_h) = |det h|^{-p} mu(u) whenever u in K(Hom(V, W)),
    where R_h(f) = f o h and p = dim W; for W = V and h = g^{-1} this is
    "phi is right |det|^n covariant", Federer 2.7.16, p. 137, obtained
    there through wedge^1 and the commutative diagram. Supporting
    theorem. *)
Theorem hom_haar_integral_right (mu : (Y -> R) -> R) (h : Hom V V) :
  is_left_haar_integral (fun f g : Y => f + g) mu -> injective h ->
  forall u, KY u -> mu (u \o (fun f : Y => (hom_comp (f : Hom V W) h : Y))) = `|hom_det hb h| ^- p * mu u.
Proof.
move=> hmu hi u hu.
have hdet := hom_right_composition_det (euclidean_two_nonzero R) hb hw h.
have hT : det (euclidean_two_nonzero R) (hom_dual_rank_one_baseP hb hw)
    (hom_right_composition W h) != 0.
  by rewrite hdet expf_neq0 //; apply/(det_nonzero_injective _ _ _).2.
have := @finite_haar_integral_linear R (Hom V W) _ (hom_inner_productP hB hD hb) _ _
  (hom_dual_rank_one_baseP hb hw) mu _ hmu hT u hu.
by rewrite hdet normrX.
Qed.

End RightComposition.

Arguments hom_base_values {R U V m} c f.
Arguments hom_linear_group_action {R U V C} hC {m c} hc {B} hB {n b} hb g f.
Arguments hom_haar_integral_covariant {R U V C} hC {m c} hc {B} hB {n b} hb {mu} _.
Arguments hom_haar_measure_covariant {R U V C} hC {m c} hc {B} hB {n b} hb {phi} _.
Arguments hom_haar_integral_right {R V W B} hB {n b} hb {D} hD {p w} hw {mu h} _ _ {u} _.
