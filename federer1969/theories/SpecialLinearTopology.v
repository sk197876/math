(** Federer (1969), 2.7.16, printed p. 135: "In case n >= 2 the special
    linear group SL(n, R) = GL(n, R) cap {f : det(f) = 1} acts transitively
    on R^n ~ {0}, and L^n is invariant with respect to the action of SL(n,
    R)." Here SL(n, R) is the set of members of the linear group GL(n, R) of
    LinearGroupTopology.v with determinant 1. It is a closed subgroup,
    because det is continuous on Hom(R^n, R^n) (its permutation expansion of
    1.3.4, p. 16, is a polynomial in the coordinates of f(e_1), ...,
    f(e_n)). With the relative topology and any restricted group structure
    (is_subgroup_restriction of IsotropyGroupTopology.v) it is a locally
    compact Hausdorff topological group, L^n is invariant for its action on
    R^n, and for n >= 2 the space R^n ~ {0} is a homogeneous space of SL(n,
    R) in the sense of 2.7.1, p. 121. The orbit maps s |-> s(x) are open
    because of the continuous map rho(h) = h o k o d((det h)^{-1}) o k^{-1}
    of GL(n, R) into SL(n, R), where k in SL(n, R) maps e_1 to x and d(c)
    multiplies the second coordinate by c: rho(h)(x) = h(x), and rho fixes
    SL(n, R), so the orbit of an open set of SL(n, R) is the GL(n, R) orbit
    of an open set of GL(n, R). *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module.
From mathcomp Require Import fingroup perm.
From Federer Require Import FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm InnerNormInequalities InnerMetric InnerNormedTopology LinearBasis TensorUP
  Hom HomInner EuclideanCoordinateTopology EuclideanCoordinateMetric InversionCount ExteriorDeterminant
  ExteriorLeibniz CoordinateProjection
  MeasureUP CompactSupportFunctionUP FunctionLatticeRegularityUP RealIntegralFunctionalUP
  MonotoneDaniellIntegralUP CovariantIntegralUP SubtypeCompactHausdorff IsotropyGroupTopology
  TopologicalProductMaps TopologicalGroupUP TopologicalGroupLaws HomogeneousSpaceUP HomeomorphismUP
  EuclideanLebesgueDimensions EuclideanLebesgueHaar EuclideanLinearMaps EuclideanLinearGroupCovariance
  SpecialLinearTransitive HomSpaceTopology LinearGroupTopology LinearGroupSealed GeneralLinearPunctured.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section SpecialLinear.
Variable R : realType.
Variable n : nat.
Local Notation V := (R_n R n).
Local Notation E := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation hB := (@euclidean_inner_productP R n).
Local Notation hb := (@coordinate_basisP R n).
Local Notation eps := (@coordinate_basis R n).
Local Notation H := (inner_metric_space (hom_inner_productP hB hB hb)).
Local Notation GL := (set_type (linear_group hB hb)).
Local Notation mul := (linear_group_mul hB hb).
Local Notation inv := (linear_group_inv hB hb).
Local Notation unit := (linear_group_unit hB hb).
Local Notation hG := (linear_group_operations hB hb).
Local Notation Leb := (@euclidean_lebesgue_measure R n).
Local Notation onorm := (hom_operator_norm hB hB hb).
Local Notation N := (inner_norm hB).

(** Source for [hom_evaluation_at_continuous]: f |-> f(a) is continuous
    on Hom(R^n, R^n), Federer 2.7.16, p. 134, a special case of the
    continuity of evaluation. Supporting lemma. *)
Lemma hom_evaluation_at_continuous (a : E) : continuous (fun f : H => ((f : Hom V V) a : E)).
Proof.
have -> : (fun f : H => ((f : Hom V V) a : E)) =
    (fun q : H * E => ((q.1 : Hom V V) q.2 : E)) \o (fun f : H => (f, a)) by [].
move=> f; apply: continuous_comp.
  apply: (@topological_pair_continuous H H E id (fun _ => a)); first by move=> f'; exact: cvg_id.
  exact: cst_continuous.
exact: (@hom_evaluation_continuous R V V _ _ hB hB n _ hb).
Qed.

(** Source for [euclidean_det_continuous]: det is continuous on
    Hom(R^n, R^n): by Federer 1.3.4, p. 16, det f = sum over the
    permutations s of sign(s) prod_i f(e_i)_{s(i)}, and the coordinates
    of f(e_i) depend continuously on f; this makes SL(n, R) closed,
    2.7.16, p. 135. Supporting lemma. *)
Lemma euclidean_det_continuous : continuous (fun f : H => euclidean_det (hom_as_linear (f : Hom V V))).
Proof.
have he : (fun f : H => euclidean_det (hom_as_linear (f : Hom V V))) =
    (fun f : H => \sum_(s : 'S_n) FedererPermutation.index R s *
      \prod_(i < n) (((f : Hom V V) (eps i) : V) (s i) : R)).
  apply: funext=> f; rewrite /euclidean_det.
  rewrite (det_formula (euclidean_two_nonzero R) (@coordinate_basisP R n)
    (f := hom_as_linear (f : Hom V V)) (b := fun i j => ((f : Hom V V) (eps i) : V) j)) //.
  move=> i; exact: esym (euclidean_coordinate_expansion ((f : Hom V V) (eps i))).
rewrite he; apply: continuous_big; first exact: add_continuous.
move=> s _ f; apply: (@continuous_comp _ _ _
  (fun f : H => \prod_(i < n) (((f : Hom V V) (eps i) : V) (s i) : R))
  ( *%R (FedererPermutation.index R s))); last exact: mulrl_continuous.
apply: continuous_big; first exact: mul_continuous.
move=> i _ g; apply: (@continuous_comp _ _ _ (fun f : H => ((f : Hom V V) (eps i) : E))
  (fun x : E => (x (s i) : R^o))); first exact: hom_evaluation_at_continuous.
exact: euclidean_coordinate_continuous.
Qed.

(** Source for [general_linear_det_continuous]: det is continuous on
    GL(n, R), Federer 2.7.16, p. 135. Supporting lemma. *)
Lemma general_linear_det_continuous : continuous (@general_linear_det R n).
Proof.
move=> g; apply: (@continuous_comp _ _ _ (set_val : GL -> H)
  (fun f : H => euclidean_det (hom_as_linear (f : Hom V V)))); first exact: set_type_val_continuous.
exact: euclidean_det_continuous.
Qed.

(** Source for [special_linear]: "SL(n, R) = GL(n, R) cap
    {f : det(f) = 1}", Federer 2.7.16, p. 135, as a subset of the
    topological group GL(n, R). Definition. *)
Definition special_linear : set GL := [set g | general_linear_det g = 1].

(** Source for [special_linear_closed]: SL(n, R) is closed in GL(n, R),
    Federer 2.7.16, p. 135, by continuity of det. Supporting lemma. *)
Lemma special_linear_closed : closed special_linear.
Proof.
have -> : special_linear = (@general_linear_det R n) @^-1` [set c | c = 1] by [].
apply: preimage_closed; last exact: closed_eq.
by move=> g _; exact: general_linear_det_continuous.
Qed.

(** Source for [general_linear_det_unit]: det 1_V = 1, Federer 1.3.4,
    p. 16. Supporting lemma. *)
Lemma general_linear_det_unit : general_linear_det unit = 1.
Proof.
rewrite /general_linear_det -(@euclidean_det_id R n); apply: det_ext=> x.
by rewrite /= (linear_group_unitE hG).
Qed.

(** Source for [general_linear_det_inv]: det(f^{-1}) det f = 1, Federer
    1.3.4, p. 16. Supporting lemma. *)
Lemma general_linear_det_inv (g : GL) : general_linear_det (inv g) * general_linear_det g = 1.
Proof.
by rewrite -general_linear_det_mul (group_mulVg (linear_group_group_laws hG)) general_linear_det_unit.
Qed.

(** Source for [special_linear_subgroup]: SL(n, R) is a subgroup of
    GL(n, R), Federer 2.7.16, p. 135, since det is multiplicative.
    Supporting lemma. *)
Lemma special_linear_subgroup : is_subgroup mul inv unit special_linear.
Proof.
split.
- exact: general_linear_det_unit.
- by move=> g h hg hh; rewrite /special_linear /= general_linear_det_mul hg hh mulr1.
- move=> g hg; have := general_linear_det_inv g.
  by rewrite /special_linear /= in hg *; rewrite hg mulr1.
Qed.

(** Source for [special_linear_restriction_exists]: SL(n, R) is a group
    with the operations of GL(n, R), Federer 2.7.16, p. 135. Existence
    of the restricted operations (subgroup_restriction_exists). *)
Theorem special_linear_restriction_exists :
  exists mulS invS eS, is_subgroup_restriction mul inv unit special_linear mulS invS eS.
Proof. exact: subgroup_restriction_exists special_linear_subgroup. Qed.

Section Restriction.
Variables (mulS : special_linear -> special_linear -> special_linear)
  (invS : special_linear -> special_linear) (eS : special_linear).
Hypothesis hS : is_subgroup_restriction mul inv unit special_linear mulS invS eS.

(** Source for [special_linear_lch]: SL(n, R), a closed subgroup of
    GL(n, R), is a locally compact Hausdorff topological group,
    Federer 2.7.16, p. 135, with 2.7.1, p. 121. Direct formalisation. *)
Theorem special_linear_lch : is_locally_compact_hausdorff_group mulS invS eS.
Proof.
apply: (subgroup_restriction_locally_compact_hausdorff hS); last exact: special_linear_closed.
exact: linear_group_operations_lch.
Qed.

End Restriction.

(** Source for [special_linear_euclidean_action]: the action of
    SL(n, R) on R^n by evaluation, Federer 2.7.16, p. 135. Definition. *)
Definition special_linear_euclidean_action (s : special_linear) (x : E) : E :=
  euclidean_linear_group_action (set_val s) x.

(** Source for [euclidean_lebesgue_special_linear_group_invariant]:
    "L^n is invariant with respect to the action of SL(n, R)", Federer
    2.7.16, p. 135, in the sense of 2.7.1, p. 122, for SL(n, R) as a
    subset of the topological group GL(n, R). Direct formalisation. *)
Theorem euclidean_lebesgue_special_linear_group_invariant :
  is_invariant_measure special_linear_euclidean_action Leb.
Proof.
have [mu [hm hc hmeas hrep hreg]] := @euclidean_lebesgue_linear_group_covariant R n.
exists mu; split=> // u s hu.
rewrite (hc u (set_val s) hu).
by have := set_valP s; rewrite /special_linear /= => ->; rewrite normr1 invr1.
Qed.

Local Notation X := (set_type (~` [set (0 : E)])).

(** Source for [special_linear_punctured_action]: the action of
    SL(n, R) on R^n ~ {0}, Federer 2.7.16, p. 135. Definition. *)
Definition special_linear_punctured_action (s : special_linear) (x : X) : X :=
  punctured_linear_action (set_val s) x.

(** Source for [hom_diagonal]: the map x |-> (c_1 x_1, ..., c_n x_n)
    of Federer 2.7.16, p. 135, as a member of Hom(R^n, R^n). The map
    d(c) multiplying the second coordinate by c is
    hom_diagonal (second_scaling c). Definition. *)
Definition hom_diagonal (c : 'I_n -> R) : Hom V V := hom_of_linear (euclidean_diagonal_map c).

(** Source for [hom_diagonal_operator_norm]: for the diagonal maps
    d and d' with entries c_1, ..., c_n and c'_1, ..., c'_n,
    ||d - d'|| <= sum_i |c_i - c'_i|, Federer 1.7.6, p. 33; supporting
    2.7.16, p. 135. *)
Lemma hom_diagonal_operator_norm (c c' : 'I_n -> R) :
  onorm (hom_diagonal c - hom_diagonal c') <= \sum_i `|c i - c' i|.
Proof.
apply: hom_operator_norm_least; first by rewrite sumr_ge0.
move=> x.
have he : ((hom_diagonal c - hom_diagonal c' : Hom V V) x : V) =
    \sum_i ((c i - c' i) * x i) *: eps i.
  rewrite -[LHS](@euclidean_coordinate_expansion R n); apply: eq_bigr=> i _.
  by rewrite /= /euclidean_diagonal !ffunE mulrBl.
rewrite he; apply: le_trans (_ : _ <= \sum_i N (((c i - c' i) * x i) *: eps i)) _.
  apply: (big_ind2 (fun (a : V) (r : R) => N a <= r)).
  - by rewrite inner_norm0.
  - move=> a1 r1 a2 r2 h1 h2; apply: le_trans (inner_norm_triangle hB _ _) _; exact: lerD.
  - by [].
rewrite mulr_suml; apply: ler_sum=> i _.
rewrite inner_normZ normrM -mulrA ler_wpM2l //.
have h1 : N (eps i) = 1.
  apply: inner_norm_value; first exact: ler01.
  by rewrite expr1n euclidean_inner_basis /coordinate_basis ffunE eqxx.
by rewrite h1 mulr1; exact: euclidean_coordinate_norm_bound.
Qed.

End SpecialLinear.

Arguments special_linear {R n}.
Arguments special_linear_euclidean_action {R n}.
Arguments special_linear_punctured_action {R n}.
Arguments hom_diagonal {R n}.

Section SpecialLinearHomogeneous.
Variable R : realType.
Variable k : nat.
Local Notation n := k.+2.
Local Notation V := (R_n R n).
Local Notation E := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation hB := (@euclidean_inner_productP R n).
Local Notation hb := (@coordinate_basisP R n).
Local Notation eps := (@coordinate_basis R n).
Local Notation H := (inner_metric_space (hom_inner_productP hB hB hb)).
Local Notation GL := (set_type (linear_group hB hb)).
Local Notation mul := (linear_group_mul hB hb).
Local Notation inv := (linear_group_inv hB hb).
Local Notation unit := (linear_group_unit hB hb).
Local Notation hG := (linear_group_operations hB hb).
Local Notation SL := (@special_linear R n).
Local Notation X := (set_type (~` [set (0 : E)])).

(** Source for [second_scaling_continuous]: c |-> d(c) is continuous
    from R into Hom(R^n, R^n), where d(c) multiplies the second
    coordinate by c, since ||d(c) - d(c')|| <= |c - c'|, Federer 1.7.6,
    p. 33; supporting 2.7.16, p. 135. *)
Lemma second_scaling_continuous :
  continuous (fun c : R => (hom_diagonal (second_scaling (k := k) c) : H)).
Proof.
move=> c A /(hom_space_nbhs_operator _ _) [r hr hA].
apply: (@filterS _ _ (nbhs_filter _) _ _ _ (nbhsx_ballx c r hr))=> c' hc'; apply: hA.
apply: le_lt_trans (hom_diagonal_operator_norm _ _) _.
rewrite (bigD1 (second_index k)) //= /second_scaling eqxx big1 ?addr0.
  by move: hc'; rewrite -ball_normE /= distrC.
by move=> i hi; rewrite (negbTE hi) subrr normr0.
Qed.

Section Orbit.
Variable x : X.

(** Source for [special_linear_section]: Federer 2.7.16, p. 135: a
    member k of SL(n, R) with k(e_1) = x, n >= 2
    (special_linear_basis_image). Supporting lemma. *)
Lemma special_linear_section :
  exists2 g : GL, general_linear_det g = 1 & (set_val g : Hom V V) (eps ord0) = set_val x.
Proof.
have hx : set_val x != 0 by apply/eqP; have := set_valP x.
have [f [hdf hfe]] := special_linear_basis_image hx.
have hfi : linear_group hB hb (hom_of_linear f : H).
  by apply: (euclidean_det_injective f).1; rewrite hdf oner_eq0.
exists (exist _ (hom_of_linear f : H) (mem_set hfi))=> //.
by rewrite /general_linear_det -hdf; apply: det_ext.
Qed.

End Orbit.

Section Restriction.
Variables (mulS : SL -> SL -> SL) (invS : SL -> SL) (eS : SL).
Hypothesis hS : is_subgroup_restriction mul inv unit SL mulS invS eS.

(** Source for [special_linear_punctured_continuous]: the action of
    SL(n, R) on R^n ~ {0} is continuous, Federer 2.7.16, p. 135, with
    2.7.1, p. 121. Supporting lemma. *)
Lemma special_linear_punctured_continuous :
  continuous (fun p : SL * X => special_linear_punctured_action p.1 p.2).
Proof.
have -> : (fun p : SL * X => special_linear_punctured_action p.1 p.2) =
    (fun q : GL * X => punctured_linear_action q.1 q.2) \o (fun p : SL * X => (set_val p.1, p.2)) by [].
move=> p; apply: continuous_comp; last exact: punctured_linear_action_continuous.
apply: (@topological_pair_continuous (SL * X)%type GL X).
- move=> q; exact: continuous_comp (@first_projection_continuous SL X q)
    (@set_type_val_continuous GL _ q.1).
- exact: second_projection_continuous.
Qed.

(** Source for [special_linear_punctured_compatible]: A(s t, x) =
    A(s, A(t, x)) for the action of SL(n, R) on R^n ~ {0}, Federer
    2.7.1, p. 121, and 2.7.16, p. 135. Supporting lemma. *)
Lemma special_linear_punctured_compatible (s t : SL) (y : X) :
  special_linear_punctured_action (mulS s t) y =
    special_linear_punctured_action s (special_linear_punctured_action t y).
Proof.
rewrite /special_linear_punctured_action -punctured_linear_action_compatible.
by rewrite (subgroup_restriction_mul hS).
Qed.

(** Source for [special_linear_punctured_onto]: "SL(n, R) acts
    transitively on R^n ~ {0}", n >= 2, Federer 2.7.16, p. 135
    (special_linear_transitive). Supporting lemma. *)
Lemma special_linear_punctured_onto (y : X) :
  orbit_map special_linear_punctured_action y @` setT = setT.
Proof.
apply/seteqP; split=> // z _.
have hy : set_val y != 0 by apply/eqP; have := set_valP y.
have hz : set_val z != 0 by apply/eqP; have := set_valP z.
have [f [hdf hfy]] := special_linear_transitive hy hz.
have hfi : linear_group hB hb (hom_of_linear f : H).
  by apply: (euclidean_det_injective f).1; rewrite hdf oner_eq0.
pose g : GL := exist _ (hom_of_linear f : H) (mem_set hfi).
have hgS : SL g by rewrite /special_linear /= /general_linear_det -hdf; apply: det_ext.
exists (exist _ g (mem_set hgS))=> //.
by apply: val_inj.
Qed.

(** Source for [special_linear_punctured_orbit_open]: the orbit maps
    s |-> s(x) of SL(n, R) on R^n ~ {0} are open, Federer 2.7.1, p. 121,
    as required by "acts transitively" in 2.7.16, p. 135, for a
    homogeneous space. With k in SL(n, R), k(e_1) = x, the continuous map
    rho(h) = h o k o d((det h)^{-1}) o k^{-1} sends GL(n, R) into
    SL(n, R), fixes SL(n, R) and satisfies rho(h)(x) = h(x); hence the
    SL(n, R) orbit of an open set U is the GL(n, R) orbit of the open set
    rho^{-1}(U). Supporting theorem. *)
Theorem special_linear_punctured_orbit_open (y : X) :
  is_open_map (orbit_map special_linear_punctured_action y).
Proof.
have [kk hkd hky] := special_linear_section y.
pose kk' := inv kk.
have [hkk' hk'k] := linear_group_inv_cancel hG kk.
pose rho (h : GL) : H := hom_comp (hom_comp (hom_comp (set_val h : Hom V V) (set_val kk))
  (hom_diagonal (second_scaling (k := k) (general_linear_det h)^-1))) (set_val kk').
have hrho_det h : euclidean_det (hom_as_linear (rho h : Hom V V)) = 1.
  have he : euclidean_det (hom_as_linear (rho h : Hom V V)) =
      general_linear_det h * general_linear_det kk *
      euclidean_det (euclidean_diagonal_map (second_scaling (k := k) (general_linear_det h)^-1)) *
      general_linear_det kk'.
    rewrite /general_linear_det -!euclidean_det_comp; apply: det_ext=> z.
    by rewrite /= /linear_comp.
  rewrite he second_scaling_det hkd mulr1 mulfV ?general_linear_det_nonzero // mul1r.
  by have := general_linear_det_inv kk; rewrite hkd mulr1=> h1; exact: h1.
have hrho_gl h : linear_group hB hb (rho h).
  by apply: (euclidean_det_injective _).1; rewrite hrho_det oner_eq0.
pose rhoG (h : GL) : GL := exist _ (rho h) (mem_set (hrho_gl h)).
have hrho_sl h : SL (rhoG h).
  rewrite /special_linear /= /general_linear_det -(hrho_det h).
  by apply: det_ext.
have hrho_x h : (rho h : Hom V V) (set_val y) = (set_val h : Hom V V) (set_val y).
  rewrite /rho !hom_compE -hky.
  rewrite (proj1 (linear_group_inv_cancel hG kk)) /hom_diagonal /=.
  by rewrite second_scaling_first.
have hrho_fix (s : SL) : rho (set_val s) = set_val (set_val s).
  have hs : general_linear_det (set_val s) = 1 by have := set_valP s.
  apply: hom_ext=> z; rewrite /rho !hom_compE hs invr1 /hom_diagonal /=.
  have -> : euclidean_diagonal (second_scaling (k := k) 1) ((set_val kk' : Hom V V) z) =
      (set_val kk' : Hom V V) z.
    apply/ffunP=> i; rewrite /euclidean_diagonal ffunE /second_scaling.
    by case: (i == second_index k); rewrite mul1r.
  by rewrite hk'k.
have hc2 (F G : GL -> H) : continuous F -> continuous G ->
    continuous (fun h => (hom_comp (F h : Hom V V) (G h : Hom V V) : H)).
  move=> hF hGc h.
  apply: (@continuous_comp GL (H * H)%type H (fun h => (F h, G h))
    (fun q : H * H => (hom_comp (q.1 : Hom V V) (q.2 : Hom V V) : H))).
    exact: (@topological_pair_continuous GL H H F G hF hGc).
  exact: hom_composition_continuous.
have hdc : continuous (fun h : GL => (hom_diagonal (second_scaling (k := k) (general_linear_det h)^-1) : H)).
  move=> h; apply: (@continuous_comp GL R H (fun h : GL => (general_linear_det h)^-1)
    (fun c : R => (hom_diagonal (second_scaling (k := k) c) : H))).
    apply: continuousV; first exact: general_linear_det_nonzero.
    exact: general_linear_det_continuous.
  exact: second_scaling_continuous.
have hrho_cont : continuous rho.
  apply: (hc2 _ _); last exact: cst_continuous.
  apply: (hc2 _ _); last exact: hdc.
  apply: (hc2 _ _); last exact: cst_continuous.
  exact: set_type_val_continuous.
have hrhoG_cont : continuous rhoG by apply: set_type_continuous_into.
move=> U [U' hU' hU'U].
pose P : set GL := rhoG @^-1` U'.
have hP : open P by apply: open_comp hU'=> h _; exact: hrhoG_cont.
have -> : orbit_map special_linear_punctured_action y @` U =
    orbit_map (@punctured_linear_action R n) y @` P.
  apply/seteqP; split=> z [a ha <-].
  - exists (set_val a).
      rewrite /P /=; have -> : rhoG (set_val a) = set_val a by apply: val_inj; exact: hrho_fix.
      by rewrite -hU'U in ha.
    by [].
  - exists (exist _ (rhoG a) (mem_set (hrho_sl a))); first by rewrite -hU'U.
    by apply: val_inj; exact: (hrho_x a).
exact: punctured_linear_orbit_open hP.
Qed.

(** Source for [special_linear_punctured_homogeneous]: "In case n >= 2
    the special linear group SL(n, R) ... acts transitively on
    R^n ~ {0}", Federer 2.7.16, p. 135: R^n ~ {0} is a homogeneous space
    of SL(n, R) in the sense of 2.7.1, p. 121. Direct formalisation. *)
Theorem special_linear_punctured_homogeneous :
  is_homogeneous_space mulS special_linear_punctured_action.
Proof.
split.
- exact: special_linear_punctured_continuous.
- exact: special_linear_punctured_compatible.
- exact: special_linear_punctured_orbit_open.
- exact: special_linear_punctured_onto.
Qed.

End Restriction.

End SpecialLinearHomogeneous.
