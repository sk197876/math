(** Federer (1969), 2.7.16, printed p. 135: "Thus L^n is |det|^{-1}
    covariant with respect to the action of GL(n, R) on R^n. (This action is
    not transitive, but a transitive action results through replacement of
    R^n by R^n ~ {0}, which really does not matter because L^n{0} = 0.)"
    Here GL(n, R) is the linear group of R^n = inner_metric_space
    (euclidean_inner_productP R n) of LinearGroupTopology.v, a locally
    compact Hausdorff topological group with the operations of
    LinearGroupSealed.v, acting on R^n by evaluation. The module restates
    the covariance of L^n of EuclideanLinearGroupCovariance.v for this group
    and proves that R^n ~ {0}, with the relative topology (set_type), is a
    locally compact Hausdorff space and a homogeneous space of GL(n, R) in
    the sense of 2.7.1, p. 121, through A(f, x) = f(x): the action is
    continuous by the continuity of evaluation, compatible with composition,
    transitive (SpecialLinearTransitive.v), and its orbit maps f |-> f(x)
    are open, because f + (x . x)^{-1} (v |-> (v . x) w) maps x to f(x) + w
    and lies within ||w|| / |x| of f. The space R^n ~ {0} is locally compact
    because it is open in R^n, whose closed balls are compact. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm InnerMetric InnerNormedTopology LinearBasis Hom HomInner
  MeasureUP CompactSupportFunctionUP FunctionLatticeRegularityUP RealIntegralFunctionalUP
  MonotoneDaniellIntegralUP CovariantIntegralUP SubtypeCompactHausdorff IsotropyGroupTopology
  TopologicalProductMaps TopologicalGroupUP HomogeneousSpaceUP HomeomorphismUP EuclideanLebesgue
  EuclideanLebesgueDimensions ExteriorDeterminant
  EuclideanAdditiveGroup EuclideanLebesgueHaar EuclideanLinearMaps EuclideanLinearGroupCovariance
  SpecialLinearTransitive HomSpaceTopology LinearGroupTopology LinearGroupSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section OpenSubspace.
Variable R : realType.
Variable T : normedModType R.
Hypothesis hT : forall (a : T) (r : R), compact [set x : T | `|x - a| <= r].
Variable S : set T.
Hypothesis hS : open S.

(** Source for [open_subspace_locally_compact]: an open subset of a
    normed space whose closed balls are compact is locally compact in
    the relative topology; each point a has the compact neighbourhood
    {x : |x - a| <= r/2} for a ball {x : |x - a| < r} inside S. This
    supports "the topological assumptions of our general theory are
    satisfied" for R^n ~ {0} and for the linear group, Federer 2.7.16,
    pp. 134–135. Supporting lemma. *)
Lemma open_subspace_locally_compact : locally_compact [set: set_type S].
Proof.
move=> a _; rewrite withinET.
have /nbhs_ballP [r hr hsub] : nbhs (set_val a) S.
  by apply: open_nbhs_nbhs; split; [exact: hS|exact: set_valP].
pose C : set T := [set x : T | `|x - set_val a| <= r / 2].
have hCsub : C `<=` S.
  move=> x hx; apply: hsub; rewrite -ball_normE /= distrC.
  apply: le_lt_trans hx _; by rewrite ltr_pdivrMr ?ltr0n // ltr_pMr // ltr1n.
have hCcl : closed C.
  have he : C = closed_ball_ Num.norm (set_val a) (r / 2).
    by rewrite /C; apply/seteqP; split=> x /=; rewrite /closed_ball_ distrC.
  rewrite he; exact: closed_closed_ball_.
exists (set_val @^-1` C : set (set_type S)); last split.
- apply: (@set_type_val_continuous T S a).
  apply: (@filterS _ _ _ (ball (set_val a) (r / 2))); last by apply: nbhsx_ballx; rewrite divr_gt0.
  by move=> x; rewrite -ball_normE /= distrC=> h; exact: ltW.
- by apply: set_type_compact_preimage hCsub; rewrite /C; exact: hT.
- by apply: preimage_closed hCcl=> c _; exact: set_type_val_continuous.
Qed.

End OpenSubspace.

Section EuclideanLinearGroup.
Variable R : realType.
Variable n : nat.
Local Notation V := (R_n R n).
Local Notation E := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation hB := (@euclidean_inner_productP R n).
Local Notation hb := (@coordinate_basisP R n).
Local Notation H := (inner_metric_space (hom_inner_productP hB hB hb)).
Local Notation GL := (set_type (linear_group hB hb)).
Local Notation mul := (linear_group_mul hB hb).
Local Notation Leb := (@euclidean_lebesgue_measure R n).
Local Notation K := (@compactly_supported_continuous_functions R E).
Local Notation onorm := (hom_operator_norm hB hB hb).
Local Notation N := (inner_norm hB).

(** Source for [general_linear_det]: det f for f in GL(n, R), Federer
    2.7.16, p. 135, with det of 1.3.4, p. 16 (euclidean_det).
    Definition. *)
Definition general_linear_det (g : GL) : R := euclidean_det (hom_as_linear (set_val g : Hom V V)).

(** Source for [general_linear_det_nonzero]: det f <> 0 for f in
    GL(n, R), Federer 2.7.16, p. 135, by 1.3.4, p. 16. Supporting
    lemma. *)
Lemma general_linear_det_nonzero (g : GL) : general_linear_det g != 0.
Proof. by apply/(euclidean_det_injective _).2; exact: set_valP g. Qed.

(** Source for [general_linear_det_mul]: det(g o h) = det g . det h,
    Federer 1.3.4, p. 16, so that |det|^{-1} is a homomorphism of
    GL(n, R), as used in 2.7.16, p. 135. Supporting lemma. *)
Lemma general_linear_det_mul (g h : GL) :
  general_linear_det (mul g h) = general_linear_det g * general_linear_det h.
Proof.
rewrite /general_linear_det -euclidean_det_comp; apply: det_ext=> x.
by rewrite /= (linear_group_mulE (linear_group_operations hB hb)).
Qed.

(** Source for [euclidean_linear_group_action]: the action
    A(f, x) = f(x) of GL(n, R) on R^n, Federer 2.7.16, p. 135, curried as
    in 2.7.1, p. 121. Definition. *)
Definition euclidean_linear_group_action (g : GL) (x : E) : E := (set_val g : Hom V V) x.

(** Source for [euclidean_lebesgue_linear_group_covariant]: "Thus L^n is
    |det|^{-1} covariant with respect to the action of GL(n, R) on R^n",
    Federer 2.7.16, p. 135, in the sense of 2.7.1, p. 122, for the
    topological group GL(n, R) of LinearGroupTopology.v. Direct
    formalisation. *)
Theorem euclidean_lebesgue_linear_group_covariant :
  is_covariant_measure euclidean_linear_group_action (fun g => `|general_linear_det g|^-1) Leb.
Proof.
exists (@euclidean_lebesgue_integral R n); split.
- exact: euclidean_lebesgue_integral_monotone.
- move=> u g hu.
  exact: (euclidean_lebesgue_linear_integral (general_linear_det_nonzero g) hu).
- exact: euclidean_lebesgue_is_measure.
- exact: euclidean_lebesgue_integral_represents.
- exact: euclidean_lebesgue_function_lattice_regular.
Qed.

Local Notation X := (set_type (~` [set (0 : E)])).

(** Source for [punctured_space_hausdorff]: R^n ~ {0} is Hausdorff,
    Federer 2.7.16, p. 135, as required of X in 2.7.1, p. 121.
    Supporting lemma. *)
Lemma punctured_space_hausdorff : hausdorff_space X.
Proof. by apply: set_type_hausdorff; exact: euclidean_hausdorff. Qed.

(** Source for [punctured_space_open]: R^n ~ {0} is open in R^n,
    Federer 2.7.16, p. 135. Supporting lemma. *)
Lemma punctured_space_open : open (~` [set (0 : E)]).
Proof.
by apply: closed_openC; apply: accessible_closed_set1; apply: hausdorff_accessible;
  exact: euclidean_hausdorff.
Qed.

(** Source for [punctured_space_locally_compact]: R^n ~ {0} is locally
    compact, Federer 2.7.16, p. 135, as required of X in 2.7.1, p. 121.
    Supporting lemma. *)
Lemma punctured_space_locally_compact : locally_compact [set: X].
Proof.
apply: open_subspace_locally_compact; last exact: punctured_space_open.
exact: euclidean_closed_ball_compact.
Qed.

(** Source for [linear_group_punctured_nonzero]: a member of GL(n, R)
    maps R^n ~ {0} into R^n ~ {0}, Federer 2.7.16, p. 135. Supporting
    lemma. *)
Lemma linear_group_punctured_nonzero (g : GL) (x : X) :
  euclidean_linear_group_action g (set_val x) \in ~` [set (0 : E)].
Proof.
apply: mem_set=> /= h0.
have hx : set_val x <> 0 by have := set_valP x.
apply: hx; apply: (set_valP g).
have h00 : (set_val g : Hom V V) 0 = 0 by exact: (linear0 (hom_as_linear (set_val g : Hom V V))).
by rewrite h00; exact: h0.
Qed.

(** Source for [punctured_linear_action]: the transitive action of
    GL(n, R) on R^n ~ {0}, A(f, x) = f(x), Federer 2.7.16, p. 135.
    Definition. *)
Definition punctured_linear_action (g : GL) (x : X) : X :=
  exist _ (euclidean_linear_group_action g (set_val x)) (linear_group_punctured_nonzero g x).

(** Source for [punctured_linear_action_continuous]: the action of
    GL(n, R) on R^n ~ {0} is continuous on the product
    GL(n, R) x (R^n ~ {0}), Federer 2.7.16, p. 135, with 2.7.1, p. 121.
    Supporting lemma. *)
Lemma punctured_linear_action_continuous :
  continuous (fun p : GL * X => punctured_linear_action p.1 p.2).
Proof.
apply: set_type_continuous_into.
have -> : set_val \o (fun p : GL * X => punctured_linear_action p.1 p.2) =
    (fun q : H * E => ((q.1 : Hom V V) q.2 : E)) \o (fun p : GL * X => (set_val p.1, set_val p.2)).
  by [].
have hp : continuous (fun p : GL * X => ((set_val p.1 : H), (set_val p.2 : E))).
  apply: (@topological_pair_continuous (GL * X)%type H E).
  - move=> q; exact: continuous_comp (@first_projection_continuous GL X q)
      (@set_type_val_continuous H _ q.1).
  - move=> q; exact: continuous_comp (@second_projection_continuous GL X q)
      (@set_type_val_continuous E _ q.2).
move=> p; apply: continuous_comp; first exact: hp.
exact: (@hom_evaluation_continuous R V V _ _ hB hB n _ hb).
Qed.

(** Source for [punctured_linear_action_compatible]: A(g h, x) =
    A(g, A(h, x)), Federer 2.7.1, p. 121, for the action of GL(n, R) on
    R^n ~ {0} of 2.7.16, p. 135. Supporting lemma. *)
Lemma punctured_linear_action_compatible (g h : GL) (x : X) :
  punctured_linear_action (mul g h) x = punctured_linear_action g (punctured_linear_action h x).
Proof.
apply: val_inj; rewrite /= /euclidean_linear_group_action.
by rewrite (linear_group_mulE (linear_group_operations hB hb)).
Qed.

(** Source for [punctured_linear_orbit_onto]: "a transitive action
    results through replacement of R^n by R^n ~ {0}", Federer 2.7.16,
    p. 135: im A^x = R^n ~ {0} (general_linear_transitive_punctured).
    Supporting lemma. *)
Lemma punctured_linear_orbit_onto (x : X) : orbit_map punctured_linear_action x @` setT = setT.
Proof.
apply/seteqP; split=> // y _.
have hx : set_val x != 0 by apply/eqP; have := set_valP x.
have hy : set_val y != 0 by apply/eqP; have := set_valP y.
have [f [hdf hfx]] := general_linear_transitive_punctured hx hy.
have hfi : linear_group hB hb (hom_of_linear f : H) by exact: (euclidean_det_injective f).1 hdf.
exists (exist _ (hom_of_linear f : H) (mem_set hfi))=> //.
by apply: val_inj.
Qed.

(** Source for [punctured_linear_orbit_open]: "for each x in X the map
    A^x: G -> X ... is open", Federer 2.7.1, p. 121, for the action of
    GL(n, R) on R^n ~ {0} of 2.7.16, p. 135. If f is in an open set U
    of GL(n, R) and |z - f(x)| < r |x|, where U contains the members g
    of GL(n, R) with ||g - f|| < r, then
    g = f + (x . x)^{-1} (v |-> (v . x) (z - f(x))) satisfies g(x) = z
    and ||g - f|| < r. Direct formalisation. *)
Theorem punctured_linear_orbit_open (x : X) : is_open_map (orbit_map punctured_linear_action x).
Proof.
move=> U hU; rewrite openE=> y [g hgU <-]; rewrite /interior.
have [O hO hOU] := hU.
have hgO : O (set_val g) by rewrite -hOU in hgU.
have hOG : nbhs (set_val g : H) (O `&` linear_group hB hb).
  apply: open_nbhs_nbhs; split; first exact: openI hO (linear_group_set_open (hB := hB) (hb := hb)).
  by split=> //; exact: set_valP.
have [r hr hrO] := (hom_space_nbhs_operator _ _).1 hOG.
pose x0 : E := set_val x.
have hx0 : x0 != 0 by apply/eqP; have := set_valP x.
have hN0 : 0 < N x0 by rewrite inner_norm_gt0.
have hd : 0 < r * N x0 by rewrite mulr_gt0.
have hnb := @set_type_val_continuous E _ (orbit_map punctured_linear_action x g) _
  (nbhsx_ballx _ _ hd).
apply: (@filterS _ _ (nbhs_filter _) _ _ _ hnb)=> z /= hz.
pose y0 : E := set_val (orbit_map punctured_linear_action x g).
pose w : E := (euclidean_inner_product x0 x0)^-1 *: (set_val z - y0).
pose h : Hom V V := (set_val g : Hom V V) + hom_rank_one hB x0 w.
have hw : onorm (h - set_val g) < r.
  have -> : h - set_val g = hom_rank_one hB x0 w by rewrite /h addrC addKr.
  apply: le_lt_trans (hom_rank_one_operator_norm hB hB hb x0 w) _.
  rewrite /w inner_normZ -(inner_norm_sqr hB x0) normfV normrX ger0_norm ?inner_norm_nonnegative //.
  rewrite mulrA expr2 invfM mulrA mulfV ?gt_eqF // mul1r mulrC ltr_pdivrMr //.
  by move: hz; rewrite -ball_normE /= distrC.
have [hhO hhG] := hrO (h : H) hw.
exists (exist _ (h : H) (mem_set hhG)); first by rewrite -hOU.
apply: val_inj; rewrite /= /euclidean_linear_group_action /h hom_addE hom_rank_oneE.
rewrite /w scalerA mulfV; first by rewrite scale1r /y0 /= addrC subrK.
by rewrite -(inner_norm_sqr hB x0) expf_neq0 // gt_eqF.
Qed.

(** Source for [punctured_linear_homogeneous]: "a transitive action
    results through replacement of R^n by R^n ~ {0}", Federer 2.7.16,
    p. 135: R^n ~ {0} is a homogeneous space of GL(n, R) through
    A(f, x) = f(x), in the sense of 2.7.1, p. 121. Direct
    formalisation. *)
Theorem punctured_linear_homogeneous : is_homogeneous_space mul punctured_linear_action.
Proof.
split.
- exact: punctured_linear_action_continuous.
- exact: punctured_linear_action_compatible.
- exact: punctured_linear_orbit_open.
- exact: punctured_linear_orbit_onto.
Qed.

End EuclideanLinearGroup.

Arguments general_linear_det {R n}.
Arguments euclidean_linear_group_action {R n}.
Arguments punctured_linear_action {R n}.
