(** Federer (1969), 4.1.19, p. 377:
    the original bounded measurable weak pair
    determines a unique flat cochain. Use
    the preceding exact q presentation and
    original smooth graph closure, with no
    fixed compact index or finite-volume restriction. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import AlternatingForms Hom Bilinear RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentDomain CurrentCoefficientNorms CurrentSpaces SmoothCompactSet
  CurrentFlatNorm FlatCurrentsUP FlatCurrentUnionSpace FlatCochainSpace
  CurrentLonePairImageUP CurrentLonePairCost CurrentLonePairFlatUP
  CurrentLonePairImageSealed CurrentCompactSmoothDivergenceUP
  FlatCochainPairFunctional FlatCochainRepresentationUP
  BoundedPairFormFunctional CurrentWeakExteriorPairUP WeakExteriorPairGraphAction
  FlatCochainGraphClosureDescent FlatCochainPairDescent
  LonePairFormDensityAlmost.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section WeakPairConverse.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation UT := (current_domain R n U).
Local Notation hNX :=
  (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation P := (@current_lone_pair_space R h2 n m U hU).
Local Notation J := (@current_lone_pair_cost R h2 n m U hU).
Local Notation W := (@flat_current_union_space R h2 n m U hU).
Local Notation inc := (@flat_current_union_inclusion R h2 n m U hU).
Local Notation FK := (@current_flat_norm R h2 n m U hU).
Local Notation flatK := (@is_flat_current_supported_in R h2 n m U hU).
Local Notation A := (@flat_cochain_space R h2 n m U hU).
Local Notation E := (@flat_cochain_evaluation R h2 n m U hU).
Local Notation graph :=
  (@is_current_compact_smooth_divergence_pair R h2 n m U hU).
Local Notation raw := (@CurrentLonePair.map R h2 n m U hU).
Variable Q : Hom P W.
Hypothesis hQ : @is_current_lone_pair_flat_map R h2 n m U hU Q.
Hypothesis hOnto : forall T, exists v, Q v=T.
Hypothesis hSecond : forall (K : smooth_compact_set hNX U) (T : W),
  flatK K (inc T) -> forall delta : R, 0 < delta ->
  exists v : P, Q v=T /\ J v <= fine (FK K (inc T))+delta.
Hypothesis hGraphClosure : forall v : P, raw v=0 ->
  forall delta : R, 0 < delta -> exists w : P,
    graph w /\ J (v-w)%R < delta.

(** Source for [flat_cochain_weak_pair_converse]:
    the converse existence and uniqueness of
    Federer 4.1.19, p. 377,
    from the literal original weak equation.
    This supporting presentation adapter consumes
    only the preceding onto, arbitrary-error cost
    and exact graph-closure conclusions of 4.1.18. *)
Theorem flat_cochain_weak_pair_converse
    (phi : UT -> A_m X R^o m) (psi : UT -> A_m X R^o m.+1) :
  @is_bounded_measurable_current_form R h2 n U m phi ->
  @is_bounded_measurable_current_form R h2 n U m.+1 psi ->
  @is_weak_current_exterior_pair R h2 n m U hU phi psi ->
  exists alpha : A,
    @is_flat_cochain_pair_density R h2 n m U hU Q alpha phi psi /\
    forall gamma : A,
      @is_flat_cochain_pair_density R h2 n m U hU Q gamma phi psi -> gamma=alpha.
Proof.
move=> hPhi hPsi hWeak.
have [beta [c [hC [hBound hDensity]]]] :=
  @bounded_pair_form_functional_exists R h2 n m U hU phi psi hPhi hPsi.
have hGraph := (@weak_exterior_pair_graph_action_iff R h2 n m U hU
  beta phi psi hDensity).1 hWeak.
have hClosure (v : P) (hv : Q v=0) : forall delta : R, 0 < delta ->
    exists w : P, graph w /\ J (v-w)%R < delta.
  have hRaw : raw v=0.
    by rewrite -(hQ v) hv (lin0 (hom_linear inc)).
  exact: (@hGraphClosure v hRaw).
have [alpha [hAlpha [hAlphaBound hUnique]]] :=
  @flat_cochain_graph_closure_descent_exists R h2 n m U hU P J Q hOnto
    hSecond graph hClosure beta c hC hBound hGraph.
have hPair : @flat_cochain_pair_functional R h2 n m U hU Q alpha=beta.
  apply: hom_ext=> v; exact: hAlpha.
exists alpha; split.
- by rewrite /is_flat_cochain_pair_density hPair.
- move=> gamma hGamma; apply: hUnique=> v.
  have hEqual := @lone_pair_form_functional_unique R h2 n m U hU
    (@flat_cochain_pair_functional R h2 n m U hU Q gamma) beta
    phi psi hGamma hDensity.
  exact: (congr1 (fun b : Hom P R^o => b v) hEqual).
Qed.
End WeakPairConverse.
