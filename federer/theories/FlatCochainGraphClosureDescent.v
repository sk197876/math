(** Federer (1969), 4.1.19, p. 377:
    use the preceding exact graph-kernel closure
    to descend the pair functional obtained
    from a weak derivative pair. This
    supporting adapter keeps every original cost
    and closure premise explicit until 4.1.18 is released. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces SmoothCompactSet CurrentFlatNorm FlatCurrentsUP
  FlatCurrentUnionSpace FlatCochainUP FlatCochainSpace
  FlatCochainPairDescent SeminormFunctionalClosedKernel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section GraphClosureDescent.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Variable U : set (R_n R n).
Hypothesis hU : forall x, U x -> norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation hNX :=
  (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation W := (@flat_current_union_space R h2 n m U hU).
Local Notation inc := (@flat_current_union_inclusion R h2 n m U hU).
Local Notation FK := (@current_flat_norm R h2 n m U hU).
Local Notation flatK := (@is_flat_current_supported_in R h2 n m U hU).
Local Notation A := (@flat_cochain_space R h2 n m U hU).
Local Notation E := (@flat_cochain_evaluation R h2 n m U hU).
Variable P : lmodType R.
Variable J : P -> R.
Variable q : Hom P W.
Hypothesis hOnto : forall w, exists v, q v=w.
Hypothesis hSecond : forall (K : smooth_compact_set hNX U) (T : W),
  flatK K (inc T) -> forall delta : R, 0 < delta ->
  exists v : P, q v=T /\ J v <= fine (FK K (inc T))+delta.
Variable G : set P.
Hypothesis hGraphClosure : forall v : P, q v=0 ->
  forall delta : R, 0 < delta -> exists w : P,
    G w /\ J (v-w)%R < delta.

(** Source for [flat_cochain_graph_closure_descent_exists]:
    beta vanishing on every original smooth
    graph pair gives the unique flat cochain,
    supporting the converse of Federer 4.1.19,
    p. 377. The original kernel closure
    of 4.1.18 supplies precisely hGraphClosure;
    no additional annihilation axiom is introduced. *)
Theorem flat_cochain_graph_closure_descent_exists
    (beta : Hom P R^o) (c : R) :
  0 <= c -> (forall v, `|beta v| <= c*J v) ->
  (forall v, G v -> beta v=0) ->
  exists alpha : A,
    (forall v, E alpha (q v)=beta v) /\
    @is_flat_cochain_bound R h2 n m U hU (E alpha) c /\
    forall gamma : A,
      (forall v, E gamma (q v)=beta v) -> gamma=alpha.
Proof.
move=> hC hBound hGraph.
have hKernel (v : P) (hv : q v=0) : beta v=0.
  exact: (@seminorm_functional_annihilates_closure R P J beta c G v
    hC hBound hGraph (@hGraphClosure v hv)).
have [alpha [hAlpha hAlphaBound]] :=
  @flat_cochain_pair_descent_exists R h2 n m U hU P J q hOnto hSecond
    beta c hC hBound hKernel.
exists alpha; split; first exact: hAlpha.
split; first exact: hAlphaBound.
move=> gamma hGamma.
apply: (@flat_cochain_pair_descent_unique R h2 n m U hU P q hOnto
  gamma alpha)=> v.
exact: (eq_trans (hGamma v) (esym (hAlpha v))).
Qed.
End GraphClosureDescent.
