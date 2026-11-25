(** Federer (1969), 4.1.19, p. 377: once
    the weak equation annihilates ker q,
    the original bounded pair functional descends
    to exactly one flat cochain. The
    common bound follows from 4.1.18's
    arbitrary-error representation at each original K. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces SmoothCompactSet CurrentFlatNorm FlatCurrentsUP
  FlatCurrentUnionSpace FlatCochainUP FlatCochainSpace
  LinearSubspaceRepresentationUP ExtendedScaledErrorBound
  SurjectiveHomFunctionalFactor.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section PairDescent.
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

(** Source for [flat_cochain_pair_descent_exists]:
    a bounded pair functional annihilating ker q
    gives a flat cochain with its unchanged
    common bound, supporting the converse in
    Federer 4.1.19, p. 377.
    This adapter does not assume the weak
    equation already implies kernel annihilation. *)
Theorem flat_cochain_pair_descent_exists (beta : Hom P R^o) (c : R) :
  0 <= c -> (forall v, `|beta v| <= c*J v) ->
  (forall v, q v=0 -> beta v=0) ->
  exists alpha : A,
    (forall v, E alpha (q v)=beta v) /\
    @is_flat_cochain_bound R h2 n m U hU (E alpha) c.
Proof.
move=> hC hBound hKernel.
have [F hAgree] := @surjective_hom_functional_factor_exists R P W R^o
  q beta hOnto hKernel.
have hF : @is_flat_cochain_bound R h2 n m U hU F c.
  split; first exact: hC.
  move=> K T hFlat.
  have hLimit : ((`|F T|)%:E <= (c*fine (FK K (inc T)))%:E)%E.
    apply: (@extended_upper_bound_from_scaled_errors R
      (`|F T|)%:E (c*fine (FK K (inc T))) c hC).
    move=> delta hDelta.
    have [v [hQ hCost]] := @hSecond K T hFlat delta hDelta.
    have hValue : F T=beta v by rewrite -hQ; exact: hAgree.
    rewrite lee_fin hValue -mulrDr.
    exact: (le_trans (hBound v) (ler_wpM2l hC hCost)).
  by rewrite lee_fin in hLimit.
have hMember : @is_flat_cochain R h2 n m U hU F by exists c.
have [alpha hAlpha] := @subspace_representation_full R (Hom W R^o) A
  (@flat_cochain_subspace R h2 n m U hU) E
  (@flat_cochain_space_laws R h2 n m U hU) F hMember.
exists alpha; rewrite hAlpha; split; first exact: hAgree.
exact: hF.
Qed.

(** Source for [flat_cochain_pair_descent_unique]:
    the two original representation actions uniquely
    determine the cochain, Federer 4.1.19,
    p. 377, once they determine its
    induced beta and q is onto. No
    fixed compact index is added. *)
Theorem flat_cochain_pair_descent_unique (alpha gamma : A) :
  (forall v, E alpha (q v)=E gamma (q v)) -> alpha=gamma.
Proof.
move=> hAgree.
apply: (subspace_representation_injective
  (@flat_cochain_space_laws R h2 n m U hU)).
apply: hom_ext=> T.
have [v <-] := hOnto T.
exact: hAgree.
Qed.
End PairDescent.
