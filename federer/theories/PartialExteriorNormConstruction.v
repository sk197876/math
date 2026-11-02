(** Private witness for Federer (1969), 3.2.20, p. 256: existence of the
    intrinsic partial exterior norm from finite bounded word costs.
    The ambient differential provides a bound only; the final norm is
    specified by its laws on the actual partial graph. Only the sealing
    module and assumptions audit may import this witness module. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanLinearMaps FiniteExteriorPowers PartialFunctionUP InnerNorm InnerExterior ExteriorNorm
  EuclideanLinearJacobian PartialExteriorNormUP PartialExteriorNormLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [partial_exterior_norm_bounded_witness_exists]: supporting
    supremum-existence step for Federer 3.2.20, p. 256, with
    the norm convention of 1.7.6, p. 33. A finite bound
    on actual exterior-word costs gives their least nonnegative bound.
    Adjoining zero handles empty positive-degree graph domains without
    asserting that a maximum is attained. *)
Theorem partial_exterior_norm_bounded_witness_exists (R : realType) n k q
    (d : partial_function (R_n R n) (R_n R k)) :
  (exists L : R, 0<=L /\ is_partial_exterior_bound q d L) ->
  exists J : R, is_partial_exterior_norm q d J.
Proof.
move=> [L [hL hBound]].
pose S : set R := [set 0] `|` [set r | exists
  (v : 'I_q -> R_n R n) (w : 'I_q -> R_n R k),
  (forall i, partial_function_graph d (v i) (w i)) /\
  exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
    (e_lambda v (ord_tuple q))<=1 /\
  r=exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R k)
    (e_lambda w (ord_tuple q))].
have hZero : S 0 by left.
have hNonempty : exists r, S r by exists 0.
have hUpper : ubound S L.
  move=> r [->|[v [w [hG [hU ->]]]]]; [exact hL|exact: hBound v w hG hU].
have hBounded : exists c, ubound S c by exists L.
pose J := sup S.
have hJ0 : 0<=J := ub_le_sup hBounded hZero.
exists J; constructor; first exact hJ0.
- move=> v w hG hU.
  apply: (ub_le_sup hBounded); right; exists v,w; by split=> //; split.
- move=> M hM hMBound; apply: (ge_sup hNonempty)=> r.
  move=> [->|[v [w [hG [hU ->]]]]]; [exact hM|exact: hMBound v w hG hU].
Qed.

