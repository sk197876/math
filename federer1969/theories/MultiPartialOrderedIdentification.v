(** Federer (1969), 4.1.2, p. 347: the
    multiindex kernel derivative is identified with the
    ordered coordinate derivative proved in 3.1.11, p. 223.
    This adapter preserves the original exact derivative graphs. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP PartialFunctionUP GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness SymmetricMultiIndices SymmetricIndexBounds
  ContinuousMultilinearUP NormHigherDifferentialUP NormHigherSymmetricFormUP
  NormHigherMultiPartialUP NormHigherCoordinatePartials NormIteratedDirectionalUP NormIteratedPartial.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [norm_multi_partial_to_ordered]: the original
    multiindex derivative equals any ordered partial with
    that occurrence count, Federer 3.1.11, p. 223,
    reused for the convolution identity of 4.1.2, p. 347. *)
Theorem norm_multi_partial_to_ordered (R:realType) n (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (Z:nat->lmodType R)
    (ev:forall k,{ffun 'I_k->R_n R n}->Hom (Z k) Y) (ZN:forall k,Z k->R)
    (hZ:forall k,is_continuous_multilinear_space
      (inner_norm (@euclidean_inner_productP R n)) NY (@ev k) (@ZN k))
    (A:R_n R n->Prop) (f:R_n R n->Y) k (alpha:symmetric_indices n k)
    (nu:seq 'I_n) a y:
  size nu=k ->(forall i,count_mem i nu=symmetric_indices_unbound alpha i) ->
  has_norm_multi_partial (inner_norm (@euclidean_inner_productP R n)) ev ZN A f alpha a y ->
  has_norm_iterated_directional NY A f [seq (@coordinate_basis R n) i|i<-nu] a y.
Proof.
move=>hSize hCount hPartial.
have [z [hz hValue]]:=hPartial.
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R n).
have [phi hPhi]:=norm_higher_differential_form_exists hN hNY hZ hz.
have [v [hv hIter]]:=@norm_multi_partial_ordered_formula R n Y
  (inner_norm (@euclidean_inner_productP R n)) NY hN hNY Z ev ZN hZ
  A f k nu alpha a phi hSize hCount hPhi.
have hSame:=@norm_multi_partial_unique R n Y (inner_norm (@euclidean_inner_productP R n))
  NY hN hNY Z ev ZN hZ A f k alpha a v y hv hPartial.
rewrite hSame in hIter.
exact:(@norm_iterated_partial_graph R n Y NY hNY A f nu a y).1 hIter.
Qed.
