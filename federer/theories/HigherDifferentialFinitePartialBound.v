(** Federer (1969), 4.1.2, p. 347: finitely
    many coordinate partial bounds control the full
    derivative norm. This reuses the original finite
    reconstruction of 3.1.11, p. 223, rather
    than constructing another differential space. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness SymmetricMultiIndices
  ContinuousMultilinearUP ContinuousMultilinearNorm NormHigherDifferentialUP NormHigherMultiPartialUP
  NormHigherCoordinateReconstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_higher_differential_finite_partial_bound]: the
    finite coordinate expansion of Federer 3.1.11,
    p. 223, supplies the norm control
    used for smooth-topology convergence in 4.1.2,
    p. 347. The target has no
    dimension or completeness restriction. *)
Theorem norm_higher_differential_finite_partial_bound (R:realType) n (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (Z:nat->lmodType R)
    (ev:forall k,{ffun 'I_k->R_n R n}->Hom (Z k) Y) (ZN:forall k,Z k->R)
    (hZ:forall k,is_continuous_multilinear_space
      (inner_norm (@euclidean_inner_productP R n)) NY (@ev k) (@ZN k)) k:
  exists M:R,0<M /\ forall (A:R_n R n->Prop) (f:R_n R n->Y) a (z:Z k) r,
    0<=r ->
    has_norm_higher_differential (inner_norm (@euclidean_inner_productP R n)) ev ZN A f k a z ->
    (forall alpha:symmetric_indices n k,NY (@ev k (norm_multi_partial_arguments R alpha) z)<=r) ->
    @ZN k z<=M*r.
Proof.
have [L [hL hReconstruction]]:=@norm_higher_coordinate_reconstruction_exists R n Y NY hNY Z ev ZN hZ k.
have hFor alpha:exists C:R,0<=C /\ forall y,@ZN k (L alpha y)<=C*NY y.
  exact:(hL alpha).
have [C hC]:=choice hFor.
pose S:=\sum_(alpha:symmetric_indices n k) C alpha.
have hS:0<=S by apply:sumr_ge0=>alpha _; exact:(hC alpha).1.
exists (S+1); split; first by lra.
move=>A f a z r hr hz hCoefficients.
pose c:=fun alpha:symmetric_indices n k=>@ev k (norm_multi_partial_arguments R alpha) z.
have hPartials alpha:has_norm_multi_partial (inner_norm (@euclidean_inner_productP R n))
    ev ZN A f alpha a (c alpha).
  exists z; by split.
have hValue:=hReconstruction A f a z c hz hPartials.
pose hNk:=continuous_multilinear_norm_is_norm hNY (@hZ k).
rewrite hValue.
apply:le_trans (real_seminorm_sum hNk.1 _) _.
have hUpper:(\sum_(alpha:symmetric_indices n k) @ZN k (L alpha (c alpha)))<=S*r.
  rewrite /S mulr_suml; apply:ler_sum=>alpha _.
  apply:le_trans ((hC alpha).2 (c alpha)) _.
  exact:(ler_wpM2l (hC alpha).1 (hCoefficients alpha)).
apply:le_trans hUpper _.
apply:ler_wpM2r=>//; by rewrite lerDl.
Qed.
