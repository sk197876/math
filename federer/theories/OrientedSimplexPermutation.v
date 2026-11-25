(** Federer (1969), 4.1.11, p. 366: the full
    vertex-permutation formula with exactly the original
    Chapter 1 index. The opaque current and independent
    simplex laws remain unchanged. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals fingroup perm.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces InversionCount PermutationIndexParity
  OrientedSimplexCurrentSealed OrientedSimplexTranspositions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [oriented_simplex_current_permutation]:
    [u_sigma(0),...,u_sigma(m)] equals index(sigma)
    times [u_0,...,u_m], Federer 4.1.11, p. 366.
    The original arbitrary ambient dimension and all
    degenerate vertex families are retained. *)
Theorem oriented_simplex_current_permutation (R:realType) (h2:(1+1:R)!=0)
    n m (s:'S_(m.+1)) (v:'I_(m.+1)->R_n R n):
  @OrientedSimplexCurrent.value R h2 n m (fun k=>v (s k))=
    FedererPermutation.index R s*:@OrientedSimplexCurrent.value R h2 n m v.
Proof.
rewrite (@permutation_index_parity R h2).
exact:(@oriented_simplex_current_permutation_parity R h2 n m s v).
Qed.

(** Source for [oriented_simplex_current_repeated_vertices]:
    an original simplex with a repeated vertex is zero,
    supporting the prism and rectangular decompositions
    in Federer 4.1.11, p. 366. This follows from
    genuine transposition alternation, not a nondegeneracy
    condition on the definition. *)
Theorem oriented_simplex_current_repeated_vertices (R:realType) (h2:(1+1:R)!=0)
    n m (v:'I_(m.+1)->R_n R n) (i j:'I_(m.+1)):
  i!=j->v i=v j->@OrientedSimplexCurrent.value R h2 n m v=0.
Proof.
move=>hij hValues.
have hFamily:(fun k=>v (tperm i j k))=v.
  apply:funext=>k;case:(tpermP i j k)=>[->|->|_ _];by [].
have hSwap:=@oriented_simplex_current_transposition R h2 n m i j hij v.
rewrite hFamily in hSwap.
have hScale:(1+1:R)*:@OrientedSimplexCurrent.value R h2 n m v=0.
  by rewrite scalerDl !scale1r {1}hSwap addNr.
move/eqP:hScale;rewrite scaler_eq0 (negPf h2) /=;exact/eqP.
Qed.
