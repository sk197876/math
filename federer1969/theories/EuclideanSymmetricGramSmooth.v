(** Federer (1969), 3.2.28(1), printed p. 263: smoothness
    and the actual differential of P:Hom(R^m,R^n)->Y_m.
    The codomain carries its inherited Hom Hilbert norm. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom TensorUP ModuleQuotient SubspaceCarrier
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  HilbertFormCompactness HomCompositionDeterminant NormedSubspace
  EuclideanHomInnerCharts EuclideanSymmetricEndomorphismSpace
  EuclideanGramDifferentialAlgebra EuclideanGramInnerDifferential EuclideanSymmetricGram
  NormDifferentialUP NormDifferentialIsometricEvaluation NormFiniteLinearBound
  NormRegularity NormRegularityLinearMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section SymmetricSmooth.
Variable R:realType.
Variables m n:nat.
Local Notation X:=(Hom (R_n R m) (R_n R n)).
Local Notation E:=(Hom (R_n R m) (R_n R m)).
Local Notation S:=(@euclidean_symmetric_hom_subspace R m).
Local Notation Y:=(subspace_space S).
Local Notation NX:=(inner_norm (@euclidean_hom_inner_productP R m n)).
Local Notation NE:=(inner_norm (@euclidean_hom_inner_productP R m m)).
Local Notation NY:=(subspace_norm NE S).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_hom_inner_productP R m n)).
Local Notation hNE:=(inner_norm_real_norm (@euclidean_hom_inner_productP R m m)).
Local Notation hNY:=(subspace_norm_laws hNE S).

(** Source for [euclidean_symmetric_gram_smooth]: P into
    the actual symmetric codomain is of class infinity,
    Federer 3.2.28(1), p. 263. A local linear
    retraction is used only in this proof of regularity. *)
Theorem euclidean_symmetric_gram_smooth:
  norm_class_all_orders hNX hNY (fun _=>True) (@euclidean_symmetric_gram R m n).
Proof.
move=>k.
pose L:=hom_of_linear (@subspace_retraction R E S).
have hBound:norm_bounded_linear NE NY L.
  exact:(norm_finite_linear_bounded hNE hNY
    (@hom_rank_one_baseP R (R_n R m) (R_n R m) m m
      (@coordinate_basis R m) (@coordinate_basisP R m)
      (@coordinate_basis R m) (@coordinate_basisP R m)) L).
have hEq:(fun g:X=>L (euclidean_gram_map g))=@euclidean_symmetric_gram R m n.
  apply:funext=>g; apply:subspace_val_injective.
  change (subspace_inclusion S (subspace_retraction S (euclidean_gram_map g))=
    subspace_val (euclidean_symmetric_gram g)).
  by rewrite euclidean_symmetric_gramE
    (@subspace_retraction_on R E S (euclidean_gram_map g)
      (@euclidean_gram_symmetric_range R m n g)).
rewrite -hEq.
exact:(@norm_class_postcompose_linear R X E Y NX NE NY hNX hNE hNY
  (fun _=>True) (@euclidean_gram_map R m n) L k hBound
  (@euclidean_gram_inner_smooth R m n k)).
Qed.

(** Source for [euclidean_symmetric_gram_has_differential]: the
    actual DP(g):Hom(R^m,R^n)->Y_m, Federer 3.2.28(1),
    p. 263. Isometric inclusion identifies the entire remainder
    and differential, with no extra derivative premise. *)
Theorem euclidean_symmetric_gram_has_differential (g:X):
  has_norm_differential NX NY (fun _=>True) (@euclidean_symmetric_gram R m n)
    g (euclidean_symmetric_gram_differential g).
Proof.
pose J:=hom_of_linear (@subspace_inclusion R E S).
apply:(@norm_differential_isometric_evaluation R X Y E NX NY NE J
  (fun y=>erefl) (fun _=>True) (@euclidean_symmetric_gram R m n) g
  (euclidean_symmetric_gram_differential g)).2.
have hF:(fun x:X=>J (euclidean_symmetric_gram x))=@euclidean_gram_map R m n.
  apply:funext=>x; exact:euclidean_symmetric_gramE.
have hL:hom_comp J (euclidean_symmetric_gram_differential g)=
    euclidean_gram_differential g.
  apply:hom_ext=>h; exact:euclidean_symmetric_gram_differentialE.
rewrite hF hL; exact:euclidean_gram_inner_has_differential.
Qed.
End SymmetricSmooth.
