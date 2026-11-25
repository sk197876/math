(** Federer (1969), 3.2.9, p. 247: the
    stacked map U=(f,p) and its actual
    differential. Use the existing two block
    injections, linear postcomposition and addition. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness RealNormUP EuclideanBlockLinearMaps EuclideanBlockNorms
  EuclideanBlockCoordinates EuclideanBlockLinear NormDifferentialUP NormDifferentialLinear
  NormDifferentialFiniteCalculus NormDifferentialArithmetic NormFiniteLinearBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Stack.
Variable R:realType.
Variables m n k:nat.
Local Notation X:=(R_n R m).
Local Notation Y:=(R_n R n).
Local Notation W:=(R_n R k).
Local Notation Z:=(R_n R (n+k)).
Local Notation I:=(@euclidean_first_injection_map R n k).
Local Notation K:=(@euclidean_last_injection_map R n k).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R m)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NZ:=(inner_norm (@euclidean_inner_productP R (n+k))).

(** Source for [euclidean_stacked_map]: the map
    U_lambda in Federer 3.2.9, p. 247,
    expressed in the canonical block coordinates. *)
Definition euclidean_stacked_map (f:X->Y) (p:Hom X W) (x:X):Z:=I (f x)+K (p x).

(** Source for [euclidean_stacked_linear_map]: the
    linear map (Df,p) in the kernel calculation
    of Federer 3.2.9, p. 247. *)
Definition euclidean_stacked_linear_map (L:Hom X Y) (p:Hom X W):Hom X Z:=
  hom_comp I L+hom_comp K p.

(** Source for [euclidean_stacked_linear_value]: exact
    value of the stacked differential used in
    Federer 3.2.9, p. 247. *)
Lemma euclidean_stacked_linear_value (L:Hom X Y) p x:
  euclidean_stacked_linear_map L p x=euclidean_stacked_map L p x.
Proof. by rewrite /euclidean_stacked_linear_map /euclidean_stacked_map hom_addE !hom_compE. Qed.

(** Source for [euclidean_stacked_first_block]: the
    first coordinate block is f, supporting
    Federer 3.2.9, p. 247. *)
Lemma euclidean_stacked_first_block (f:X->Y) p x:
  @euclidean_first_block R n k (euclidean_stacked_map f p x)=f x.
Proof.
change (@euclidean_first_block_map R n k (euclidean_stacked_map f p x)=f x).
rewrite /euclidean_stacked_map linearD.
change (euclidean_first_block (@euclidean_first_injection R n k (f x))+
  euclidean_first_block (@euclidean_last_injection R n k (p x))=f x).
by rewrite euclidean_first_block_injectionK euclidean_first_block_last_injection addr0.
Qed.

(** Source for [euclidean_stacked_last_block]: the
    last coordinate block is p, supporting
    Federer 3.2.9, p. 247. *)
Lemma euclidean_stacked_last_block (f:X->Y) p x:
  @euclidean_last_block R n k (euclidean_stacked_map f p x)=p x.
Proof.
change (@euclidean_last_block_map R n k (euclidean_stacked_map f p x)=p x).
rewrite /euclidean_stacked_map linearD.
change (euclidean_last_block (@euclidean_first_injection R n k (f x))+
  euclidean_last_block (@euclidean_last_injection R n k (p x))=p x).
by rewrite euclidean_last_block_first_injection euclidean_last_block_injectionK add0r.
Qed.

(** Source for [euclidean_stacked_join]: agreement
    with the Cartesian notation U=(f,p) of
    Federer 3.2.9, p. 247. *)
Lemma euclidean_stacked_join (f:X->Y) p x:
  euclidean_stacked_map f p x=euclidean_block_join (f x,p x).
Proof.
have hSplit:euclidean_block_split (euclidean_stacked_map f p x)=(f x,p x).
  apply:injective_projections; [exact:euclidean_stacked_first_block|exact:euclidean_stacked_last_block].
by rewrite -(euclidean_block_splitK (euclidean_stacked_map f p x)) hSplit.
Qed.

(** Source for [euclidean_stacked_differential]: the
    actual stacked differential in the proof of
    Federer 3.2.9, p. 247. No derivative
    is assigned outside the actual differential domain
    of f. The constant linear p is differentiated
    using only finite-dimensional norm bounds. *)
Theorem euclidean_stacked_differential (f:X->Y) p a (L:Hom X Y):
  has_norm_differential NX NY (fun _=>True) f a L ->
  has_norm_differential NX NZ (fun _=>True) (euclidean_stacked_map f p) a
    (euclidean_stacked_linear_map L p).
Proof.
move=>hL.
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose hNZ:=inner_norm_real_norm (@euclidean_inner_productP R (n+k)).
have hI:norm_bounded_linear NY NZ I.
  exists 1; split; first exact:ler01.
  move=>v; change (is_true (NZ (@euclidean_first_injection R n k v)<=1*NY v)).
  by rewrite euclidean_first_injection_norm mul1r.
have hQ:norm_bounded_linear NX NZ (hom_comp K p):=
  norm_finite_linear_bounded hNX hNZ (@coordinate_basisP R m) (hom_comp K p).
have hFirst:=norm_differential_postcompose hNX hL hI.
have hSecond:=norm_differential_linear hNX hNZ (norm_differential_interior hL) hQ.
exact (norm_differential_add hNZ hFirst hSecond).
Qed.
End Stack.
