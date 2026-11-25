(** Federer (1969), 3.2.28(1), printed p. 263: the
    Gram map and differential with their actual symmetric
    codomain Y_m. Subtype inclusions retain the exact ambient
    values; the surjectivity theorem is proved, not postulated. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP ModuleQuotient SubspaceCarrier
  GrassmannAbbreviations EuclideanInnerProduct InnerProductUP
  SymmetricEndomorphisms EuclideanSymmetricEndomorphismSpace
  EuclideanGramDifferentialAlgebra EuclideanGramTangentAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section SymmetricGram.
Variable R:realType.
Variables m n:nat.
Local Notation X:=(Hom (R_n R m) (R_n R n)).
Local Notation Y:=(subspace_space (@euclidean_symmetric_hom_subspace R m)).

(** Source for [euclidean_symmetric_gram]: P(g)=g* g as
    a map into the actual Y_m, Federer 3.2.28(1), p. 263.
    This only attaches the proved symmetric range law. *)
Definition euclidean_symmetric_gram (g:X):Y:=
  subspace_lift (@euclidean_gram_symmetric_range R m n g).

(** Source for [euclidean_symmetric_gramE]: the inclusion of
    P into Hom is exactly g* g, Federer 3.2.28(1), p. 263. *)
Lemma euclidean_symmetric_gramE g:
  subspace_val (euclidean_symmetric_gram g)=euclidean_gram_map g.
Proof. exact:subspace_liftE. Qed.

(** Source for [euclidean_symmetric_gram_differential_fun]:
    DP(g)h in the actual Y_m, Federer 3.2.28(1), p. 263. *)
Definition euclidean_symmetric_gram_differential_fun (g h:X):Y:=
  subspace_lift (@euclidean_gram_differential_symmetric_range R m n g h).

(** Source for [euclidean_symmetric_gram_differential_linear]:
    linearity of DP(g) with its symmetric codomain,
    Federer 3.2.28(1), p. 263. *)
Lemma euclidean_symmetric_gram_differential_linear g:
  linear (euclidean_symmetric_gram_differential_fun g).
Proof.
move=>c h k; apply:subspace_val_injective.
change (euclidean_gram_differential g (c*:h+k)=
  c*:euclidean_gram_differential g h+euclidean_gram_differential g k).
exact:linearP.
Qed.
HB.instance Definition _ g:=GRing.isLinear.Build R X Y *:%R
  (euclidean_symmetric_gram_differential_fun g)
  (euclidean_symmetric_gram_differential_linear g).

(** Source for [euclidean_symmetric_gram_differential]: the
    linear map DP(g):Hom(R^m,R^n)->Y_m, Federer
    3.2.28(1), p. 263. *)
Definition euclidean_symmetric_gram_differential (g:X):Hom X Y:=
  hom_of_linear (GRing.Linear.clone _ _ _ _
    (euclidean_symmetric_gram_differential_fun g) _).

(** Source for [euclidean_symmetric_gram_differentialE]: exact
    inclusion of DP(g)h into Hom(R^m,R^m), Federer
    3.2.28(1), p. 263. *)
Lemma euclidean_symmetric_gram_differentialE g h:
  subspace_val (euclidean_symmetric_gram_differential g h)=
    euclidean_gram_differential g h.
Proof. exact:subspace_liftE. Qed.

(** Source for [euclidean_symmetric_gram_differential_surjective]:
    im DP(g)=Y_m when g is injective, Federer
    3.2.28(1), p. 263, on the actual codomain carrier. *)
Theorem euclidean_symmetric_gram_differential_surjective (g:X):
  injective g ->forall y:Y, exists h:X,
    euclidean_symmetric_gram_differential g h=y.
Proof.
move=>hg y.
have hSym:=(@euclidean_symmetric_hom_membership R m (subspace_val y)).1
  (@subspace_valP R (Hom (R_n R m) (R_n R m))
    (@euclidean_symmetric_hom_subspace R m) y).
have [h he]:=@euclidean_gram_differential_surjective R m n g hg
  (subspace_val y) hSym.
exists h; apply:subspace_val_injective.
by rewrite euclidean_symmetric_gram_differentialE he.
Qed.
End SymmetricGram.
