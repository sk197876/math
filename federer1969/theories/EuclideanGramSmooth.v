(** Federer (1969), 3.2.28(1), printed p. 263: the polynomial
    P(g)= g* g is smooth and its actual differential is
    DP(g)h= h* g+g* h. These statements cover all natural dimensions. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom TensorUP RealNormUP GrassmannAbbreviations
  EuclideanHomOperator EuclideanRectangularAdjoint EuclideanGramDifferentialAlgebra
  NormDifferentialUP NormDifferentialLinear NormOpenDomainLaws
  NormClassOneUP NormRegularity NormRegularityOperations
  NormRegularityBilinear NormDifferentialBilinearProduct NormBilinearDifferentialAlgebra
  NormDifferentialDirectional NormBoundedBilinearUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Gram.
Variable R:realType.
Variables m n:nat.
Local Notation X:=(Hom (R_n R m) (R_n R n)).
Local Notation Y:=(Hom (R_n R m) (R_n R m)).
Local Notation NX:=(@euclidean_operator_norm R m n).
Local Notation NY:=(@euclidean_operator_norm R m m).
Local Notation hNX:=(@euclidean_operator_norm_is_norm R m n).
Local Notation hNY:=(@euclidean_operator_norm_is_norm R m m).

(** Source for [euclidean_gram_smooth]: smoothness of the
    quadratic map P, Federer 3.2.28(1), p. 263, from the
    bounded bilinear class law of 3.1.11, p. 220. *)
Theorem euclidean_gram_smooth:
  norm_class_all_orders hNX hNY (fun _=>True) (@euclidean_gram_map R m n).
Proof.
move=>k.
have hId:norm_class hNX hNX (fun _=>True) (fun x:X=>x) k.
  apply:(@norm_class_linear R X X NX NX hNX hNX (fun _=>True)
    (hom_of_linear (linear_id X)) k).
  - move=>x _; exact:norm_full_domain_interior.
  - exists 1; split; first exact:ler01.
    by move=>x; rewrite mul1r.
exact:(@norm_class_bilinear R X X X Y NX NX NX NY hNX hNX hNX hNY
  (fun _=>True) (fun x=>x) (fun x=>x)
  (fun g h=>hom_comp (euclidean_rectangular_adjoint g) h) k
  (@euclidean_gram_pair_bounded R m n) hId hId).
Qed.

(** Source for [euclidean_gram_has_differential]: the actual
    displayed differential DP(g), Federer 3.2.28(1), p. 263.
    No candidate-field or differentiability premise is assumed. *)
Theorem euclidean_gram_has_differential (g:X):
  has_norm_differential NX NY (fun _=>True) (@euclidean_gram_map R m n)
    g (euclidean_gram_differential g).
Proof.
have hId:has_norm_differential NX NX (fun _=>True) (fun x:X=>x)
    g (hom_of_linear (linear_id X)).
  apply:(@norm_differential_linear R X X NX NX hNX hNX (fun _=>True)
    g (hom_of_linear (linear_id X))).
  - exact:norm_full_domain_interior.
  - exists 1; split; first exact:ler01.
    by move=>x; rewrite mul1r.
have [hB [C [hC hb]]]:=@euclidean_gram_pair_bounded R m n.
have hd:=@norm_differential_bilinear_product R X X X Y NX NX NX NY
  hNX hNX hNX hNY _ hB C (fun _=>True) (fun x=>x) (fun x=>x)
  g (hom_of_linear (linear_id X)) (hom_of_linear (linear_id X)) hC hb hId hId.
have hEq:norm_bilinear_product_linear_term hB g g
    (hom_of_linear (linear_id X)) (hom_of_linear (linear_id X))=
    euclidean_gram_differential g.
  apply:hom_ext=>h; by [].
by rewrite hEq in hd.
Qed.

(** Source for [euclidean_gram_class_one_field]: the smooth Gram
    map has the displayed continuous differential field, Federer
    3.2.28(1), p. 263. Uniqueness identifies the actual field
    supplied by the class-one theorem with the displayed formula. *)
Theorem euclidean_gram_class_one_field:
  is_norm_class_one_field NX NY (fun _=>True) (@euclidean_gram_map R m n)
    (@euclidean_gram_differential R m n).
Proof.
have [D hD]:=(norm_class_firstP hNX hNY (fun _=>True)
  (@euclidean_gram_map R m n)).1 (euclidean_gram_smooth 1%N).
have hEq:D= @euclidean_gram_differential R m n.
  apply:funext=>g.
  exact:(norm_differential_unique hNX hNY
    (norm_class_one_differential hD I) (euclidean_gram_has_differential g)).
by rewrite -hEq.
Qed.
End Gram.
