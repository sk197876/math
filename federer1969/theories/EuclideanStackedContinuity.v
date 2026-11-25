(** Federer (1969), 3.2.9, p. 247: continuity
    of U_lambda=(f,p_lambda). Use the intrinsic
    class-zero laws for the continuous first block
    and bounded linear complementary block. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness
  EuclideanBlockLinearMaps EuclideanBlockNorms EuclideanStackedMap NormDifferentialUP NormFiniteLinearBound
  NormClassOneUP NormClassZeroPostcompose NormClassZeroArithmetic NormClassZeroWhole NormBoundedLinearTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_stacked_class_zero]: the
    continuity required before applying 3.2.2 to
    U_lambda in Federer 3.2.9, p. 247.
    No Lipschitz hypothesis on f is used. *)
Lemma euclidean_stacked_class_zero (R:realType) m n k
    (f:R_n R m->R_n R n) (p:Hom (R_n R m) (R_n R k)):
  norm_class_zero (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT f ->
  norm_class_zero (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R (n+k))) setT (euclidean_stacked_map f p).
Proof.
move=>hf.
pose NX:=inner_norm (@euclidean_inner_productP R m).
pose NY:=inner_norm (@euclidean_inner_productP R n).
pose NZ:=inner_norm (@euclidean_inner_productP R (n+k)).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hNZ:=inner_norm_real_norm (@euclidean_inner_productP R (n+k)).
pose I:=@euclidean_first_injection_map R n k.
pose Q:=hom_comp (@euclidean_last_injection_map R n k) p.
have hI:norm_bounded_linear NY NZ I.
  exists 1; split; first exact:ler01.
  move=>y; change (is_true (NZ (@euclidean_first_injection R n k y)<=1*NY y)).
  by rewrite /NZ /NY euclidean_first_injection_norm mul1r.
have hQ:norm_bounded_linear NX NZ Q:=norm_finite_linear_bounded hNX hNZ (@coordinate_basisP R m) Q.
have hFirst:=norm_class_zero_postcompose hNY hf hI.
have hQCont:=@norm_bounded_linear_continuous R (R_n R m) (R_n R (n+k)) NX NZ hNX hNZ Q hQ.
have hSecond:=@norm_continuous_whole_class_zero R (R_n R m) (R_n R (n+k)) NX NZ hNX hNZ Q hQCont.
exact (norm_class_zero_add hNZ hFirst hSecond).
Qed.
