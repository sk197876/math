(** Federer (1969), 4.1.7, p. 359:
    the original inclusion of the positive
    half-line into the whole line is
    smooth. This is the bounded linear
    map assertion of 3.1.11, p. 221,
    restricted to the original open domain. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import TensorUP Hom RealNormUP NormDifferentialUP NormRegularity NormRegularityOperations
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct HalflineCurrents.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [halfline_inclusion_smooth]: the
    actual inclusion used in the example
    is of every finite class on
    U=(0,infinity), Federer 4.1.7, p. 359.
    Smoothness supplies no support-properness conclusion. *)
Theorem halfline_inclusion_smooth (R:realType):
  norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R 1))
    (inner_norm_real_norm (@euclidean_inner_productP R 1)) (@current_halfline_domain R) id.
Proof.
move=>k.
pose X:=R_n R 1.
pose NX:=inner_norm (@euclidean_inner_productP R 1).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R 1).
have hBound:norm_bounded_linear NX NX (hom_of_linear (linear_id X)).
  exists 1;split;first exact:ler01.
  by move=>x;rewrite hom_of_linearE mul1r.
exact:(@norm_class_linear R X X NX NX hNX hNX (@current_halfline_domain R)
  (hom_of_linear (linear_id X)) k (@current_halfline_domain_open R) hBound).
Qed.
