(** Federer (1969), 4.1.13, pp. 369–370: the inclusion
    of an open support neighbourhood is smooth, by the
    bounded linear calculus of 3.1.11, p. 220. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity
  NormRegularityOperations InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [current_open_identity_smooth]: the original
    source inclusion in the proof of Federer 4.1.13,
    pp. 369–370, is smooth on every open domain,
    including empty and zero-dimensional domains. *)
Theorem current_open_identity_smooth (R:realType) n (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x):
  norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) U (fun x=>x).
Proof.
pose X:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose Id:=hom_of_linear (@TensorUP.linear_id R X).
have hBound:norm_bounded_linear NX NX Id.
  exists 1;split;first exact:ler01.
  by move=>x;rewrite /Id hom_of_linearE /= mul1r.
move=>k.
exact:(@norm_class_linear R X X NX NX hNX hNX U Id k hU hBound).
Qed.
