(** Federer (1969), 3.4.4, p. 318: independent
    laws of the printed coordinatewise map and original source set. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerMetric EuclideanOneCoordinate RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_critical_sharp_product_map]: the displayed
    coordinates y_i=x_i for i<=nu and y_i=g(x_i)
    otherwise, 3.4.4, p. 318. Zero-based
    coordinates express the same original two blocks.
    Regularity, differential, rank, and image are consequences. *)
Definition is_critical_sharp_product_map (R:realType) m nu
    (g:inner_metric_space (@euclidean_inner_productP R 1)->R^o)
    (F:R_n R m->R_n R m):Prop:=
  forall x i,F x i=if (i<nu)%N then x i else g (euclidean_one_embed (x i)).

(** Source for [critical_sharp_product_source]: the actual
    B consisting of all points whose last m-nu coordinates
    belong to A(alpha,n), 3.4.4, p. 318.
    No source or image property is put into this definition. *)
Definition critical_sharp_product_source (R:realType) m nu
    (A:set (real_line_metric R)):set (R_n R m):=
  fun x=>forall i:'I_m,(nu<=i)%N ->A (x i).
