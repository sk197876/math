(** Federer (1969), 4.1.27, p. 384: the
    original prefix-product map from the open
    unit cube to the ordered simplex. State
    its exact coordinate formula independently of
    an existence witness. Smoothness, image geometry,
    injectivity, Jacobian and current identities remain
    separate laws to prove. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading FiniteExteriorPowers EuclideanOpenUnitCube.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [simplex_cube_prefix_product]: the product
    x_1 ... x_k in the definition of
    f in 4.1.27, p. 384. The
    empty initial product is one. This
    abbreviates existing finite multiplication. *)
Definition simplex_cube_prefix_product (R:realType) m (x:R_n R m) k:R:=
  \prod_(i:'I_m | (i<k)%N) x i.

(** Source for [simplex_consecutive_edge_family]: the original
    consecutive edges u_i-u_(i-1) in 4.1.27,
    p. 384. Zero-based source index i
    corresponds to the book's edge i+1. *)
Definition simplex_consecutive_edge_family (R:realType) n m
    (v:'I_(m.+1)->R_n R n):'I_m->R_n R n:=
  fun i=>v (lift ord0 i)-v (widen_ord (leqnSn m) i).

(** Source for [simplex_consecutive_orientation]: the original
    m-vector zeta in 4.1.27, p. 384,
    is the exterior product of consecutive
    edges. Dependent families and m=0 retain
    the original exterior-product conventions. *)
Definition simplex_consecutive_orientation (R:realType) n m
    (v:'I_(m.+1)->R_n R n):exterior_power (R_n R n) m:=
  e_lambda (simplex_consecutive_edge_family v) (ord_tuple m).

(** Source for [is_simplex_cube_parametrisation]: the displayed
    f(x)=u_0+sum_i(x_1 ... x_i)(u_i-u_(i-1))
    in 4.1.27, p. 384. This pointwise
    law specifies the map before its
    existence or analytic properties are proved. *)
Definition is_simplex_cube_parametrisation (R:realType) n m
    (v:'I_(m.+1)->R_n R n) (f:R_n R m->R_n R n):Prop:=
  forall x,f x=v ord0+\sum_(i:'I_m)
    (simplex_cube_prefix_product x (val i).+1)*:simplex_consecutive_edge_family v i.

(** Source for [simplex_cube_parametrisation_unique]: the original
    coordinate formula determines a unique actual
    map, supporting 4.1.27, p. 384. *)
Theorem simplex_cube_parametrisation_unique (R:realType) n m
    (v:'I_(m.+1)->R_n R n) (f g:R_n R m->R_n R n):
  is_simplex_cube_parametrisation v f->
  is_simplex_cube_parametrisation v g->f=g.
Proof.
move=>hF hG;apply:funext=>x;by rewrite hF hG.
Qed.

(** Source for [simplex_positive_barycentric_image]: the original
    image displayed in 4.1.27, p. 384:
    positive coefficients of every vertex with
    total coefficient one. The source permits
    repeated or affinely dependent vertices. *)
Definition simplex_positive_barycentric_image (R:realType) n m
    (v:'I_(m.+1)->R_n R n):set (R_n R n):=
  [set y|exists t:'I_(m.+1)->R,
    (forall i,0<t i) /\(\sum_i t i)= 1 /\y=\sum_i t i*:v i].

(** Source for [simplex_cube_jacobian_weight]: the printed
    product x_1^(m-1) ... x_(m-1) in the
    wedge differential formula of 4.1.27,
    p. 384. The last coordinate has
    exponent zero, so this finite-product abbreviation
    includes the original empty products at m=0,1. *)
Definition simplex_cube_jacobian_weight (R:realType) m (x:R_n R m):R:=
  \prod_(i:'I_m) (x i)^+(m-(val i).+1).
