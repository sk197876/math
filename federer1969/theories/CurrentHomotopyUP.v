(** Federer (1969), 4.1.9, p. 363: the original homotopy
    on an open real interval containing zero and one. The
    existing block coordinates of 2.6.5, p. 120, identify
    the original time-space product with R^(1+n).
    Domain, image and endpoint laws are independent of regularity. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import RealNormUP NormDifferentialUP NormRegularity RealMetricBackground
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanCartesianMap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_homotopy_parameter_interval]: the original
    A is an open subinterval of R and contains zero and
    one, Federer 4.1.9, p. 363. The independent laws
    permit bounded and unbounded intervals, including all R. *)
Record is_homotopy_parameter_interval (R:realType) (A:set R):Prop:={
  (** Source for [homotopy_parameter_open]: openness of the
      original real time interval, Federer 4.1.9, p. 363. *)
  homotopy_parameter_open:@open (real_line_metric R) A;
  (** Source for [homotopy_parameter_between]: the original
      interval contains every intermediate real point,
      supporting Federer 4.1.9, p. 363. *)
  homotopy_parameter_between:forall s t u:R,
    A s -> A t -> s<=u<=t -> A u;
  (** Source for [homotopy_parameter_zero]: zero belongs
      to the original A, Federer 4.1.9, p. 363. *)
  homotopy_parameter_zero:A 0;
  (** Source for [homotopy_parameter_one]: one belongs
      to the original A, Federer 4.1.9, p. 363. *)
  homotopy_parameter_one:A 1
}.

(** Source for [current_homotopy_time_domain]: the original
    real interval in the existing R=R^1 coordinate
    identification, supporting Federer 4.1.9, p. 363,
    by 2.6.5, pp. 119–120. *)
Definition current_homotopy_time_domain (R:realType) (A:set R):set (R_n R 1%N):=
  fun x=>A (@euclidean_one_project R x).

(** Source for [current_homotopy_product_domain]: the original
    A times U in the existing Euclidean block
    coordinates, supporting Federer 4.1.9, p. 363. *)
Definition current_homotopy_product_domain (R:realType) n (A:set R) (U:set (R_n R n)):
    set (R_n R (1+n)%N):=
  @euclidean_cartesian_set R 1%N n (@current_homotopy_time_domain R A) U.

(** Source for [current_homotopy_slice_map]: the original
    h_t(x)=h(t,x), Federer 4.1.9, p. 363. The
    given map h is retained through the original block identification. *)
Definition current_homotopy_slice_map (R:realType) n nu
    (h:R_n R (1+n)%N->R_n R nu) (t:R) (x:R_n R n):R_n R nu:=
  h (@euclidean_block_join R 1%N n (@euclidean_one_embed R t,x)).

(** Source for [is_current_homotopy_geometry]: the original
    open source and target, time interval, image and
    endpoint conditions for a homotopy from f to g,
    Federer 4.1.9, p. 363. Regularity is specified
    separately, and no homotopy existence is assumed. *)
Record is_current_homotopy_geometry (R:realType) n nu (A:set R)
    (U:set (R_n R n)) (V:set (R_n R nu))
    (f g:R_n R n->R_n R nu) (h:R_n R (1+n)%N->R_n R nu):Prop:={
  (** Source for [current_homotopy_parameter_interval]: the
      original open interval contains zero and one,
      Federer 4.1.9, p. 363. *)
  current_homotopy_parameter_interval:@is_homotopy_parameter_interval R A;
  (** Source for [current_homotopy_source_open]: the original
      U is open, Federer 4.1.9, p. 363. *)
  current_homotopy_source_open:forall x,U x->norm_domain_interior
    (inner_norm (@euclidean_inner_productP R n)) U x;
  (** Source for [current_homotopy_target_open]: the original
      V is open, Federer 4.1.9, p. 363. *)
  current_homotopy_target_open:forall y,V y->norm_domain_interior
    (inner_norm (@euclidean_inner_productP R nu)) V y;
  (** Source for [current_homotopy_image]: the original
      h maps A times U into V, Federer 4.1.9, p. 363. *)
  current_homotopy_image:forall z,@current_homotopy_product_domain R n A U z->V (h z);
  (** Source for [current_homotopy_start]: the original
      h(0,x)=f(x) for every x in U, Federer 4.1.9, p. 363. *)
  current_homotopy_start:forall x,U x->@current_homotopy_slice_map R n nu h 0 x = f x;
  (** Source for [current_homotopy_end]: the original
      h(1,x)=g(x) for every x in U, Federer 4.1.9, p. 363. *)
  current_homotopy_end:forall x,U x->@current_homotopy_slice_map R n nu h 1 x = g x
}.

(** Source for [is_current_homotopy_class]: the original
    homotopy of finite class r from f to g,
    Federer 4.1.9, p. 363, using the actual
    class-r predicate of 3.1.11, p. 220. *)
Definition is_current_homotopy_class (R:realType) n nu (A:set R)
    (U:set (R_n R n)) (V:set (R_n R nu))
    (f g:R_n R n->R_n R nu) (h:R_n R (1+n)%N->R_n R nu) r:Prop:=
  @is_current_homotopy_geometry R n nu A U V f g h /\
  @norm_class R (R_n R (1+n)%N) (R_n R nu)
    (inner_norm (@euclidean_inner_productP R (1+n)%N))
    (inner_norm (@euclidean_inner_productP R nu))
    (inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N))
    (inner_norm_real_norm (@euclidean_inner_productP R nu))
    (@current_homotopy_product_domain R n A U) h r.

(** Source for [is_smooth_current_homotopy]: the original
    class-infinity homotopy used for the deformation chain,
    Federer 4.1.9, p. 363. It has every original
    finite class on the same original product domain. *)
Definition is_smooth_current_homotopy (R:realType) n nu (A:set R)
    (U:set (R_n R n)) (V:set (R_n R nu))
    (f g:R_n R n->R_n R nu) (h:R_n R (1+n)%N->R_n R nu):Prop:=
  @is_current_homotopy_geometry R n nu A U V f g h /\
  @norm_class_all_orders R (R_n R (1+n)%N) (R_n R nu)
    (inner_norm (@euclidean_inner_productP R (1+n)%N))
    (inner_norm (@euclidean_inner_productP R nu))
    (inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N))
    (inner_norm_real_norm (@euclidean_inner_productP R nu))
    (@current_homotopy_product_domain R n A U) h.
