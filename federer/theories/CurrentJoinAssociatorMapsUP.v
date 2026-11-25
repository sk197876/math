(** Federer (1969), 4.1.11, p. 366: independently
    specify the original barycentric map H and the
    two time-square maps f and g used in the
    associativity proof. No current identity is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanOneCoordinate
  EuclideanBlockCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_current_join_barycentre]: the printed
    H(x,y,z,w)=w_1 x+w_2 y+w_3 z,
    Federer 4.1.11, p. 366, on the original
    ordered four-factor Euclidean domain. *)
Definition is_current_join_barycentre (R:realType) n
    (H:R_n R (n+(n+(n+3)))%N->R_n R n):Prop:=
  forall (x y z:R_n R n) (w:R_n R 3%N),
    H (@euclidean_block_join R n (n+(n+3))%N
      (x,@euclidean_block_join R n (n+3)%N (y,@euclidean_block_join R n 3%N (z,w))))=
    w ord0*:x+w (lift ord0 ord0)*:y+w (lift ord0 (lift ord0 ord0))*:z.

(** Source for [is_current_join_left_triangle_map]: the
    printed f(t_1,t_2)=((1-t_1)(1-t_2),t_1(1-t_2),t_2),
    Federer 4.1.11, p. 366. The basis is the
    original standard basis of R^3. *)
Definition is_current_join_left_triangle_map (R:realType)
    (f:R_n R 2%N->R_n R 3%N):Prop:=
  forall t:R_n R 2%N,
    f t=((1-t ord0)*(1-t (lift ord0 ord0)))*:@coordinate_basis R 3%N ord0+
      (t ord0*(1-t (lift ord0 ord0)))*:@coordinate_basis R 3%N (lift ord0 ord0)+
      t (lift ord0 ord0)*:@coordinate_basis R 3%N (lift ord0 (lift ord0 ord0)).

(** Source for [is_current_join_right_triangle_map]: the
    printed g(t_1,t_2)=(1-t_1,t_1(1-t_2),t_1 t_2),
    Federer 4.1.11, p. 366. These original formulas
    do not postulate equality of the square images. *)
Definition is_current_join_right_triangle_map (R:realType)
    (g:R_n R 2%N->R_n R 3%N):Prop:=
  forall t:R_n R 2%N,
    g t=(1-t ord0)*:@coordinate_basis R 3%N ord0+
      (t ord0*(1-t (lift ord0 ord0)))*:@coordinate_basis R 3%N (lift ord0 ord0)+
      (t ord0*t (lift ord0 ord0))*:@coordinate_basis R 3%N (lift ord0 (lift ord0 ord0)).
