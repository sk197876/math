(** Federer (1969), 4.1.9, p. 363: the time
    velocity is the original differential evaluated
    in the direction (1,0). The existing sealed
    partial differential supplies the actual value. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanBlockLinearMaps
  CurrentMapDifferential CurrentHomotopyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_homotopy_time_velocity]: the original
    h-dot_t(x)=Dh(t,x)(1,0), Federer 4.1.9,
    p. 363. Its mathematical laws apply at every
    original domain point under positive class. The existing
    total representative outside that domain adds no derivative claim. *)
Definition current_homotopy_time_velocity (R:realType) n nu (A:set R)
    (U:set (R_n R n)) (h:R_n R (1+n)%N->R_n R nu) (t:R) (x:R_n R n):R_n R nu:=
  @current_map_differential R (1+n)%N nu (@current_homotopy_product_domain R n A U) h
    (@euclidean_block_join R 1%N n (@euclidean_one_embed R t,x))
    (@euclidean_first_injection_map R 1%N n (@euclidean_one_embed R 1)).
