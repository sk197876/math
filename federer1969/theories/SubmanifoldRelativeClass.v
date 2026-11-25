(** Federer (1969), 3.1.22, p. 236, last paragraph:
    relative class k on a submanifold is equivalent to class k
    in every coordinate system. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  RealNormUP NormRegularity NormCoordinateSystemUP RelativeClassUP RelativeCoordinateClass
  EuclideanSubmanifoldUP SubmanifoldCoordinateSystems.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [submanifold_relative_class_coordinates]: the full
    last assertion of Federer 3.1.22, p. 236. The
    forward direction applies to every actual coordinate system;
    the reverse uses the proved chart at each point and
    extends the coordinate representative by composition with phi.
    Class zero and empty submanifolds are included. *)
Theorem submanifold_relative_class_coordinates (R:realType) n mu k (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (A B:set (R_n R n)) (f:R_n R n->Y) :
  @is_euclidean_submanifold R n mu k B -> B `<=` A ->
  (@norm_class_relative R (R_n R n) Y (inner_norm (@euclidean_inner_productP R n)) NY
    (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY A B f k <->
  forall T V phi psi,is_norm_coordinate_system
    (inner_norm_real_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R mu)) B T V phi psi k ->
    norm_class (inner_norm_real_norm (@euclidean_inner_productP R mu)) hNY V
      (fun u=>f (psi u)) k).
Proof.
move=>hB hBA; split.
- move=>hf T V phi psi hc; exact (relative_class_in_coordinates hc hf).
- move=>hall a ha.
  have [T [V [phi [psi [hat hc]]]]]:=submanifold_coordinate_system_exists hB ha.
  have [g [hg hag]]:=coordinate_class_relative_local_extension hc hBA (hall T V phi psi hc).
  exists T,g; by split=>//; split.
Qed.
