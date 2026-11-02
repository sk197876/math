(** Federer (1969), 3.2.38, p. 274: each side-vr bad cube
    is divided into v^m side-r cubes with the same closed union. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanCoordinateCubeUP EqualCoordinateCubeGridUP EqualCoordinateCubeGridLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [coordinate_cube_subdivision_exists]: the construction
    of H from F minus G in Federer 3.2.38, p. 274. Independent
    grid laws prove that v^m closed children have side r and their
    exact union is the original side-vr cube, including boundaries,
    v=1 and the zero-dimensional single atom. No subdivision
    covering or volume identity is taken as an additional premise. *)
Lemma coordinate_cube_subdivision_exists (R:realType) m v (a:R_n R m) (r:R)
    (Q:set (inner_metric_space (@euclidean_inner_productP R m))):
  (0<v)%N ->0<=r ->is_euclidean_coordinate_cube a (v%:R*r) Q ->
  exists P,is_equal_coordinate_cube_grid v a r P /\Q=\bigcup_s P s.
Proof.
move=>hv hr hQ; have [P hP]:=equal_coordinate_cube_grid_exists a hv hr.
exists P; split=>//; apply/seteqP; split=>x.
- move=>hx; have hBox:forall i,a i<=x i<=a i+v%:R*r:=(hQ.2 x).1 hx.
  have [s hs]:=equal_coordinate_grid_covers_box hP hBox; by exists s.
- move=>[s _ hs]; apply:(hQ.2 x).2.
  exact:(@equal_coordinate_grid_within_box R m v a r P hP s x hs).
Qed.
