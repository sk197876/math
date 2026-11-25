(** Federer (1969), 3.3.4, p. 289: the original
    one-coordinate cones I_j and their two union
    inclusions around A intersect X. All frames,
    projections and enlarged apertures are local arguments. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  OrthogonalMaps EuclideanBlockLinearMaps EuclideanProjectionSpace
  StructureCone StructureProjectionKernel StructureBlockCone
  StructureCoordinateConeComparison StructureApertureEnlargement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_coordinate_cone]: the literal
    I_j(r,g,t) defined in Federer 3.3.4,
    p. 289. The orthogonal map f expresses
    coordinates in the actual moving frame; its
    first block has m coordinates and j indexes
    the complementary block of k coordinates. *)
Definition structure_coordinate_cone (R:realType) m k
    (A:set (inner_metric_space (@euclidean_inner_productP R (m+k))))
    (a:inner_metric_space (@euclidean_inner_productP R (m+k)))
    (f:{linear R_n R (m+k)->R_n R (m+k)}) (j:'I_k) (r: \bar R) (s:R):=
  [set x:inner_metric_space (@euclidean_inner_productP R (m+k))|
    A x /\ ((inner_norm (@euclidean_inner_productP R (m+k)) (x-a))%:E<r)%E /\
    ((s^-1)^+2-1)*
      (inner_norm (@euclidean_inner_productP R m) (@euclidean_first_block R m k (f (x-a))))^+2<
      ((@euclidean_last_block R m k (f (x-a))) j)^+2].

(** Source for [structure_frame_cone_union_squeeze]: both
    displayed cone inclusions of Federer 3.3.4,
    p. 289, for actual original sets. The enlarged
    aperture satisfies its prior independent equation;
    actual existence was proved separately. *)
Theorem structure_frame_cone_union_squeeze (R:realType) m k
    (hmn:(m<=m+k)%N)
    (A:set (inner_metric_space (@euclidean_inner_productP R (m+k)))) a
    (f:{linear R_n R (m+k)->R_n R (m+k)})
    (p:euclidean_projection_space R (m+k) m) (r: \bar R) (s u:R):
  is_orthogonal_map (@euclidean_inner_product R (m+k))
    (@euclidean_inner_product R (m+k)) f ->
  (forall y,euclidean_projection_linear p y=@euclidean_first_block R m k (f y)) ->
  (0<k)%N ->0<s<1 ->is_structure_enlarged_aperture k s u ->
  (\bigcup_j structure_coordinate_cone A a f j r s) `<=`
    A `&` structure_cone (structure_projection_kernel hmn p) a r s /\
  A `&` structure_cone (structure_projection_kernel hmn p) a r s `<=`
    (\bigcup_j structure_coordinate_cone A a f j r u).
Proof.
move=>hF hP hk /andP [hs hs1] hU.
have hu:0<u:=(andP hU.1).1.
have hCoefficient:(k%:R:R)*((u^-1)^+2-1)=((s^-1)^+2-1).
  rewrite (structure_enlarged_aperture_inverse_equation hk hs hU) mulrC divfK //.
  by rewrite pnatr_eq0 -lt0n.
split=>x.
- move=>[j _ [hA [hRadius hAngle]]]; split=>//.
  apply/(@structure_frame_cone_square_equation R m k hmn f p a x r s hF hP hs).
  split=>//; apply:structure_coordinate_cone_lower.
  by exists j.
- move=>[hA hCone].
  have [hAngle hRadius]:=(@structure_frame_cone_square_equation R m k hmn f p a x r s hF hP hs).1 hCone.
  have [j hj]:=structure_coordinate_cone_upper hCoefficient hAngle.
  exists j=>//; by split=>//; split.
Qed.
