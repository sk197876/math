(** Federer (1969), 3.3.19, pp. 305–306: each
    original planar line projection has a local unit
    normal coordinate, with no global frame selection. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates OrthonormalFamilies CoordinateProjection InnerNorm InnerMetric
  EuclideanOneNormDifferential EuclideanProjectionSpace OrthogonalInjectionSpaces EuclideanRectangularAdjoint
  StructureProjectionDistance StructureProjectionKernel StructureProjectionCone StructureCone.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Normal.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation N:=(inner_norm (@euclidean_inner_productP R 2)).
Local Notation B:=(@euclidean_inner_product R 2).

(** Source for [is_planar_projection_unit_normal]: independent
    unit-normal and actual projection-norm laws for the
    line planes used in 3.3.19, pp. 305–306.
    Existence is proved separately from these equations. *)
Definition is_planar_projection_unit_normal (p:euclidean_projection_space R 2 1) (u:E):Prop:=
  N u= 1 /\forall v:E,inner_norm (@euclidean_inner_productP R 1)
    (euclidean_projection_linear p v)=`|B v u|.

(** Source for [planar_projection_unit_normal_exists]: every
    original orthogonal line projection has the stated
    actual unit normal, supporting 3.3.19, p. 305.
    Its adjoint on the scalar unit supplies a local
    existence witness, used only through these public laws. *)
Theorem planar_projection_unit_normal_exists (p:euclidean_projection_space R 2 1):
  exists u,is_planar_projection_unit_normal p u.
Proof.
pose e:= @coordinate_basis R 1 ord0.
pose u:= euclidean_rectangular_adjoint (orthogonal_projection_map p) e.
exists u;split.
- apply:inner_norm_value;first exact:ler01.
  rewrite /u expr1n structure_projection_adjoint_orthogonal euclidean_inner_basis.
  by rewrite /e /coordinate_basis ffunE eqxx.
- move=>v;rewrite euclidean_one_norm_coordinate.
  have hPair:B v u=(euclidean_projection_linear p v) ord0.
    by rewrite /u structure_projection_adjoint_pairing euclidean_inner_basis.
  by rewrite hPair.
Qed.

(** Source for [planar_projection_normal_coneE]: the original
    strict cone of 3.3.1, p. 287 expressed in the
    local normal coordinate used in 3.3.19, p. 305.
    No normal-distance premise is left unproved. *)
Lemma planar_projection_normal_coneE (p:euclidean_projection_space R 2 1) (u a x:E)
    (t: \bar R) (s:R):
  is_planar_projection_unit_normal p u ->0<s ->
  (structure_cone (structure_projection_kernel (leqnSn 1) p) a t s x <->
    `|B (x-a) u|<s* N (x-a) /\((N (x-a))%:E<t)%E).
Proof.
move=>hNormal hs;rewrite structure_projection_coneE hNormal.2.
have hInverse:0<s^-1 by rewrite invr_gt0.
have hSN:s!=0 by rewrite gt_eqF.
split.
- move=>[hAngle hRadius];split=>//.
  have h:s*(s^-1*`|B (x-a) u|)<s* N (x-a) by rewrite ltr_pM2l.
  by rewrite mulrA mulfV // mul1r in h.
- move=>[hAngle hRadius];split=>//.
  have h:s^-1*`|B (x-a) u|<s^-1*(s* N (x-a)) by rewrite ltr_pM2l.
  by rewrite mulrA mulVf // mul1r in h.
Qed.
End Normal.
