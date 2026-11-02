(** Federer (1969), 3.2.22, p. 259: express
    the intrinsic partial exterior norm in orthonormal source
    coordinates before comparing almost-isometric chart bounds. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm OrthogonalMaps
  EuclideanLinearJacobian PartialFunctionUP PartialExteriorNormUP
  InjectiveOrthogonalCoordinates PartialExteriorIsometricChart.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [partial_exterior_chart_coordinates_exists]:
    supporting comparison of ap J_mu f and J_mu(F composed
    with psi) in Federer 3.2.22, p. 259.
    Factor the injective chart differential as O composed K;
    in the isometric coordinates O the actual partial map is
    L=H composed inverse K. Its intrinsic norm is exactly
    J_q L, in every degree. All coordinate objects are local
    existence witnesses, with both inverse laws proved. *)
Lemma partial_exterior_chart_coordinates_exists (R:realType) m n k q
    (D:Hom (R_n R m) (R_n R n)) (H:Hom (R_n R m) (R_n R k))
    (d:partial_function (R_n R n) (R_n R k)):
  injective D ->
  (forall v w,partial_function_graph d v w <->exists x,D x=v /\ H x=w) ->
  exists (L:Hom (R_n R m) (R_n R k)) (K Ki:Hom (R_n R m) (R_n R m)),
    is_partial_exterior_norm q d (euclidean_linear_jacobian q L) /\
    (forall x,L (K x)=H x) /\
    (forall x,inner_norm (@euclidean_inner_productP R m) (K x)=
      inner_norm (@euclidean_inner_productP R n) (D x)) /\
    cancel K Ki /\ cancel Ki K.
Proof.
move=>hD hGraph.
have [O [K [Ki [hO [hDK [hLeft hRight]]]]]]:=injective_orthogonal_coordinates_exists hD.
pose L:=hom_comp H Ki.
have hLK x:L (K x)=H x by rewrite /L hom_compE hLeft.
have hGraphO v w:partial_function_graph d v w <->exists y,O y=v /\ L y=w.
  split.
  - move=>/(hGraph v w) [x [hDx hHx]]; exists (K x); split.
    + by rewrite hDK.
    + by rewrite hLK.
  - move=>[y [hOy hLy]]; apply:(hGraph v w).2; exists (Ki y); split.
    + by rewrite -(hDK (Ki y)) hRight.
    + exact hLy.
exists L,K,Ki; split.
- exact:(@partial_exterior_isometric_chart_norm R m n k q O L d hO hGraphO).
- split; first exact hLK; split; last by split.
  move=>x; rewrite -(hDK x).
  symmetry; exact:(orthogonal_map_norm (@euclidean_inner_productP R m)
    (@euclidean_inner_productP R n) hO (K x)).
Qed.
