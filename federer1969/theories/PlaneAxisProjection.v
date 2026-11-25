(** Federer (1969), 3.2.7, p. 246, second
    example: the linear map (x_1,x_2) to (x_1,0).
    Reuse the existing first-coordinate inclusion and
    projection; prove its unit Lipschitz bound and
    vanishing two-dimensional Jacobian. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanCoordinateMetric HilbertFormCompactness RealNormUP NormDifferentialUP NormDifferentialLinear
  EuclideanLinearJacobian Jacobian LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [plane_axis_projection]: the explicit
    map f(x)=(x_1,0) in the second example
    of Federer 3.2.7, p. 246, expressed
    through the existing coordinate maps. *)
Definition plane_axis_projection (R:realType):Hom (R_n R 2) (R_n R 2).
Proof.
apply:(@HomMap R (R_n R 2) (R_n R 2)
  (fun x=>@coordinate_head_inclusion R 1 (@coordinate_head R 1 x))).
apply/asboolP=>a x y; by rewrite !linearD !linearZ.
Defined.

(** Source for [plane_axis_projection_value]: supporting
    first-axis formula for Federer 3.2.7, p. 246.
    The first coordinate is retained and the other is zero. *)
Lemma plane_axis_projection_value (R:realType) (x:R_n R 2):
  @plane_axis_projection R x=x ord0*:(@coordinate_basis R 2 ord0).
Proof.
apply/ffunP=>i.
rewrite /plane_axis_projection /= /coordinate_head_inclusion /coordinate_head /coordinate_basis !ffunE.
change ((if i==ord0 then x ord0 else 0)=x ord0*(if i==ord0 then 1 else 0)).
by case:ifP=>_; rewrite ?mulr1 ?mulr0.

Qed.

(** Source for [plane_axis_projection_head]: the
    first coordinate of f(x), as printed in the
    second example of Federer 3.2.7, p. 246. *)
Lemma plane_axis_projection_head (R:realType) (x:R_n R 2):
  (@plane_axis_projection R x) ord0=x ord0.
Proof. by change (@coordinate_head R 1 (@coordinate_head_inclusion R 1 (@coordinate_head R 1 x))=x ord0); rewrite coordinate_headK. Qed.

(** Source for [plane_axis_projection_norm_bound]: the
    unit Lipschitz bound for the second example of
    Federer 3.2.7, p. 246, from the
    existing coordinate projection norm bound. *)
Lemma plane_axis_projection_norm_bound (R:realType) (x:R_n R 2):
  inner_norm (@euclidean_inner_productP R 2) (@plane_axis_projection R x)<=
    inner_norm (@euclidean_inner_productP R 2) x.
Proof.
rewrite plane_axis_projection_value inner_normZ euclidean_coordinate_unit_norm mulr1.
exact:euclidean_coordinate_norm_bound.
Qed.

(** Source for [plane_axis_projection_lipschitz]: the
    global Lipschitz hypothesis for the second example
    in Federer 3.2.7, p. 246. *)
Lemma plane_axis_projection_lipschitz (R:realType):
  is_metric_lipschitz setT
    (@plane_axis_projection R:inner_metric_space (@euclidean_inner_productP R 2)->
      inner_metric_space (@euclidean_inner_productP R 2)).
Proof.
exists 1; split; first exact:ltr01; split; first exact:ler01.
move=>x y _ _; rewrite !inner_metric_distanceE mul1r -linearB.
exact:plane_axis_projection_norm_bound.
Qed.

(** Source for [plane_axis_projection_differential]: the
    actual constant differential of the linear map in
    the second example of Federer 3.2.7, p. 246. *)
Lemma plane_axis_projection_differential (R:realType) (a:R_n R 2):
  has_norm_differential (inner_norm (@euclidean_inner_productP R 2))
    (inner_norm (@euclidean_inner_productP R 2)) (fun _=>True)
    (@plane_axis_projection R) a (@plane_axis_projection R).
Proof.
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R 2).
apply:(norm_differential_linear hN hN).
- exists 1; split; first exact:ltr01; by move=>h _.
- exists 1; split; first exact:ler01.
  move=>v; rewrite mul1r; exact:plane_axis_projection_norm_bound.
Qed.

(** Source for [plane_axis_projection_jacobian_zero]: the
    two-dimensional Jacobian vanishes everywhere in the
    second example of Federer 3.2.7, p. 246.
    The second basis vector is an actual nonzero kernel vector. *)
Lemma plane_axis_projection_jacobian_zero (R:realType):
  euclidean_linear_jacobian 2 (@plane_axis_projection R)= 0.
Proof.
pose L:=@plane_axis_projection R; pose i:'I_2:=lift ord0 ord0.
pose e:=@coordinate_basis R 2 i.
have he:L e=L 0.
  rewrite /L plane_axis_projection_value linear0 /e /coordinate_basis ffunE eq_sym lift_eqF scale0r.
  exact:erefl.
have hNot:~injective L.
  move=>hInj; have hz:e= 0:=hInj e 0 he.
  have hx:=congr1 (fun v:R_n R 2=>v i) hz.
  rewrite /e /coordinate_basis !ffunE eqxx in hx.
  have hOne:(1:R)=0:=hx.
  by have hNZ:=@oner_neq0 R; rewrite hOne eqxx in hNZ.
have hLe:euclidean_linear_jacobian 2 L<= 0.
  rewrite leNgt; apply/negP=>hp; apply:hNot.
  exact ((euclidean_linear_jacobian_top_positive L).1 hp).
apply/eqP; by rewrite eq_le hLe (euclidean_linear_jacobian_nonnegative 2 L).
Qed.
