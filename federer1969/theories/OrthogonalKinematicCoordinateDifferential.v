(** Federer (1969), 3.2.48, p. 285: the original polynomial
    differential in actual isometric ambient coordinates. Public source
    and target chart laws suffice; no extension, derivative field or
    global Lipschitz property of the ambient polynomial is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  EuclideanHomInnerCharts OrthogonalMaps ProductInner FiniteInnerChartUP NormDifferentialUP
  OrthogonalKinematicMap OrthogonalKinematicDifferential FiniteInnerDifferentialChart.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [orthogonal_kinematic_coordinate_differential]: the
    source and target isometries conjugate D Psi, in the diagram of
    3.2.48, p. 285. This is the actual polynomial differential. *)
Definition orthogonal_kinematic_coordinate_differential (R:realType) N n k
    (e:Hom (R_n R n) [the lmodType R of
      ((Hom (R_n R N) (R_n R N))*(Hom (R_n R N) (R_n R N)))%type])
    (t:Hom (Hom (R_n R N) (R_n R N)) (R_n R k)) (z:R_n R n):=
  hom_comp t (hom_comp (orthogonal_kinematic_differential (e z).1 (e z).2) e).

(** Source for [orthogonal_kinematic_coordinate_differential_actual]:
    the actual coordinate differential in 3.2.48, p. 285, from
    the proved full ambient polynomial differential and the chain rule
    3.1.1(2), p. 210. All coordinate differential obligations are derived. *)
Theorem orthogonal_kinematic_coordinate_differential_actual (R:realType) N n k
    (e:Hom (R_n R n) [the lmodType R of
      ((Hom (R_n R N) (R_n R N))*(Hom (R_n R N) (R_n R N)))%type])
    (p:Hom [the lmodType R of
      ((Hom (R_n R N) (R_n R N))*(Hom (R_n R N) (R_n R N)))%type] (R_n R n))
    (t:Hom (Hom (R_n R N) (R_n R N)) (R_n R k)):
  is_finite_inner_chart (product_inner (@euclidean_hom_inner_productP R N N)
    (@euclidean_hom_inner_productP R N N)) e p ->
  is_orthogonal_map (@euclidean_hom_inner_product R N N)
    (@euclidean_inner_product R k) (hom_as_linear t) ->forall z,
  has_norm_differential (inner_norm (@euclidean_inner_productP R n))
    (inner_norm (@euclidean_inner_productP R k)) (fun _=>True)
    (fun u=>t (orthogonal_kinematic_map (e u))) z
    (orthogonal_kinematic_coordinate_differential e t z).
Proof.
move=>hChart ht z.
have hRaw:=orthogonal_kinematic_differential_actual (e z).1 (e z).2.
have hPoint:((e z).1,(e z).2)=e z:=esym (surjective_pairing (e z)).
rewrite hPoint in hRaw.
have hD:=@finite_inner_differential_chart R [the lmodType R of
  ((Hom (R_n R N) (R_n R N))*(Hom (R_n R N) (R_n R N)))%type]
  (Hom (R_n R N) (R_n R N)) _ _
  (product_inner_productP (@euclidean_hom_inner_productP R N N) (@euclidean_hom_inner_productP R N N))
  (@euclidean_hom_inner_productP R N N) n k e p t (@orthogonal_kinematic_map R N) (e z)
  (orthogonal_kinematic_differential (e z).1 (e z).2) hChart ht
  hRaw.
by rewrite (finite_inner_chart_left_inverse hChart) in hD.
Qed.
