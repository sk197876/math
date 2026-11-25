(** Federer (1969), 3.1.23, pp. 236–237: a
    supported ambient diffeomorphism straightens a submanifold to
    its affine tangent plane, with prescribed Lipschitz control. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  EuclideanSubmanifoldUP SubmanifoldChartsUP SubmanifoldStraighteningCoordinates
  SubmanifoldCoordinateParametrisation SubmanifoldParametrisationGraph
  SupportedStraighteningUP ControlledGraphStraightening.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_3_1_23]: the full theorem of
    Federer 3.1.23, p. 236, proved on pp. 236–237.
    Every sufficiently small positive radius has a global
    class-k diffeomorphism and inverse with Lipschitz constants
    at most 1/t, identity outside the radius-r ball,
    and the printed exact equality inside the radius-tr ball.
    The target is the actual affine tangent plane; dimension
    zero and arbitrary centres are included. *)
Theorem federer_3_1_23 (R:realType) n mu k
    (B:set (R_n R n)) b t :
  (1<=k)%N -> @is_euclidean_submanifold R n mu k B -> B b -> 0<t<1 ->
  exists rho:R,0<rho /\ forall r:R,0<r -> r<rho -> exists F g,
    is_controlled_tangent_straightening
      (inner_norm_real_norm (@euclidean_inner_productP R n)) B b t r F g k.
Proof.
move=>hk hB hb ht.
have hCharts:=open_parametrisations_orthogonal_graphs hk
  (convex_coordinates_open_parametrisations hk (submanifold_convex_coordinates hB)).
have [T [p [j [psi [hTb [hj [hp [hinj [him [hconv [hpsi [hrange [hcan [hinv hD]]]]]]]]]]]]]]:=
  hCharts b hb.
exact (@controlled_graph_straightening R n mu k B T b t p j psi hk hb ht hTb hj hp
  hpsi hrange hcan (fun x hx ht=>hinv x (conj hx ht)) hD).
Qed.
