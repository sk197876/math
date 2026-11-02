(** Federer (1969), 3.2.33, p. 270: on the
    zero scalar-derivative locus, the printed mu-Jacobian is
    exactly one, strengthening its sufficient lower bound. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  EuclideanBlockCoordinates EuclideanBlockLinearMaps EuclideanBlockNorms CoareaPerturbationBound
  EuclideanLinearJacobian EuclideanExteriorComposition ScalarCylinderMapUP ScalarCylinderJacobianLower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_cylinder_zero_jacobian]: the preserved
    coordinate directions give J_mu f>= 1 in Federer
    3.2.33, p. 270. When g'= 0 its differential is
    an orthogonal coordinate projection followed by an isometric
    coordinate inclusion, hence is nonexpanding and has J_mu= 1.
    This proves exact constant integrability on X without a
    separate assumption about measurability of a selected field. *)
Theorem scalar_cylinder_zero_jacobian (R:realType) mu k
    (L:Hom (R_n R ((mu+1)+k)) (R_n R (mu+1))):
  is_scalar_cylinder_map (fun _=>0) L ->euclidean_linear_jacobian mu L= 1.
Proof.
move=>hL.
have hVector x:inner_norm (@euclidean_inner_productP R (mu+1)) (L x)<=
    1*inner_norm (@euclidean_inner_productP R ((mu+1)+k)) x.
  pose P:=@euclidean_first_block R mu 1 (@euclidean_first_block R (mu+1) k x).
  have hValue:L x=@euclidean_first_injection R mu 1 P.
    apply/ffunP=>i; rewrite -(splitK i); case:(split i)=>a.
    - by rewrite (scalar_cylinder_first_coordinates hL) /euclidean_first_injection
        euclidean_block_join_left /P /euclidean_first_block !ffunE.
    - by rewrite (ord1 a) (scalar_cylinder_last_coordinate hL) /euclidean_first_injection
        euclidean_block_join_right ffunE.
  rewrite hValue euclidean_first_injection_norm mul1r.
  have h1:=(@coarea_block_projection_norms R mu 1 (@euclidean_first_block R (mu+1) k x)).1.
  have h2:=(@coarea_block_projection_norms R (mu+1) k x).1.
  exact:(le_trans h1 h2).
have hUpper:=euclidean_exterior_jacobian_vector_bound_power mu (@ler01 R) hVector.
rewrite expr1n in hUpper.
have hLower:1<=euclidean_linear_jacobian mu L.
  apply:(@scalar_cylinder_jacobian_lower_bound R mu k 0 L).
  constructor; first exact:(scalar_cylinder_first_coordinates hL).
  move=>x; change (L x (rshift mu ord0)=0*x (lshift k (rshift mu ord0))).
  by rewrite mul0r; exact:(scalar_cylinder_last_coordinate hL x).
by apply/eqP; rewrite eq_le hUpper hLower.
Qed.
