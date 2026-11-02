(** Federer (1969), 3.2.34, p. 271: a
    differential of norm at most one attaining a unit
    slope has degree-one Jacobian exactly one. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  EuclideanLinearJacobian EuclideanExteriorComposition ExteriorPowers ExteriorDegreeOneNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_unit_direction_jacobian]: the
    equality J_1 f(x)=1 in Federer 3.2.34,
    p. 271. The actual vector bound gives the
    exterior upper bound one; evaluation of the actual
    degree-one exterior map on the given nonzero vector
    gives the reverse inequality. This supporting statement
    allows any finite Euclidean target and selects no basis
    or differential witness. *)
Lemma euclidean_unit_direction_jacobian (R:realType) m n
    (L:Hom (R_n R m) (R_n R n)) w:
  (forall x,inner_norm (@euclidean_inner_productP R n) (L x)<=
    inner_norm (@euclidean_inner_productP R m) x) ->
  0<inner_norm (@euclidean_inner_productP R m) w ->
  inner_norm (@euclidean_inner_productP R n) (L w)=
    inner_norm (@euclidean_inner_productP R m) w ->
  euclidean_linear_jacobian 1 L= 1.
Proof.
move=>hBound hw hAttain.
have hUnitBound x:inner_norm (@euclidean_inner_productP R n) (L x)<=
    1*inner_norm (@euclidean_inner_productP R m) x by rewrite mul1r; exact:hBound.
have hUpper:=@euclidean_exterior_jacobian_vector_bound_power R m n 1%N L 1 ler01 hUnitBound.
rewrite expr1 in hUpper.
have hLower:=@euclidean_exterior_jacobian_vector_bound R m n 1%N L
  (exterior_first_inclusion (R_n R m) w).
rewrite exterior_map_first_inclusion !exterior_first_norm hAttain in hLower.
have hAtLeast:1<=euclidean_linear_jacobian 1 L.
  by move:hLower; rewrite -{1}(mul1r (inner_norm (@euclidean_inner_productP R m) w)) ler_pM2r.
by apply/eqP; rewrite eq_le hUpper hAtLeast.
Qed.
