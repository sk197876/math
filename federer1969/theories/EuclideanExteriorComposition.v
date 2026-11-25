(** Federer (1969), 3.2.22, p. 259: supporting
    exterior Jacobian estimates for the two coordinate changes.
    All estimates use the abstract exterior operator-norm laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerExterior InnerExteriorPositivity ExteriorNorm ExteriorGrading ExteriorMaps ExteriorMapScaling
  ExteriorOperatorNorm OperatorNormUP OperatorNormLaws OperatorNorm EuclideanLinearMaps
  EuclideanLinearJacobian EuclideanHomOperator.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_exterior_jacobian_vector_bound]:
    supporting operator estimate behind Federer 3.2.22,
    p. 259, as specified in 1.7.6, pp. 33–34.
    The bound holds for every exterior vector, including
    nonsimple vectors and all natural degrees. *)
Lemma euclidean_exterior_jacobian_vector_bound (R:realType) m n q
    (L:Hom (R_n R m) (R_n R n)) (x:exterior_power (R_n R m) q):
  exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
    (exterior_power_map (hom_as_linear L) q x)<=
  euclidean_linear_jacobian q L*
    exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R m) x.
Proof.
exact:(operator_norm_vector_bound (exterior_operator_normP (euclidean_two_nonzero R)
  (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
  (@coordinate_basisP R m) (hom_as_linear L) q) x).
Qed.

(** Source for [euclidean_exterior_jacobian_compose_bound]:
    the exterior-norm inequalities in Federer 3.2.22,
    p. 259, follow from the norm bound for composition.
    The middle space and exterior degree are arbitrary. *)
Lemma euclidean_exterior_jacobian_compose_bound (R:realType) m n k q
    (A:Hom (R_n R m) (R_n R n)) (B:Hom (R_n R n) (R_n R k)):
  euclidean_linear_jacobian q (hom_comp B A)<=
    euclidean_linear_jacobian q B*euclidean_linear_jacobian q A.
Proof.
apply:(operator_norm_le_unit (exterior_operator_normP (euclidean_two_nonzero R)
  (@euclidean_inner_productP R m) (@euclidean_inner_productP R k)
  (@coordinate_basisP R m) (hom_as_linear (hom_comp B A)) q) _).2=>x hx.
have hComp:hom_as_linear (hom_comp B A)=1 linear_comp (hom_as_linear B) (hom_as_linear A).
  by move=>v.
rewrite (exterior_power_map_ext hComp x) -exterior_power_map_composition.
apply:(le_trans (euclidean_exterior_jacobian_vector_bound B _) _).
apply:(le_trans (ler_wpM2l (euclidean_linear_jacobian_nonnegative q B)
  (euclidean_exterior_jacobian_vector_bound A x)) _).
rewrite mulrA; apply:(le_trans (ler_wpM2l (mulr_ge0
  (euclidean_linear_jacobian_nonnegative q B) (euclidean_linear_jacobian_nonnegative q A)) hx) _).
by rewrite mulr1.
Qed.

(** Source for [euclidean_exterior_jacobian_vector_bound_power]:
    the powers lambda^mu in Federer 3.2.22, p. 259,
    follow from a vector bound by lambda and the exterior
    operator estimate of 1.7.6, p. 34. *)
Lemma euclidean_exterior_jacobian_vector_bound_power (R:realType) m n q
    (L:Hom (R_n R m) (R_n R n)) (C:R):
  0<=C ->
  (forall x,inner_norm (@euclidean_inner_productP R n) (L x)<=
    C*inner_norm (@euclidean_inner_productP R m) x) ->
  euclidean_linear_jacobian q L<=C^+q.
Proof.
move=>hC hBound.
have hN:euclidean_operator_norm L<=C.
  apply:(operator_norm_le_unit (linear_operator_normP (@euclidean_inner_productP R m)
    (@euclidean_inner_productP R n) (@coordinate_basisP R m) (hom_as_linear L)) C).2=>x hx.
  apply:(le_trans (hBound x) _); apply:(le_trans (ler_wpM2l hC hx) _); by rewrite mulr1.
apply:(le_trans (euclidean_linear_jacobian_bound q L) _).
have hNonneg:0<=euclidean_operator_norm L:=linear_operator_norm_nonnegative
  (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
  (@coordinate_basisP R m) (hom_as_linear L).
elim:q=>[|q ih]; first by rewrite !expr0.
rewrite !exprS; apply:(le_trans (ler_wpM2l hNonneg ih) _).
exact:(ler_wpM2r (exprn_ge0 q hC) hN).
Qed.
