(** Federer (1969), 3.2.22, pp. 258–259:
    rank below mu forces the mu-dimensional ordinary and
    intrinsic partial exterior Jacobians to vanish. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanLinearMaps EuclideanLinearJacobian LinearRankAtLeast LinearRankExterior
  FiniteExteriorPowers ExteriorGrading ExteriorMaps ExteriorNorm ExteriorOperatorEstimate ExteriorOperatorNorm
  OperatorNormUP OperatorNormLaws EuclideanExteriorComposition PartialFunctionUP PartialExteriorNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_exterior_jacobian_rank_zero]: the
    vanishing exterior Jacobian after the rank conclusion of
    3.2.21 in Federer 3.2.22, p. 259.
    The rank/exterior-power equivalence from 3.1.18 gives
    the zero map; its abstract operator norm is zero. *)
Lemma euclidean_exterior_jacobian_rank_zero (R:realType) m n q
    (H:Hom (R_n R m) (R_n R n)):
  ~linear_rank_at_least H q ->euclidean_linear_jacobian q H=0.
Proof.
move=>hRank.
apply:(operator_norm_zero_iff (exterior_operator_normP (euclidean_two_nonzero R)
  (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
  (@coordinate_basisP R m) (hom_as_linear H) q)).2=>x.
apply/eqP; apply/negPn/negP=>hNonzero.
apply:hRank; apply:(linear_rank_exteriorP (euclidean_two_nonzero R) (@coordinate_basisP R m) H q).2.
by exists x.
Qed.

(** Source for [partial_exterior_low_rank_norm_zero]: the
    zero approximate Jacobian over the exceptional target Q
    in Federer 3.2.22, pp. 258–259.
    Every output of the actual partial graph lies in a
    linear image of rank below q, so every actual exterior
    output word is zero. No ambient extension of the partial
    graph or regularity of its source cone is required. *)
Lemma partial_exterior_low_rank_norm_zero (R:realType) m n k q
    (H:Hom (R_n R m) (R_n R k))
    (d:partial_function (R_n R n) (R_n R k)):
  ~linear_rank_at_least H q ->
  (forall v w,partial_function_graph d v w ->exists x,H x=w) ->
  is_partial_exterior_norm q d 0.
Proof.
move=>hRank hRange; constructor; first exact:lexx.
- move=>v w hVW hUnit.
  have hex i:=hRange _ _ (hVW i); have [x hx]:=choice hex.
  have hW:(fun i=>H (x i))=w by apply:funext=>i; exact:hx.
  rewrite -hW -exterior_map_indexed_product.
  have hBound:=@euclidean_exterior_jacobian_vector_bound R m k q H (e_lambda x (ord_tuple q)).
  by rewrite (euclidean_exterior_jacobian_rank_zero hRank) mul0r in hBound.
- by move=>J hJ _.
Qed.
