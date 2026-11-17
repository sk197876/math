(** Federer (1969), 3.4.8(8), p. 329:
    adjacent original prefix projections compose,
    and their actual germ pullbacks compose
    contravariantly. Apply the existing representative
    composition theorem after checking the exact
    original coordinate equations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness EuclideanScalarCoordinateMaps
  AnalyticGermUP AnalyticPrefixCoordinatesUP PointedAnalyticPullbackUP PointedAnalyticPullbackComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [analytic_adjacent_prefix_composition]:
    the original p_j is the first j
    coordinates of p_(j+1), as used for
    the nested rings Q_j in 3.4.8(8),
    p. 329. Widened index proofs are
    compared through their actual ordinal values. *)
Theorem analytic_adjacent_prefix_composition (R:realType) (X:lmodType R) n
  (omega:'I_n->Hom X R^o) j (hJN:(j<=n)%N) (hJ1N:(j.+1<=n)%N)
  (P:Hom X (R_n R j)) (Q:Hom X (R_n R j.+1))
  (between:Hom (R_n R j.+1) (R_n R j)):
  is_analytic_prefix_projection omega hJN P ->
  is_analytic_prefix_projection omega hJ1N Q ->
  is_analytic_prefix_projection (fun i:'I_j.+1=>euclidean_scalar_coordinate_map i) (leqnSn j) between ->
  forall x:X,P x = between (Q x).
Proof.
move=>hP hQ hBetween x;apply/ffunP=>i.
rewrite hP hBetween.
change (omega (widen_ord hJN i) x = Q x (widen_ord (leqnSn j) i)).
rewrite hQ.
have hIndex:widen_ord hJN i = widen_ord hJ1N (widen_ord (leqnSn j) i) by apply:val_inj.
by rewrite hIndex.
Qed.

(** Source for [analytic_adjacent_prefix_germ_composition]:
    O_0(p_j) factors through O_0(p_(j+1)),
    the coefficient-ring compatibility in 3.4.8(8),
    p. 329. Apply the existing pointed
    pullback composition and map-extensionality theorems;
    no representative implementation is inspected. *)
Theorem analytic_adjacent_prefix_germ_composition (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) n (omega:'I_n->Hom X R^o)
  j (hJN:(j<=n)%N) (hJ1N:(j.+1<=n)%N)
  (P:Hom X (R_n R j)) (Q:Hom X (R_n R j.+1))
  (between:Hom (R_n R j.+1) (R_n R j))
  (EP:analytic_germ_space (inner_norm_real_norm (@euclidean_inner_productP R j)) (0:R_n R j)->
    analytic_germ_space hNX (0:X))
  (EQ:analytic_germ_space (inner_norm_real_norm (@euclidean_inner_productP R j.+1)) (0:R_n R j.+1)->
    analytic_germ_space hNX (0:X))
  (EB:analytic_germ_space (inner_norm_real_norm (@euclidean_inner_productP R j)) (0:R_n R j)->
    analytic_germ_space (inner_norm_real_norm (@euclidean_inner_productP R j.+1)) (0:R_n R j.+1)):
  is_analytic_prefix_projection omega hJN P ->is_analytic_prefix_projection omega hJ1N Q ->
  is_analytic_prefix_projection (fun i:'I_j.+1=>euclidean_scalar_coordinate_map i) (leqnSn j) between ->
  is_pointed_analytic_germ_pullback P EP ->is_pointed_analytic_germ_pullback Q EQ ->
  is_pointed_analytic_germ_pullback between EB ->
  forall alpha,EP alpha = EQ (EB alpha).
Proof.
move=>hP hQ hBetween hEP hEQ hEB.
have hComposite:=pointed_analytic_pullback_composes hEQ hEB.
apply:(pointed_analytic_pullback_map_extensional hEP hComposite).
exact:(@analytic_adjacent_prefix_composition R X n omega j hJN hJ1N P Q between hP hQ hBetween).
Qed.
