(** Federer (1969), 3.2.31, p. 269: the actual exterior
    norm of the symmetric range/kernel scaling is controlled
    by one small coefficient in each exterior basis word. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanLinearMaps
  InnerProductUP InnerNorm LinearBasis OrthonormalFamilies ExteriorIndices ExteriorOperatorNorm OperatorNormUP
  EuclideanLinearJacobian LinearRankAtLeast SymmetricRangeIdempotentUP ProjectionScaleAutomorphismUP
  LowRankProjectionWord DiagonalExteriorSmallFactor.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [projection_scale_exterior_bound]: supporting
    norm(Lambda^mu t)<epsilon in Federer 3.2.31, p. 269.
    Actual range/kernel scaling laws give diagonal coefficients
    M or d in an orthonormal eigenbasis of the range projection.
    Rank below mu forces a d coefficient in each mu-word. The
    proved diagonal norm bound, followed by abstract norm
    uniqueness, computes the actual standard-coordinate Jacobian.
    No auxiliary Jacobian estimate or dimension bound is assumed. *)
Theorem projection_scale_exterior_bound (R:realType) m v mu
    (D:Hom (R_n R m) (R_n R v)) (P:Hom (R_n R v) (R_n R v))
    (M d:R) (T U:Hom (R_n R v) (R_n R v))
    (e:'I_v->R_n R v) (he:is_basis e)
    (hE:orthonormal_family (@euclidean_inner_product R v) e) (c:'I_v->R):
  @is_symmetric_range_idempotent R (R_n R m) (R_n R v) (@euclidean_inner_product R v) D P ->
  @is_projection_scale_automorphism R (R_n R v) (@euclidean_inner_product R v) P M d T U ->
  (forall i,P (e i)=c i*:e i) ->(forall i,c i=0 \/c i= 1) ->
  ~linear_rank_at_least D mu ->1<=M ->0<d ->d<=1 ->
  euclidean_linear_jacobian mu T<=d*M^+mu.-1.
Proof.
move=>hP hT hEigen hBinary hRank hM1 hd hd1.
pose a i:=if c i==0 then d else M.
have hM:0<=M:=le_trans ler01 hM1.
have hA i:0<=a i.
  rewrite /a; case:(c i==0); [exact:ltW hd|exact hM].
have hAM i:a i<=M.
  rewrite /a; case:(c i==0); first exact (le_trans hd1 hM1).
  exact:lexx.
have hMap i:hom_as_linear T (e i)=a i*:e i.
  change (T (e i)=a i*:e i).
  case:(hBinary i)=>hc.
  - have hZero:P (e i)=0 by rewrite hEigen hc scale0r.
    rewrite /a hc eqxx.
    exact (@projection_scale_kernel R (R_n R v) (@euclidean_inner_product R v)
      P M d T U hT (e i) hZero).
  - have hOne:P (e i)=e i by rewrite hEigen hc scale1r.
    have hh:=@projection_scale_range R (R_n R v) (@euclidean_inner_product R v) P M d T U hT (e i).
    rewrite hOne in hh.
    by rewrite /a hc oner_eq0.
have hRange y:P y=y ->exists x,D x=y.
  exact (@range_idempotent_fixed_range R (R_n R m) (R_n R v)
    (@euclidean_inner_product R v) D P hP y).1.
have hWord (lambda:Lambda v mu):exists i:'I_mu,a (tnth (val lambda) i)<=d.
  have [i hi]:=@low_rank_projection_word_zero_eigenvalue R m v mu D P e c
    hE hEigen hBinary hRange hRank lambda.
  exists i; by rewrite /a hi eqxx.
pose h2:=euclidean_two_nonzero R.
have hBound:=@diagonal_exterior_small_factor_bound R h2 (R_n R v) (@euclidean_inner_product R v)
  (@euclidean_inner_productP R v) v e he hE (hom_as_linear T) a mu d M
  (ltW hd) hM hA hAM hMap hWord.
have hSame:euclidean_linear_jacobian mu T=
    exterior_operator_norm h2 (@euclidean_inner_productP R v) (@euclidean_inner_productP R v) he (hom_as_linear T) mu.
  exact (operator_norm_unique
    (exterior_operator_normP h2 (@euclidean_inner_productP R v) (@euclidean_inner_productP R v)
      (@coordinate_basisP R v) (hom_as_linear T) mu)
    (exterior_operator_normP h2 (@euclidean_inner_productP R v) (@euclidean_inner_productP R v)
      he (hom_as_linear T) mu)).
by rewrite hSame.
Qed.
