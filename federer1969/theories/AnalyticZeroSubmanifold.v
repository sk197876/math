(** Federer (1969), 3.1.24, p. 240, referring to 3.1.19, p. 231, final sentence: a subset is a
    zero-dimensional submanifold exactly when every point is isolated. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom ModuleQuotient SubspaceSums SubspaceCarrier
  GrassmannSubspaces GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness LinearRankUP NormDifferentialUP NormOpenDomainLaws
  NormDiffeomorphismUP NormBallTranslation EuclideanSubmanifoldUP SubmanifoldBasicLaws ZeroSubmanifold AnalyticSubmanifoldUP NormAnalyticTranslation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [isolated_points_zero_analytic_submanifold]: 3.1.24, p. 240: isolated points
    give local translation charts for the zero plane, the reverse
    implication of the last sentence of Federer 3.1.19, p. 231.
    All ambient dimensions are covered. *)
Theorem isolated_points_zero_analytic_submanifold (R:realType) n (B:set (R_n R n)) :
  (forall b, B b -> norm_isolated_point (inner_norm (@euclidean_inner_productP R n)) B b) ->
  @is_euclidean_analytic_submanifold R n 0 B.
Proof.
move=>hB b hb.
pose X:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
have [_ [r [hr hIso]]]:=hB b hb.
pose T:=fun x:X=>NX (x-b)<r.
pose C:=fun y:X=>NX (y-0)<r.
pose sigma:=fun x:X=>x-b.
pose tau:=fun y:X=>y+b.
have hD:=@norm_ball_translation_diffeomorphism R X NX hNX b r 1%N.
have [Z hZ]:=@zero_dimensional_grassmann_exists R X.
have hbT:T b by rewrite /T /NX subrr inner_norm0.
have hTopen x (hx:T x):norm_domain_interior NX T x.
  exact (@norm_open_ball_domain_interior R X NX hNX b r x hx).
have hCopen y (hy:C y):norm_domain_interior NX C y.
  exact (@norm_open_ball_domain_interior R X NX hNX 0 r y hy).
have hsA:=(@norm_translations_analytic R X NX hNX T hTopen b).2.
have htA:=(@norm_translations_analytic R X NX hNX C hCopen b).1.
exists T,C,sigma,tau,Z; split; last by split.
constructor.
- exact (@norm_open_ball_domain_interior R X NX hNX b r b hbT).
- exact hD.
- apply/seteqP; split=>y.
  + move=>[x [hBx hTx] hxy].
    have hxb:x=b.
      have hh:=hIso (x-b) hTx; rewrite (addrC b (x-b)) subrK in hh.
      exact: hh hBx.
    have hy0:y=0 by rewrite -hxy /sigma hxb subrr.
    split; first exact: (hZ y).2 hy0.
    by rewrite hy0 /C /NX subr0 inner_norm0.
  + move=>[hyZ hyC].
    have hy0:y=0:=(hZ y).1 hyZ.
    exists b; first exact: conj hb hbT.
    by rewrite /sigma subrr hy0.
Qed.

(** Source for [federer_3_1_19_analytic_zero]: 3.1.24, p. 240: the final equivalence in Federer
    3.1.19, p. 231, including the empty set, the
    zero-dimensional ambient space. *)
Theorem federer_3_1_19_analytic_zero (R:realType) n (B:set (R_n R n)) :
  @is_euclidean_analytic_submanifold R n 0 B <->
  forall b, B b -> norm_isolated_point (inner_norm (@euclidean_inner_productP R n)) B b.
Proof.
split.
- move=>hB b hb; exact: zero_submanifold_point_isolated (analytic_submanifold_class_one hB) hb.
- exact: isolated_points_zero_analytic_submanifold.
Qed.
