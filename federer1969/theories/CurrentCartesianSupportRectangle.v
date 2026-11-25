(** Federer (1969), 4.1.8, p. 360: open annihilation
    cylinders in the two original factors are open on
    A x B. Reuse the original bounded-linear preimage
    and intersection laws of 3.1.18, pp. 229–230. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLinear
  NormFiniteLinearBound NormRegularity NormRegularityOperations
  NormMetric NormOpenTopology NormBoundedLinearTopology NormLinearDomainLaws NormOpenDomainLaws
  EuclideanBlockNorms RealNormUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct EuclideanBlockLinearMaps EuclideanCartesianMap
  CurrentCartesianDomain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCartesianSupportRectangle.
Variable R:realType.
Variables m n:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (m+n))).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (m+n))).
Local Notation p := (@euclidean_first_block_map R m n).
Local Notation q := (@euclidean_last_block_map R m n).
Variable A:set X.
Variable B:set Y.
Hypothesis hA:forall a,A a->norm_domain_interior NX A a.
Hypothesis hB:forall b,B b->norm_domain_interior NY B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).

(** Source for [current_cartesian_support_rectangle]: every
    ambient open neighbourhood of a point of A x B
    contains a rectangle of original open factor neighbourhoods,
    supporting the support identity of Federer 4.1.8,
    p. 360. The earlier 3.1.18 block-ball theorem
    supplies the rectangle, including zero-dimensional blocks. *)
Theorem current_cartesian_support_rectangle z (W:set Z):
  AB z->norm_open_family hNZ W->W z->
  exists U:set X,exists V:set Y,
    norm_open_family hNX U /\ norm_open_family hNY V /\
    U (p z) /\ V (q z) /\ U `<=` A /\ V `<=` B /\
    @euclidean_cartesian_set R m n U V `<=` W.
Proof.
move=>hz hW hWz.
have hInterior:=(@norm_domain_interior_neighbourhood R Z NZ hNZ W z).2
  (@open_nbhs_nbhs (real_norm_metric_space hNZ) z W (conj hW hWz)).
have[r [hr hBall]]:=hInterior.
have hThird:0<r/3 by rewrite divr_gt0 // ltr0n.
pose U:=A `&` [set a|NX (a-p z)<r/3].
pose V:=B `&` [set b|NY (b-q z)<r/3].
have hU:norm_open_family hNX U.
  rewrite /norm_open_family openE=>a [ha hSmall].
  apply:(@norm_domain_interior_neighbourhood R X NX hNX U a).1.
  exact:(@norm_domain_intersection_interior R X NX A (fun a=>NX (a-p z)<r/3) a
    (@hA a ha) (@norm_open_ball_domain_interior R X NX hNX (p z) (r/3) a hSmall)).
have hV:norm_open_family hNY V.
  rewrite /norm_open_family openE=>b [hb hSmall].
  apply:(@norm_domain_interior_neighbourhood R Y NY hNY V b).1.
  exact:(@norm_domain_intersection_interior R Y NY B (fun b=>NY (b-q z)<r/3) b
    (@hB b hb) (@norm_open_ball_domain_interior R Y NY hNY (q z) (r/3) b hSmall)).
have hPointU:U (p z).
  split;first exact:hz.1.
  change (NX (p z-p z)<r/3).
  rewrite subrr (real_seminorm_zero hNX.1);exact:hThird.
have hPointV:V (q z).
  split;first exact:hz.2.
  change (NY (q z-q z)<r/3).
  rewrite subrr (real_seminorm_zero hNY.1);exact:hThird.
exists U,V;split;first exact:hU.
split;first exact:hV.
split;first exact:hPointU.
split;first exact:hPointV.
split;first by move=>a ha;exact:ha.1.
split;first by move=>b hb;exact:hb.1.
move=>x hx.
have hSmall:=@euclidean_product_box_in_ball R m n z x r hr hx.1.2 hx.2.2.
have hPoint:=hBall (x-z) hSmall.
by rewrite addrC subrK in hPoint.
Qed.
End CurrentCartesianSupportRectangle.
