(** Federer (1969), 3.4.1, p. 310: public original critical sets and their actual-differential interpretation. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  HilbertFormCompactness RealNormUP NormDifferentialUP NormDifferentialLinear NormDifferentialDirectional LinearRankUP
  FiniteSourceLinearRank CriticalValueLociUP CriticalValueLociSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_rank_locus]: the original source
    {x in A:dim im Df(x)<=nu} of 3.4.1, p. 310. The alias exposes
    the opaque object, not its existence construction. *)
Definition critical_rank_locus (R:realType) m (Y:lmodType R) (NY:Y->R)
    (A:set (R_n R m)) (f:R_n R m->Y) nu:=@CriticalValues.locus R m Y NY A f nu.

(** Source for [critical_value_image]: the actual image occurring in
    3.4.1, p. 310, with the original function and original rank locus. *)
Definition critical_value_image (R:realType) m (Y:lmodType R) (NY:Y->R)
    (A:set (R_n R m)) (f:R_n R m->Y) nu:=@CriticalValues.image R m Y NY A f nu.

(** Source for [critical_rank_locusP]: exact actual differential and
    finite range dimension at an original source point, 3.4.1, p. 310.
    No derivative is extended outside its actual domain. *)
Lemma critical_rank_locusP (R:realType) m (Y:lmodType R) (NY:Y->R)
    (A:set (R_n R m)) (f:R_n R m->Y) nu a:
  critical_rank_locus NY A f nu a <-> A a /\exists D:Hom (R_n R m) Y,
    has_norm_differential (inner_norm (@euclidean_inner_productP R m)) NY A f a D /\
    exists r,has_linear_rank D r /\(r<=nu)%N.
Proof. exact:(critical_rank_locus_equation (@CriticalValues.laws R m Y NY A f nu) a). Qed.

(** Source for [critical_value_imageE]: original image equality of
    3.4.1, p. 310, obtained only from the public independent laws. *)
Lemma critical_value_imageE (R:realType) m (Y:lmodType R) (NY:Y->R)
    (A:set (R_n R m)) (f:R_n R m->Y) nu:
  critical_value_image NY A f nu=f @` critical_rank_locus NY A f nu.
Proof. exact:(critical_value_image_equation (@CriticalValues.laws R m Y NY A f nu)). Qed.

(** Source for [critical_rank_locus_subset]: the original rank locus
    lies in the original map domain, 3.4.1, p. 310. *)
Lemma critical_rank_locus_subset (R:realType) m (Y:lmodType R) (NY:Y->R)
    (A:set (R_n R m)) (f:R_n R m->Y) nu:critical_rank_locus NY A f nu `<=` A.
Proof. move=>a /critical_rank_locusP[ha _];exact:ha. Qed.

(** Source for [critical_rank_locus_at_differential]: the notation
    dim im Df(x) in 3.4.1, p. 310, is independent of an actual
    differential witness. Uniqueness is the already proved 3.1.1 theorem.
    No derivative field, target basis or coordinate representative is assumed. *)
Lemma critical_rank_locus_at_differential (R:realType) m (Y:lmodType R) (NY:Y->R)
    (hNY:is_real_norm NY) (A:set (R_n R m)) (f:R_n R m->Y) nu a (D:Hom (R_n R m) Y):
  has_norm_differential (inner_norm (@euclidean_inner_productP R m)) NY A f a D ->
  (critical_rank_locus NY A f nu a <->exists r,has_linear_rank D r /\(r<=nu)%N).
Proof.
move=>hD;split.
- move/critical_rank_locusP=>[_ [L [hL [r [hRank hr]]]]].
  have he:L=D:=norm_differential_unique (inner_norm_real_norm (@euclidean_inner_productP R m)) hNY hL hD.
  exists r;by rewrite -he.
- move=>[r [hRank hr]];apply/critical_rank_locusP.
  split;first exact:(norm_domain_interior_member (inner_norm_real_norm (@euclidean_inner_productP R m)) (norm_differential_interior hD)).
  exists D;split;first exact:hD.
  by exists r.
Qed.

(** Source for [critical_rank_locus_monotone]: the rank-threshold
    source in 3.4.1, p. 310, increases with the integer threshold.
    The same actual differential and same actual image basis suffice. *)
Lemma critical_rank_locus_monotone (R:realType) m (Y:lmodType R) (NY:Y->R)
    (A:set (R_n R m)) (f:R_n R m->Y) nu mu:
  (nu<=mu)%N ->critical_rank_locus NY A f nu `<=` critical_rank_locus NY A f mu.
Proof.
move=>hnu a /critical_rank_locusP[ha [D [hD [r [hRank hr]]]]].
apply/critical_rank_locusP;split;first exact:ha.
exists D;split;first exact:hD.
exists r;split;first exact:hRank.
exact:(leq_trans hr hnu).
Qed.

(** Source for [critical_rank_locus_source_dimension]: for an arbitrary
    normed target, the actual rank never exceeds the finite source
    dimension. This discharges the rank-existence implicit in 3.4.1,
    p. 310, rather than assuming the target finite dimensional. *)
Theorem critical_rank_locus_source_dimension (R:realType) m (Y:lmodType R) (NY:Y->R)
    (A:set (R_n R m)) (f:R_n R m->Y) a:
  critical_rank_locus NY A f m a <-> A a /\
    norm_differentiable_at (inner_norm (@euclidean_inner_productP R m)) NY A f a.
Proof.
split.
- move/critical_rank_locusP=>[ha [D [hD _]]];split;first exact:ha.
  by exists D.
- move=>[ha [D hD]].
  have [r [hRank hr]]:=@finite_source_linear_rank_exists R (R_n R m) Y D m
    (@coordinate_basis R m) (@coordinate_basisP R m).
  apply/critical_rank_locusP;split;first exact:ha.
  exists D;split;first exact:hD.
  by exists r.
Qed.

(** Source for [critical_rank_locus_linearP]: supporting linear-map
    interpretation of the rank locus in 3.4.1, p. 310. On an open domain,
    a bounded linear map has constant rank; hence its entire domain
    satisfies the threshold exactly when that rank does. *)
Lemma critical_rank_locus_linearP (R:realType) m (Y:lmodType R) (NY:Y->R)
    (hNY:is_real_norm NY) (A:set (R_n R m))
    (hA:forall a,A a ->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R m)) A a)
    (L:Hom (R_n R m) Y) (hL:norm_bounded_linear
      (inner_norm (@euclidean_inner_productP R m)) NY L) r
    (hRank:has_linear_rank L r) nu a:
  critical_rank_locus NY A L nu a <->A a /\(r<=nu)%N.
Proof.
have hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
split.
- move=>ha;have hAa:=critical_rank_locus_subset ha.
  have hD:=norm_differential_linear hNX hNY (hA a hAa) hL.
  have [t [ht htnu]]:=(@critical_rank_locus_at_differential R m Y NY hNY A L nu a L hD).1 ha.
  have he:t=r:=linear_rank_unique ht hRank.
  split;first exact:hAa.
  by rewrite -he.
- move=>[ha hr].
  have hD:=norm_differential_linear hNX hNY (hA a ha) hL.
  apply:(@critical_rank_locus_at_differential R m Y NY hNY A L nu a L hD).2.
  by exists r.
Qed.

(** Source for [critical_rank_locus_constant]: supporting the rank-zero
    boundary in 3.4.1, p. 310. Every point of an open domain belongs to
    the critical locus of a constant map, for every natural threshold. *)
Lemma critical_rank_locus_constant (R:realType) m (Y:lmodType R) (NY:Y->R)
    (hNY:is_real_norm NY) (A:set (R_n R m))
    (hA:forall a,A a ->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R m)) A a) (c:Y) nu:
  critical_rank_locus NY A (fun _=>c) nu=A.
Proof.
apply/seteqP;split;first exact:critical_rank_locus_subset.
move=>a ha.
have hD:=@norm_differential_constant R (R_n R m) Y
  (inner_norm (@euclidean_inner_productP R m)) NY
  (inner_norm_real_norm (@euclidean_inner_productP R m)) hNY A a c (hA a ha).
apply/critical_rank_locusP;split;first exact:ha.
exists 0;split;first exact:hD.
exists 0%N;split;last exact:leq0n.
apply/linear_rank_zeroP;exact:hom_zeroE.
Qed.
