(** Federer (1969), 3.2.38, p. 274: smaller good radii retain
    the first-order remainder condition, and reciprocal radii exhaust
    all actual differentiability points at each positive error. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerNorm
  NormDifferentialUP EuclideanUniformRemainderPoints ArchimedeanReciprocal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_uniform_remainder_radius_monotone]: supporting
    increasing measurable good sets as delta decreases in Federer
    3.2.38, p. 274. No regularity of a derivative field is assumed. *)
Lemma euclidean_uniform_remainder_radius_monotone (R:realType) m n
    (f:R_n R m->R_n R n) (e d t:R):
  d<=t ->euclidean_uniform_remainder_points f e t `<=`
    euclidean_uniform_remainder_points f e d.
Proof.
move=>hdt a [D [hD hRate]]; exists D; split=>// x hx.
exact:hRate x (lt_le_trans hx hdt).
Qed.

(** Source for [euclidean_uniform_remainder_reciprocal_exhaustion]:
    supporting countable radius exhaustion before the common delta
    choice in Federer 3.2.38, p. 274. Every actual differential
    supplies a sufficiently small positive natural reciprocal radius. *)
Lemma euclidean_uniform_remainder_reciprocal_exhaustion (R:realType) m n
    (f:R_n R m->R_n R n) a D (e:R):
  has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT f a D ->0<e ->
  exists j,euclidean_uniform_remainder_points f e ((j.+1%:R:R)^-1) a.
Proof.
move=>hD he.
have [d [hd hGood]]:=euclidean_uniform_remainder_from_differential hD he.
have [j hj]:=real_reciprocal_below hd.
exists j; exact:(@euclidean_uniform_remainder_radius_monotone R m n f e
  ((j.+1%:R:R)^-1) d (ltW hj) a hGood).
Qed.
