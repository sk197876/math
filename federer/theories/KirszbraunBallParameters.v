(** Federer (1969), 2.10.43, printed p. 201: P consists of pairs
    (f(x),|x-a|) for x in the finite original source F, where a is the new
    source point. The membership predicate is specified directly;
    finiteness, compactness and positive radii are proved consequences. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets cardinality topology.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerNorm WeightedBallMinimumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [kirszbraun_ball_parameters]: direct finite
    prescribed-ball parameter family of 2.10.43, p. 201.
    Membership is expressed by the printed centre and
    radius laws, without choosing any extension value. *)
Definition kirszbraun_ball_parameters (R : realType) m n
    (F : set (inner_metric_space (@euclidean_inner_productP R m)))
    (f : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n))
    (a : inner_metric_space (@euclidean_inner_productP R m)) :
    set ((inner_metric_space (@euclidean_inner_productP R n))*R^o) :=
  [set p | exists x, F x /\ p.1=f x /\ p.2=inner_norm (@euclidean_inner_productP R m) (x-a)].

(** Source for [kirszbraun_ball_parameters_image]: supporting
    image description of P in 2.10.43, p. 201.
    It is derived from the parameter membership laws
    and is used only to prove finiteness and compactness. *)
Lemma kirszbraun_ball_parameters_image (R : realType) m n F f a :
  @kirszbraun_ball_parameters R m n F f a=
    (fun x=>(f x,inner_norm (@euclidean_inner_productP R m) (x-a))) @` F.
Proof.
apply/seteqP; split=> p.
- move=> [x [hx [h1 h2]]]; exists x=> //.
  by rewrite (surjective_pairing p) h1 h2.
- move=> [x hx <-]; exists x; repeat split=> //.
Qed.

(** Source for [kirszbraun_ball_parameters_compact]: direct
    compactness of the finite parameter family used
    in 2.10.43, p. 201. No continuity of
    f is required for the finite-image argument. *)
Lemma kirszbraun_ball_parameters_compact (R : realType) m n F f a :
  finite_set F -> compact (@kirszbraun_ball_parameters R m n F f a).
Proof.
move=> hF; rewrite kirszbraun_ball_parameters_image.
apply: finite_compact; exact: finite_image _ hF.
Qed.

(** Source for [kirszbraun_ball_parameters_nonempty]: supporting
    nonempty finite-family application of 2.10.40 inside
    2.10.43, p. 201. The empty family is
    handled separately by choosing any target point. *)
Lemma kirszbraun_ball_parameters_nonempty (R : realType) m n F f a :
  F !=set0 -> @kirszbraun_ball_parameters R m n F f a !=set0.
Proof.
move=> [x hx]; exists (f x,inner_norm (@euclidean_inner_productP R m) (x-a)).
exists x; repeat split=> //.
Qed.

(** Source for [kirszbraun_ball_parameters_positive]: direct
    strict positivity of the prescribed radii in
    2.10.43, p. 201, since the new point
    does not belong to the finite original source. *)
Lemma kirszbraun_ball_parameters_positive (R : realType) m n F f a :
  (forall x, F x -> x!=a) ->
  positive_ball_parameter_family (@kirszbraun_ball_parameters R m n F f a).
Proof.
move=> hne p [x [hx [h1 h2]]].
by rewrite h2 inner_norm_gt0 subr_eq0; exact: hne x hx.
Qed.

(** Source for [kirszbraun_contact_source_preimage]: direct
    choice of source points corresponding to contact
    centres in 2.10.43, p. 201. The contact
    equality gives |f(x)-b|=c |x-a|; repetitions
    are allowed and no injectivity of f is assumed. *)
Lemma kirszbraun_contact_source_preimage (R : realType) m n F f a
    (b z : inner_metric_space (@euclidean_inner_productP R n)) (c : R) :
  weighted_ball_contact_centres (@kirszbraun_ball_parameters R m n F f a) b c z ->
  exists x, F x /\ z=f x /\
    inner_norm (@euclidean_inner_productP R n) (z-b)=
      c*inner_norm (@euclidean_inner_productP R m) (x-a).
Proof.
move=> [r [hp hnorm]].
have [x [hx [hz hr]]] := hp.
change (z=f x) in hz.
change (r=inner_norm (@euclidean_inner_productP R m) (x-a)) in hr.
exists x; split=> //; split=> //.
by rewrite -[z-b]opprB inner_normN hnorm hr mulrC.
Qed.
