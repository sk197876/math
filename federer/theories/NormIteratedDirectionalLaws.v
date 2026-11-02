(** Federer (1969), 3.1.11, p. 223: exact domains and
    uniqueness in the recursive coordinate derivative definition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import RealNormUP NormedCurveDerivativeUP NormIteratedDirectionalUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_line_domain_member]: the base point
    belongs to the domain used for the quotient, Federer
    3.1.11, p. 223, using 3.1.1, p. 211. *)
Lemma norm_line_domain_member (R : realType) (X : lmodType R)
    (A : X->Prop) a v : norm_line_domain A a v -> A a.
Proof.
move=>[r [hr hA]].
have h0 : `|(0:R)|<r by rewrite normr0.
have hh := hA 0 h0; by rewrite scale0r addr0 in hh.
Qed.

(** Source for [norm_line_derivative_local_agreement]: agreement
    on a two-sided interval leaves the directional quotient limit
    unchanged, supporting the recursion of Federer 3.1.11, p. 223. *)
Lemma norm_line_derivative_local_agreement (R : realType)
    (X Y : lmodType R) (NY : Y->R) (A B : X->Prop)
    (f g : X->Y) a v y r :
  0<r -> (forall t, `|t|<r -> f (a+t*:v)=g (a+t*:v)) ->
  norm_line_domain B a v ->
  has_norm_line_derivative NY A f a v y ->
  has_norm_line_derivative NY B g a v y.
Proof.
move=>hr he hB [_ hf]; split; first exact hB.
have hzero : `|(0:R)|<r by rewrite normr0.
have ha := he 0 hzero; rewrite scale0r addr0 in ha.
move=>e heps; have [d [hd hb]] := hf e heps.
exists (Num.min r d); split; first by rewrite lt_min hr hd.
move=>t /andP [ht0 ht].
have /andP [htr htd] : (`|t|<r)&&(`|t|<d) by rewrite -lt_min.
rewrite -(he t htr) -ha; exact: hb t (introT andP (conj ht0 htd)).
Qed.

(** Source for [norm_iterated_directional_unique]: the recursive
    partial derivative has at most one value, Federer 3.1.11,
    p. 223. Different representatives agree on the actual
    preceding derivative domain before their limits are compared. *)
Theorem norm_iterated_directional_unique (R : realType)
    (X Y : lmodType R) (NY : Y->R) (hNY : is_real_norm NY)
    (A : X->Prop) (f : X->Y) s a y z :
  has_norm_iterated_directional NY A f s a y ->
  has_norm_iterated_directional NY A f s a z -> y=z.
Proof.
case:s=>[|v s] /=.
- by move=>[_ ->] [_ ->].
- move=>[g [hg [hdom hgy]]] [q [hq hqz]].
  have [r [hr hline]] := hdom.
  have he t (ht : `|t|<r) : g (a+t*:v)=q (a+t*:v).
    have [w hw] := hline t ht; by rewrite (hg _ _ hw) (hq _ _ hw).
  have hqy := norm_line_derivative_local_agreement hr he hqz.1 (conj hdom hgy).
  exact (punctured_norm_limit_unique hNY hqy.2 hqz.2).
Qed.

(** Source for [norm_iterated_directional_domain]: every iterated
    partial derivative lies over the original function domain,
    Federer 3.1.11, p. 223. *)
Theorem norm_iterated_directional_domain (R : realType)
    (X Y : lmodType R) (NY : Y->R)
    (A : X->Prop) (f : X->Y) s a y :
  has_norm_iterated_directional NY A f s a y -> A a.
Proof.
elim:s a y=>[|v s ih] a y /=; first by move=>[].
move=>[g [_ [hdom _]]].
have [z hz] := norm_line_domain_member hdom; exact: ih a z hz.
Qed.

(** Source for [norm_iterated_directional_representative_exists]:
    a total representative may be chosen for the exact graph
    without changing its domain or any of its values, supporting
    the recursive step in Federer 3.1.11, p. 223. *)
Lemma norm_iterated_directional_representative_exists (R : realType)
    (X Y : lmodType R) (NY : Y->R) (hNY : is_real_norm NY)
    (A : X->Prop) (f : X->Y) s :
  exists g : X->Y, forall a y,
    has_norm_iterated_directional NY A f s a y -> g a=y.
Proof.
have hex a : exists y, forall z, has_norm_iterated_directional NY A f s a z -> y=z.
  case:(pselect (exists z, has_norm_iterated_directional NY A f s a z))=>[[z hz]|hn].
  - exists z=>w hw; exact (@norm_iterated_directional_unique R X Y NY hNY A f s a z w hz hw).
  - exists 0=>z hz; exfalso; apply: hn; by exists z.
have [g hg] := choice hex.
by exists g.
Qed.
