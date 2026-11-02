(** Federer (1969), 3.1.19, p. 231: the derivative of a
    parametrisation with a differentiable left inverse has full source rank. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Hom LinearBasis LinearRankUP LinearRankAtLeast LinearFullRank.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [linear_injective_rank]: supporting the rank-mu
    assertion in (4) implies (3), Federer 3.1.19, p. 231. An
    injective linear map from a mu-dimensional space has rank mu. *)
Lemma linear_injective_rank (K:fieldType) (X Y:lmodType K)
    m (b:'I_m->X) (hb:is_basis b) n (c:'I_n->Y) (hc:is_basis c) (L:Hom X Y) :
  injective L -> has_linear_rank L m.
Proof.
move=>hi.
have [r [hr hrc]]:=linear_rank_exists L hc.
have hmr: (m<=r)%N := (linear_rank_at_leastP m hr).1 ((linear_full_rankP hb L).2 hi).
have hrm: (r<=m)%N := linear_rank_domain_bound hb hr.
have he:r=m by apply/eqP; rewrite eqn_leq hrm hmr.
by rewrite -he.
Qed.
