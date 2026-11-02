(** Federer (1969), 3.1.20, p. 233: a finite derivative-rank
    maximum exists on every nonempty finite-dimensional domain.
    This elementary supporting maximum does not assume continuity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates LinearRankUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [euclidean_maximal_rank_exists]: the supremum mu
    in the converse proof of Federer 3.1.20, p. 233, is an
    attained integer maximum when the domain is nonempty. *)
Lemma euclidean_maximal_rank_exists (R:realType) n (A:R_n R n->Prop)
    (D:R_n R n->Hom (R_n R n) (R_n R n)) :
  (exists a,A a) -> exists mu,
    (mu<=n)%N /\ (exists a,A a /\ has_linear_rank (D a) mu) /\
    forall a r,A a -> has_linear_rank (D a) r -> (r<=mu)%N.
Proof.
move=>[a ha].
pose P r:= `[< exists x,A x /\ has_linear_rank (D x) r >].
have hbound r:P r -> (r<=n)%N.
  move=>/asboolP [x [hx hr]].
  exact (@linear_rank_codomain_bound R (R_n R n) (R_n R n) (D x) n
    (@coordinate_basis R n) (@coordinate_basisP R n) r hr).
have [r [hr hrn]]:=linear_rank_exists (D a) (@coordinate_basisP R n).
have hne:exists r,P r by exists r; apply/asboolP; exists a; split.
have [mu hmu hmax]:=@ex_maxnP P n hne hbound.
exists mu; split; first exact: hbound.
split; first exact: (elimT (asboolP _) hmu).
move=>x s hx hs; apply: hmax; apply/asboolP; exists x; by split.
Qed.
