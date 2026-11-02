(** Federer (1969), 3.2.33, p. 270: vanishing
    of h_(mu+1) detects the non-strict rank condition. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates LinearRankUP
  LinearRankAtLeast EuclideanExteriorGramRank.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [euclidean_exterior_gram_low_rank]: the
    low-rank zero locus used to obtain the alternative
    for S in Federer 3.2.33, p. 270. Both
    directions use the original image-basis rank and actual
    Hilbert exterior Gram function; zero degree and all
    ambient dimensions are retained. *)
Lemma euclidean_exterior_gram_low_rank (R:realType) m n mu
    (L:Hom (R_n R m) (R_n R n)):
  euclidean_exterior_gram mu.+1 L= 0 <->
    exists r,has_linear_rank L r /\(r<=mu)%N.
Proof.
split.
- move=>hz; have [r [hRank hr]]:=linear_rank_exists L (@coordinate_basisP R n).
  exists r; split=>//.
  rewrite leqNgt; apply/negP=>hHigh.
  apply:((euclidean_exterior_gram_zero_iff mu.+1 L).1 hz).
  exact:(linear_rank_at_leastP mu.+1 hRank).2 hHigh.
- move=>[r [hRank hr]]; apply:(euclidean_exterior_gram_zero_iff mu.+1 L).2=>hHigh.
  have hBad:=(linear_rank_at_leastP mu.+1 hRank).1 hHigh.
  by have:=leq_trans hBad hr; rewrite ltnn.
Qed.
