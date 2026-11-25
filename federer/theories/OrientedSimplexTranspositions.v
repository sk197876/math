(** Federer (1969), 4.1.11, p. 366: the original
    first-pair exchange and the point-join recursion imply
    alternation under every genuine vertex exchange.
    This precedes both prism decomposition and associativity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology fingroup perm.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  FiniteArgumentPermutation FiniteStarTranspositionAlternation CurrentSimplexFirstSwap
  OrientedSimplexCurrentUP OrientedSimplexCurrentSealed OrientedSimplexCurrentLaws
  OrientedSimplexTailAlternation OrientedSimplexFirstSwap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section OrientedSimplexTranspositions.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X
  (inner_norm (@euclidean_inner_productP R n)) x).
Local Notation F := (fun (d:nat) (w:'I_(d.+1)->X)=>@OrientedSimplexCurrent.value R h2 n d w).
Local Notation C := (fun d=>@current_space R h2 n Full hFull d).

(** Source for [oriented_simplex_current_transposition]:
    every genuine exchange negates the original simplex,
    supporting the permutation formula in Federer
    4.1.11, p. 366. Repeated vertices and every ambient
    dimension remain allowed. *)
Theorem oriented_simplex_current_transposition d:
  forall (i j:'I_(d.+1)),i!=j->forall v:'I_(d.+1)->X,
    F d (fun k=>v (tperm i j k))= -F d v.
Proof.
elim:d=>[|d ih] i j hij v.
- have hi:i=ord0:=ord1 i.
  have hj:j=ord0:=ord1 j.
  by rewrite hi hj eqxx in hij.
- pose G:=fun u:{ffun 'I_(d.+2)->X}=>F d.+1 (fun k=>u k).
  have hStar:forall j:'I_(d.+2),j!=lift ord0 ord0->
      forall u:{ffun 'I_(d.+2)->X},
      G (finite_argument_permutation (tperm (lift ord0 ord0) j) u)= -G u.
    move=>k hk u.
    have hAction:(fun l=>finite_argument_permutation (tperm (lift ord0 ord0) k) u l)=
        (fun l=>u (tperm (lift ord0 ord0) k l)).
      apply:funext=>l;by rewrite /finite_argument_permutation ffunE.
    rewrite /G hAction.
    case:(unliftP ord0 k)=>[p hp|hp].
    + rewrite hp in hk *.
      have hDistinct:p!=ord0 by move:hk;rewrite (inj_eq (@lift_inj (d.+2) ord0)).
      apply:(@oriented_simplex_current_tail_negative R h2 n d (fun l=>u l)).
      * exact:(@current_simplex_positive_swap_head X d (fun l=>u l) ord0 p).
      * rewrite current_simplex_positive_swap_tail.
        have hZero:ord0!=p by rewrite eq_sym.
        exact:(ih ord0 p hZero (current_simplex_tail (fun l=>u l))).
    + rewrite hp tpermC.
      exact:(@oriented_simplex_current_first_swap R h2 d n (fun l=>u l)).
  have hAll:=@finite_star_transposition_alternation R (Finite.clone 'I_(d.+2) _)
    X (C d.+1) G (lift ord0 ord0) hStar i j hij [ffun k=>v k].
  have hValues:(fun l=>finite_argument_permutation (tperm i j) [ffun k=>v k] l)=
      (fun l=>v (tperm i j l)).
    apply:funext=>l;by rewrite /finite_argument_permutation !ffunE.
  have hOriginal:(fun l=>[ffun k=>v k] l)=v.
    apply:funext=>l;by rewrite ffunE.
  by rewrite /G hValues hOriginal in hAll.
Qed.

(** Source for [oriented_simplex_current_permutation_parity]:
    the original ordered simplex changes by the parity
    sign of every vertex permutation, supporting
    Federer's index formula in 4.1.11, p. 366.
    The identification with the Chapter 1 index is separate. *)
Theorem oriented_simplex_current_permutation_parity d (s:'S_(d.+1))
    (v:'I_(d.+1)->X):
  F d (fun k=>v (s k))=(-1:R)^+(odd_perm s)*:F d v.
Proof.
pose G:=fun u:{ffun 'I_(d.+1)->X}=>F d (fun k=>u k).
have hSwap:forall i j:'I_(d.+1),i!=j->forall u:{ffun 'I_(d.+1)->X},
    G (finite_argument_permutation (tperm i j) u)= -G u.
  move=>i j hij u.
  have hValues:(fun l=>finite_argument_permutation (tperm i j) u l)=
      (fun l=>u (tperm i j l)).
    apply:funext=>l;by rewrite /finite_argument_permutation ffunE.
  rewrite /G hValues.
  exact:(oriented_simplex_current_transposition hij (fun l=>u l)).
have hAll:=@finite_transposition_parity_alternation R (Finite.clone 'I_(d.+1) _)
  X (C d) G hSwap s [ffun k=>v k].
have hValues:(fun l=>finite_argument_permutation s [ffun k=>v k] l)=(fun l=>v (s l)).
  apply:funext=>l;by rewrite /finite_argument_permutation !ffunE.
have hOriginal:(fun l=>[ffun k=>v k] l)=v.
  apply:funext=>l;by rewrite ffunE.
by rewrite /G hValues hOriginal in hAll.
Qed.
End OrientedSimplexTranspositions.
