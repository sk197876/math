(** Federer (1969), 3.4.3, p. 317: the rank
    criterion in the commutative diagram after the local source change. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates
  LinearRankUP LinearRankAtLeast LinearRankComposition LinearSurjectiveRank
  LinearBasis FiniteBasisComparison EuclideanBlockLinearMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [critical_rank_prefix_kernel]: if L DF(u,v)
    sends (alpha,beta) to alpha and rank DF(u,v)<=nu,
    then DF(u,v) vanishes on {0} times R^(m-nu),
    3.4.3, p. 317. The actual prefix gives full
    composite rank. The proved equal-rank kernel theorem then
    supplies the original vertical vanishing condition. The target
    Y needs no finite basis. *)
Theorem critical_rank_prefix_kernel (R:realType) nu l (Y:lmodType R)
    (D:Hom (R_n R (nu+l)) Y) (L:Hom Y (R_n R nu)) r:
  has_linear_rank D r ->(r<=nu)%N ->
  (forall x,L (D x)=euclidean_first_block x) ->
  forall x,euclidean_first_block x=0 ->D x=0.
Proof.
move=>hRank hBound hPrefix.
have hSurj:forall u,exists x,hom_comp L D x=u.
  move=>u;exists (@euclidean_first_injection R nu l u).
  change (L (D (@euclidean_first_injection R nu l u))=u).
  by rewrite hPrefix euclidean_first_block_injectionK.
have hComposite:has_linear_rank (hom_comp L D) nu.
  apply:(@linear_rank_from_full_threshold R (R_n R (nu+l)) (R_n R nu)
    nu (@coordinate_basis R nu) (@coordinate_basisP R nu) (hom_comp L D)).
  exact:(@linear_surjective_rank_at_least R (R_n R (nu+l)) (R_n R nu)
    nu (@coordinate_basis R nu) (@coordinate_basisP R nu) (hom_comp L D) hSurj).
have [e he]:=(linear_rank_at_leastP nu hComposite).2 (leqnn nu).
have hIndependent:linear_rank_at_least D nu.
  exists e;move=>c hc;apply:he.
  have hh:=congr1 L hc;rewrite linear_sum linear0 in hh.
  have hSum:(\sum_i L (c i*:D (e i)))=\sum_i c i*:hom_comp L D (e i).
    apply:eq_bigr=>i _;by rewrite linearZ hom_compE.
  rewrite hSum in hh;exact:hh.
have hLower:(nu<=r)%N:=(linear_rank_at_leastP nu hRank).1 hIndependent.
have hEqual:r=nu by apply/eqP;rewrite eqn_leq hBound hLower.
have hD:has_linear_rank D nu:=@eq_rect nat r (fun s=>has_linear_rank D s) hRank nu hEqual.
move=>x hx;apply:(linear_composition_equal_rank_kernel hD hComposite).
by rewrite hPrefix.
Qed.
