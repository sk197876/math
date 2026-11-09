(** Federer (1969), 3.4.4, p. 318: the
    actual differential image of the printed product example. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  ConcatenatedFamilies EuclideanBlockCoordinates EuclideanBlockLinearMaps LinearRankUP LinearRankAtLeast
  LinearSurjectiveRank LinearRankTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [critical_prefix_linear_map]: the differential
    retaining exactly the first nu coordinates and annihilating
    the rest in 3.4.4, p. 318. *)
Definition critical_prefix_linear_map (R:realType) (m nu:nat):Hom (R_n R m) (R_n R m).
Proof.
apply:(@HomMap R (R_n R m) (R_n R m)
  (fun x:R_n R m=>[ffun i:'I_m=>if (i<nu)%N then x i else 0])).
apply/asboolP=>c x y;apply/ffunP=>i;rewrite !ffunE.
by case:(i<nu)%N=>//;rewrite scaler0 add0r.
Defined.

(** Source for [critical_prefix_linear_rank]: the exact
    rank nu of the actual printed differential in
    3.4.4, p. 318. The prefix projection is
    onto R^nu and its inclusion is injective, including
    nu=0. No numerical rank is supplied as a premise. *)
Theorem critical_prefix_linear_rank (R:realType) nu l:
  has_linear_rank (@critical_prefix_linear_map R (nu+l) nu) nu.
Proof.
pose X:=R_n R (nu+l).
pose V:=R_n R nu.
pose P:=@euclidean_first_block_map R nu l.
pose I:=@euclidean_first_injection_map R nu l.
have hCancel:cancel I P:=@euclidean_first_block_injectionK R nu l.
have hSurjective:forall v:V,exists x:X,P x=v.
  move=>v;exists (I v);exact:euclidean_first_block_injectionK.
have hFull:=@linear_surjective_rank_at_least R X V nu (@coordinate_basis R nu)
  (@coordinate_basisP R nu) P hSurjective.
have hP:has_linear_rank P nu:=@linear_rank_from_full_threshold R X V nu
  (@coordinate_basis R nu) (@coordinate_basisP R nu) P hFull.
have hInjective:injective I:=can_inj hCancel.
have hRank:=@linear_injective_postcomposition_rank R X V X P I (nu+l)%N
  (@coordinate_basis R (nu+l)) (@coordinate_basisP R (nu+l)) nu hInjective hP.
have hEqual:hom_comp I P=@critical_prefix_linear_map R (nu+l) nu.
  apply:hom_ext=>x;apply/ffunP=>i.
  rewrite hom_compE /I /P /euclidean_first_injection_map /euclidean_first_block_map
    /critical_prefix_linear_map /= ffunE.
  case:(split_ordP i)=>[j ->|j ->].
  - have hIndex:((lshift l j)<nu)%N:=ltn_ord j.
    by rewrite ffunE hIndex concatenate_family_l /= /euclidean_first_block ffunE.
  - have hIndex:~~((rshift nu j)<nu)%N by rewrite -leqNgt;exact:leq_addr.
    by rewrite ffunE (negPf hIndex) concatenate_family_r /= ffunE.

by rewrite hEqual in hRank.
Qed.
