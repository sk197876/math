(** Federer (1969), 3.2.9, p. 247: the
    exact stacked-kernel calculation ker(Df,p)=ker Df
    intersect ker p. A coordinate projection
    separating ker Df makes the stack injective. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanBlockLinearMaps EuclideanStackedMap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Kernel.
Variable R:realType.
Variables m n k:nat.
Local Notation X:=(R_n R m).
Local Notation Y:=(R_n R n).
Local Notation W:=(R_n R k).

(** Source for [euclidean_stacked_linear_first]: first
    coordinate of the stacked differential in
    Federer 3.2.9, p. 247. *)
Lemma euclidean_stacked_linear_first (L:Hom X Y) (p:Hom X W) x:
  @euclidean_first_block_map R n k (euclidean_stacked_linear_map L p x)=L x.
Proof.
change (euclidean_first_block (euclidean_stacked_linear_map L p x)=L x).
rewrite euclidean_stacked_linear_value; exact:euclidean_stacked_first_block.
Qed.

(** Source for [euclidean_stacked_linear_last]: complementary
    coordinate of the stacked differential in
    Federer 3.2.9, p. 247. *)
Lemma euclidean_stacked_linear_last (L:Hom X Y) (p:Hom X W) x:
  @euclidean_last_block_map R n k (euclidean_stacked_linear_map L p x)=p x.
Proof.
change (euclidean_last_block (euclidean_stacked_linear_map L p x)=p x).
rewrite euclidean_stacked_linear_value; exact:euclidean_stacked_last_block.
Qed.

(** Source for [euclidean_stacked_kernel]: the
    displayed identity ker DU_lambda=ker Df intersect
    ker p_lambda in Federer 3.2.9, p. 247. *)
Lemma euclidean_stacked_kernel (L:Hom X Y) (p:Hom X W) x:
  euclidean_stacked_linear_map L p x=0 <-> L x=0 /\ p x=0.
Proof.
split.
- move=>hZero; split.
  + have hh:=congr1 (@euclidean_first_block_map R n k) hZero.
    by rewrite euclidean_stacked_linear_first linear0 in hh.
  + have hh:=congr1 (@euclidean_last_block_map R n k) hZero.
    by rewrite euclidean_stacked_linear_last linear0 in hh.
- move=>[hL hp].
  rewrite /euclidean_stacked_linear_map hom_addE !hom_compE hL hp !linear0 add0r.
  exact:erefl.
Qed.

(** Source for [euclidean_stacked_kernel_injective]:
    membership in A_lambda in the proof of
    Federer 3.2.9, p. 247, when p_lambda
    separates the actual derivative kernel. *)
Lemma euclidean_stacked_kernel_injective (L:Hom X Y) (p:Hom X W):
  (forall x,L x=0 -> p x=0 -> x=0) -> injective (euclidean_stacked_linear_map L p).
Proof.
move=>hSep x y hEq.
have hB:=linearB (hom_as_linear (euclidean_stacked_linear_map L p)) x y.
have hZero:euclidean_stacked_linear_map L p (x-y)=0.
  change (euclidean_stacked_linear_map L p (x-y)=
    euclidean_stacked_linear_map L p x-euclidean_stacked_linear_map L p y) in hB.
  by rewrite hB hEq subrr.
have [hL hp]:=(euclidean_stacked_kernel L p (x-y)).1 hZero.
have hDiff:x-y=0:=hSep (x-y) hL hp.
by move/eqP:hDiff; rewrite subr_eq0=>/eqP.
Qed.
End Kernel.
