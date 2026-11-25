(** Federer (1969), 4.1.18, p. 375: the
    translated current and its fixed-z deformation
    remain within distance |z| of the original
    support. The current may have unbounded support
    and infinite mass.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockLinearMaps CurrentSpaces CurrentDomainTransport CurrentPushforwardSealed
  CurrentPushforwardSupport CurrentTranslations EuclideanAdditiveGroup
  CurrentTranslationHomotopy CurrentTranslationChain CurrentHomotopyUP
  CurrentHomotopyDomain CurrentHomotopyCylinder CurrentDeformationChainSupport
  EuclideanClosedSupportTube VectorSetSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentTranslationSupportTube.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Variable T:@current_space R h2 n Full hFull m.
Local Notation Support:=(@current_support R h2 n Full hFull m T).
Variable z:X.

(** Source for [current_translation_support_tube]: the
    original translation support lies in the
    literal closed radius-r tube when |z|<=r,
    supporting 4.1.18, p. 375. *)
Theorem current_translation_support_tube r:
  NX z<=r ->
  @current_support R h2 n Full hFull m
    (@current_translation_pushforward R h2 n m z T) `<=`
      @euclidean_closed_support_tube R n Support r.
Proof.
move=>hz y hy.
have [x hx hImage]:=@current_pushforward_support_image R h2 n n m Full Full hFull hFull
  T (@euclidean_translation R n z) (fun _ _=>Logic.I)
  (@current_translation_smooth R n z) (@current_translation_proper R h2 n m z T) y hy.
rewrite -hImage /euclidean_translation addrC.
exact:(@vector_set_sum_contains X Support [set v:X|NX v<=r] x z hx hz).
Qed.

(** Source for [current_translation_chain_support_tube]: each
    original fixed-z homotopy path stays in the
    closed radius-r tube when |z|<=r, as used
    for H_epsilon in 4.1.18, p. 375. *)
Theorem current_translation_chain_support_tube r:
  NX z<=r ->
  @current_support R h2 n Full hFull (1+m)%N
    (@current_translation_chain R h2 n m z T) `<=`
      @euclidean_closed_support_tube R n Support r.
Proof.
move=>hz.
rewrite /current_translation_chain current_domain_transport_support.
move=>y hy.
have [a ha hImage]:=@current_deformation_chain_support R h2 n n m
  (fun _=>True) Full Full (fun x:X=>x) (@euclidean_translation R n z)
  (@current_translation_homotopy R n z) (@current_translation_homotopy_laws R n z)
  (@current_translation_chain_input R h2 n m z T)
  (@current_translation_chain_proper R h2 n m z T) y hy.
pose x:=@euclidean_last_block_map R 1%N n a.
have hx:Support x.
  have hAt:=ha.2.
  by rewrite /current_translation_chain_input current_domain_transport_support in hAt.
have hDisplacement:=@current_translation_homotopy_displacement R n z a ha.1.
rewrite -hImage.
have hMember:=@vector_set_sum_contains X Support [set v:X|NX v<=r]
  x ((@current_translation_homotopy R n z a)-x) hx
  (le_trans hDisplacement hz).
by rewrite addrC subrK in hMember.
Qed.
End CurrentTranslationSupportTube.
