(** Federer (1969), 3.1.21, p. 234: ambient normal
    lifts of a class-(k+1) diffeomorphism are class-k
    diffeomorphisms, including k=0. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  NormDifferentialUP NormDifferentialInverseIdentities NormClassOneUP NormRegularity NormDiffeomorphismUP
  EuclideanBlockLinearMaps EuclideanBundleUP EuclideanCotangentLiftUP EuclideanCotangentLiftClass EuclideanCotangentLiftLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_cotangent_lift_diffeomorphism]:
    supporting ambient charts for Nor(B) in Federer 3.1.21,
    p. 234. The actual derivative fields are obtained from
    class-(k+1) maps; inverse-adjoint laws follow from the pairing and the
    chain rule. Only one derivative of regularity is lost. *)
Theorem euclidean_cotangent_lift_diffeomorphism (R:realType) n k
    (A C:R_n R n->Prop) (f g:R_n R n->R_n R n) :
  is_norm_diffeomorphism (inner_norm_real_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) A C f g k.+1 ->
  exists (D E:R_n R n->Hom (R_n R n) (R_n R n)),
    (forall x,A x -> has_norm_differential (inner_norm (@euclidean_inner_productP R n))
      (inner_norm (@euclidean_inner_productP R n)) A f x (D x)) /\
    (forall y,C y -> has_norm_differential (inner_norm (@euclidean_inner_productP R n))
      (inner_norm (@euclidean_inner_productP R n)) C g y (E y)) /\
    is_norm_diffeomorphism (inner_norm_real_norm (@euclidean_inner_productP R (n+n)))
      (inner_norm_real_norm (@euclidean_inner_productP R (n+n)))
      (fun z=>A (@euclidean_first_block_map R n n z))
      (fun z=>C (@euclidean_first_block_map R n n z))
      (@euclidean_cotangent_lift R n f E) (@euclidean_cotangent_lift R n g D) k.
Proof.
move=>hD.
pose X:=R_n R n.
pose P:=R_n R (n+n).
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose NP:=inner_norm (@euclidean_inner_productP R (n+n)).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hNP:=inner_norm_real_norm (@euclidean_inner_productP R (n+n)).
have hfk:=norm_diffeomorphism_forward_class hD.
have hgk:=norm_diffeomorphism_inverse_class hD.
have hk: (1<=k.+1)%N by [].
have [D hFD]:=(@norm_class_firstP R X X NX NX hNX hNX A f).1 (norm_class_lower hk hfk).
have [E hGE]:=(@norm_class_firstP R X X NX NX hNX hNX C g).1 (norm_class_lower hk hgk).
have hfx x (hx:A x):C (f x):=@norm_diffeomorphism_maps R X X NX NX hNX hNX A C f g k.+1 hD x hx.
have hgy y (hy:C y):A (g y):=@norm_diffeomorphism_inverse_maps R X X NX NX hNX hNX A C f g k.+1 hD y hy.
have hgf x (hx:A x):g (f x)=x:=@norm_diffeomorphism_left_inverse R X X NX NX hNX hNX A C f g k.+1 hD x hx.
have hfg y (hy:C y):f (g y)=y:=@norm_diffeomorphism_right_inverse R X X NX NX hNX hNX A C f g k.+1 hD y hy.
have hDf x (hx:A x):has_norm_differential NX NX A f x (D x):=norm_class_one_differential hFD hx.
have hDg y (hy:C y):has_norm_differential NX NX C g y (E y):=norm_class_one_differential hGE hy.
have hED x (hx:A x) v:E (f x) (D x v)=v.
  have he:=@norm_differentials_left_inverse R X X NX NX hNX hNX A C f g x (D x) (E (f x))
    hfx hgf (hDf x hx) (hDg _ (hfx x hx)).
  exact (congr1 (fun L:Hom X X=>L v) he).
have hDE y (hy:C y) v:D (g y) (E y v)=v.
  have he:=@norm_differentials_left_inverse R X X NX NX hNX hNX C A g f y (E y) (D (g y))
    hgy hfg (hDg y hy) (hDf _ (hgy y hy)).
  exact (congr1 (fun L:Hom X X=>L v) he).
exists D,E; split=>//; split=>//; constructor.
- pose I:=hom_of_linear (linear_id P).
  have hI:norm_bounded_linear NP NP I.
    exists 1; split; first exact: ler01.
    by move=>v; rewrite /I hom_of_linearE /= mul1r.
  exists I,I; split=>//; split=>//; by split.
- exact (@euclidean_cotangent_lift_class R n k A C f g E
    (norm_class_lower (leqnSn k) hfk) hgk hfx hDg).
- exact (@euclidean_cotangent_lift_class R n k C A g f D
    (norm_class_lower (leqnSn k) hgk) hfk hgy hDf).
- move=>z hz; rewrite euclidean_cotangent_lift_base; exact: hfx.
- move=>z hz; rewrite euclidean_cotangent_lift_base; exact: hgy.
- exact (@euclidean_cotangent_lift_cancel R n A f g D E hgf hED).
- exact (@euclidean_cotangent_lift_cancel R n C g f E D hfg hDE).
Qed.
