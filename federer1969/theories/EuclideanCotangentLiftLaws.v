(** Federer (1969), 3.1.21, p. 234: inverse laws of
    the normal-bundle ambient coordinate changes. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom Bilinear GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockLinearMaps EuclideanAdjoint EuclideanCotangentLiftUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Lifts.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation p := (@euclidean_first_block_map R n n).
Local Notation q := (@euclidean_last_block_map R n n).
Local Notation i := (@euclidean_first_injection_map R n n).
Local Notation j := (@euclidean_last_injection_map R n n).

(** Source for [euclidean_cotangent_lift_base]: the base
    coordinate is f(x), supporting normal-bundle coordinate
    changes in Federer 3.1.21, p. 234. *)
Lemma euclidean_cotangent_lift_base (f:X->X) (E:X->Hom X X) z :
  p (@euclidean_cotangent_lift R n f E z)=f (p z).
Proof.
have hpi y:p (i y)=y:=@euclidean_first_block_injectionK R n n y.
have hpj y:p (j y)=0:=@euclidean_first_block_last_injection R n n y.
by rewrite /euclidean_cotangent_lift (linD (hom_linear p)) hpi hpj addr0.
Qed.

(** Source for [euclidean_cotangent_lift_vector]: the normal
    vector coordinate is the inverse derivative adjoint applied
    to u, supporting Federer 3.1.21, p. 234. *)
Lemma euclidean_cotangent_lift_vector (f:X->X) (E:X->Hom X X) z :
  q (@euclidean_cotangent_lift R n f E z)=@euclidean_adjoint R n (E (f (p z))) (q z).
Proof.
have hqi y:q (i y)=0:=@euclidean_last_block_first_injection R n n y.
have hqj y:q (j y)=y:=@euclidean_last_block_injectionK R n n y.
by rewrite /euclidean_cotangent_lift (linD (hom_linear q)) hqi hqj add0r.
Qed.

(** Source for [euclidean_cotangent_lift_cancel]: supporting
    inverse normal-bundle coordinate maps in Federer 3.1.21,
    p. 234. The inverse adjoints cancel by the pairing law. *)
Lemma euclidean_cotangent_lift_cancel (A:X->Prop)
    (f g:X->X) (D E:X->Hom X X) :
  (forall x,A x -> g (f x)=x) ->
  (forall x,A x -> forall v,E (f x) (D x v)=v) ->
  forall z,A (p z) -> @euclidean_cotangent_lift R n g D
    (@euclidean_cotangent_lift R n f E z)=z.
Proof.
move=>hgf hED z hz.
rewrite /euclidean_cotangent_lift -/(@euclidean_cotangent_lift R n f E z).
rewrite euclidean_cotangent_lift_base euclidean_cotangent_lift_vector (hgf _ hz).
have hcan:=@euclidean_adjoint_inverse R n (D (p z)) (E (f (p z))) (hED _ hz).
rewrite hcan.
exact: esym (@euclidean_block_linear_decomposition R n n z).
Qed.
End Lifts.
