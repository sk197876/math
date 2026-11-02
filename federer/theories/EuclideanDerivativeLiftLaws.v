(** Federer (1969), 3.1.21, p. 234: the derivative lift
    of a diffeomorphism has the corresponding inverse lift. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom Bilinear GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  EuclideanBlockLinearMaps EuclideanBundleUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Lifts.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation P := (R_n R (n+n)).
Local Notation p := (@euclidean_first_block_map R n n).
Local Notation q := (@euclidean_last_block_map R n n).
Local Notation i := (@euclidean_first_injection_map R n n).
Local Notation j := (@euclidean_last_injection_map R n n).

(** Source for [euclidean_derivative_lift_base]: the base
    coordinate of the tangent lift is f(x), supporting the
    bundle assertion of Federer 3.1.21, p. 234. *)
Lemma euclidean_derivative_lift_base (f:X->X) (D:X->Hom X X) z :
  p (@euclidean_derivative_lift R n f D z)=f (p z).
Proof.
have hpi y:p (i y)=y:=@euclidean_first_block_injectionK R n n y.
have hpj y:p (j y)=0:=@euclidean_first_block_last_injection R n n y.
by rewrite /euclidean_derivative_lift (linD (hom_linear p)) hpi hpj addr0.
Qed.

(** Source for [euclidean_derivative_lift_vector]: the fibre
    coordinate of the tangent lift is Df(x)v, supporting
    Federer 3.1.21, p. 234. *)
Lemma euclidean_derivative_lift_vector (f:X->X) (D:X->Hom X X) z :
  q (@euclidean_derivative_lift R n f D z)=D (p z) (q z).
Proof.
have hqi y:q (i y)=0:=@euclidean_last_block_first_injection R n n y.
have hqj y:q (j y)=y:=@euclidean_last_block_injectionK R n n y.
by rewrite /euclidean_derivative_lift (linD (hom_linear q)) hqi hqj add0r.
Qed.

(** Source for [euclidean_derivative_lift_cancel]: supporting
    inverse law for the tangent bundle charts in Federer
    3.1.21, p. 234. Inverse functions and inverse
    differentials give inverse ambient lifts. *)
Lemma euclidean_derivative_lift_cancel (A:X->Prop)
    (f g:X->X) (D E:X->Hom X X) :
  (forall x,A x -> g (f x)=x) ->
  (forall x,A x -> forall v,E (f x) (D x v)=v) ->
  forall z,A (p z) -> @euclidean_derivative_lift R n g E
    (@euclidean_derivative_lift R n f D z)=z.
Proof.
move=>hgf hED z hz.
rewrite /euclidean_derivative_lift -/(@euclidean_derivative_lift R n f D z).
rewrite euclidean_derivative_lift_base euclidean_derivative_lift_vector (hgf _ hz) (hED _ hz).
exact: esym (@euclidean_block_linear_decomposition R n n z).
Qed.
End Lifts.
