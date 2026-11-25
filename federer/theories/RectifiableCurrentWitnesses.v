(** Federer (1969), 4.1.24, pp. 380–381: every
    original image witness is rectifiable; identity places
    integral polyhedral currents in the rectifiable class.
    Zero is retained on every original open domain and
    compact index, including empty ones. No source point
    is selected. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP LipschitzBasic SmoothCompactSet CurrentSpaces CurrentMassSealed
  CurrentMassFiniteAlgebra FlatCurrentsUP CurrentFlatIdentityPushforward
  PolyhedralCurrentAlgebra PolyhedralCurrentFlat RectifiableCurrentApproximationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section RectifiableCurrentWitnesses.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set hNX U.
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation Rect:=(@is_rectifiable_current_supported_in R h2 n m U hU K).
Local Notation Approx:=(@is_rectifiable_image_approximant R h2 n m U hU K).

(** Source for [rectifiable_image_approximant_is_rectifiable]: the
    defining image witnesses themselves satisfy the mass
    approximation property, Federer 4.1.24, p. 380.
    Reusing a witness gives zero mass error for every
    positive tolerance, without additional input hypotheses. *)
Theorem rectifiable_image_approximant_is_rectifiable (T:C):Approx T->Rect T.
Proof.
move=>hT epsilon hEpsilon;exists T;split;first exact:hT.
by rewrite subrr current_mass_zero lte_fin.
Qed.

(** Source for [integral_polyhedral_current_rectifiable_supported]:
    the identity Lipschitz witness places the original
    integral polyhedral class in the same-K rectifiable
    class, supporting 4.1.24's diagram on p. 381.
    The witness works unchanged for empty U and K. *)
Theorem integral_polyhedral_current_rectifiable_supported (T:C):
  @integral_polyhedral_current_class R h2 n m U hU K T->Rect T.
Proof.
move=>hT;apply:rectifiable_image_approximant_is_rectifiable.
have hLip:@is_metric_lipschitz R (real_norm_metric_space hNX)
    (real_norm_metric_space hNX) U (fun x=>x).
  exists 1;split;first exact:ltr01.
  split;first exact:ler01.
  by move=>x y hx hy;rewrite mul1r.
pose hImage:=fun (x:X) (hx:U x)=>hx.
exists n,U,hU,K,(fun x:X=>x),hImage,hLip,T,hT;split.
- by move=>x hx.
- unfold polyhedral_lipschitz_image.
  exact:current_flat_lipschitz_identity_pushforward.
Qed.

(** Source for [rectifiable_current_zero]: the zero
    current satisfies the literal original definition at
    every compact index, Federer 4.1.24, p. 380.
    Identity and the zero integral polyhedral current
    give a witness even on the empty domain. *)
Theorem rectifiable_current_zero:Rect (0:C).
Proof.
apply:integral_polyhedral_current_rectifiable_supported.
exact:integral_polyhedral_current_zero.
Qed.
End RectifiableCurrentWitnesses.
