(** Federer (1969), 3.2.28(4), printed p. 267:
    the square representation of G(n,m) is well-defined,
    one-to-one and onto the actual square image of Go.
    The choice of orientation does not affect its value. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom TensorUP ModuleQuotient InnerProductUP InnerNorm InnerNormalization
  GrassmannSubspaces GrassmannSurjection NonzeroSimple AssociatedSubspace SimpleElementary
  SimpleProportionality ExteriorGrading ExteriorNorm InnerExteriorPositivity
  SymmetricGrading SymmetricSquareGeometry GrassmannSquareUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Realisation.
Variable R:realType.
Variable V:lmodType R.
Variable B:V->V->R.
Hypothesis hB:is_inner_product B.
Variable h2:(1+1:R)!=0.
Variable m:nat.
Local Notation E:=(exterior_power V m).
Local Notation hE:=(@exterior_inner_productP R h2 V B hB m).
Local Notation N:=(inner_norm hE).
Local Notation T:=(@inner_projective_square R E).

(** Source for [grassmann_square_representative_exists]: every
    m-plane has a unit top exterior vector and hence the
    required square, Federer 3.2.28(4), p. 267,
    by 1.6.2 and 1.7.5, pp. 24,32. Positive
    degree respects the literal simple-vector convention. *)
Theorem grassmann_square_representative_exists:
  (0<m)%N ->forall P:G V m,exists t,is_grassmann_square_representative hB h2 P t.
Proof.
move=>hm P.
have [xi hXi]:=@associated_G_surjective R h2 V m P.
pose x:=simple_val xi.
have hx:x!=0:=simple_val_nonzero xi.
pose z:=inner_normalize hE x.
have hc:(N x)^-1!=0 by rewrite invr_eq0 (inner_norm_eq0 hE).
exists (T z); exists z; split.
- change (simple ((N x)^-1*:x)).
  exact:(@simple_scale R V m x (N x)^-1 hm (simple_val_simple xi)).
split; first exact:(@inner_normalize_norm R E _ hE x hx).
split; last reflexivity.
move=>v; rewrite -hXi.
change (FedererSimple.T x v <->FedererSimple.T ((N x)^-1*:x) v).
symmetry; exact:(@associated_scale_nonzero R V m x (N x)^-1 hc v).
Qed.

(** Source for [grassmann_square_representative_unique]: changing
    the unit generator changes only its sign, and hence
    not its square, Federer 3.2.28(4), p. 267,
    by the proportionality corollary in 1.6.1, p. 24. *)
Theorem grassmann_square_representative_unique (P:G V m) s t:
  is_grassmann_square_representative hB h2 P s ->
  is_grassmann_square_representative hB h2 P t ->s=t.
Proof.
move=>[x [hx [hNx [hPx hXs]]]] [y [hy [hNy [hPy hYt]]]].
have hX:x!=0 by apply/eqP=>hz; move:hNx; rewrite hz exterior_norm_zero=>/eqP; by rewrite eq_sym oner_eq0.
have hY:y!=0 by apply/eqP=>hz; move:hNy; rewrite hz exterior_norm_zero=>/eqP; by rewrite eq_sym oner_eq0.
have hSame v:FedererSimple.T x v <->FedererSimple.T y v.
  by rewrite -hPx -hPy.
have [c [hc hxy]]:=(@simple_associated_equal R h2 V m x y hX hY hy).1 hSame.
have hAbs:`|c|= 1.
  have he:=congr1 N hxy.
  rewrite inner_normZ in he.
  change (exterior_norm h2 hB x=`|c|*exterior_norm h2 hB y) in he.
  by rewrite hNx hNy mulr1 in he; symmetry.
have hSq:c^+2=(1:R)^+2.
  by rewrite expr1n -[c^+2](ger0_norm (sqr_ge0 c)) normrX hAbs expr1n.
have hSign:(c== 1)||(c== -1) by rewrite -eqf_sqr hSq eqxx.
rewrite -hXs -hYt hxy.
case/orP:hSign=>/eqP ->; first by rewrite scale1r.
rewrite scaleN1r; exact:(@inner_projective_square_antipodal R E _ hE y).
Qed.

(** Source for [grassmann_square_representative_injective]: equal
    squares represent the same unoriented plane, Federer
    3.2.28(4), p. 267. The actual two-point
    unit fibres are used, without quotient assumptions. *)
Theorem grassmann_square_representative_injective (P Q:G V m) t:
  is_grassmann_square_representative hB h2 P t ->
  is_grassmann_square_representative hB h2 Q t ->P=Q.
Proof.
move=>[x [hx [hNx [hPx hXt]]]] [y [hy [hNy [hQy hYt]]]].
have hSquare:T x=T y by rewrite hXt hYt.
have hSigns:=(@inner_projective_square_unit_fibre R E _ hE x y hNx hNy).1 hSquare.
apply:grassmann_ext=>v; rewrite hPx hQy.
case:hSigns=>->; first by [].
rewrite -[(-y):E]scaleN1r.
have hNeg:(-1:R)!=0 by rewrite oppr_eq0 oner_eq0.
change (FedererSimple.T ((-1:R)*:y) v <->FedererSimple.T y v).
exact:(@associated_scale_nonzero R V m y (-1) hNeg v).
Qed.
End Realisation.
