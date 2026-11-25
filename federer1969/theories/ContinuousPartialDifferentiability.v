(** Federer (1969), 3.1.1, p. 211: existence of all partial
    derivatives on a common neighbourhood, and continuity of each at a,
    imply differentiability at a. The proof follows the printed
    subtraction and coordinate telescoping argument. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness BasisInterpolation
  NormDifferentialUP NormFiniteLinearBound NormPartialDerivative
  NormPartialDerivativeCalculus NormPartialDerivativeBallBound FiniteCommonRadius.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [continuous_partials_differential]: the final
    differentiability criterion of Federer 3.1.1, p. 211. Only continuity
    of the partial derivatives at a is required, not continuity at every
    nearby point. Their common neighbourhood belongs to the actual
    domain A. The candidate L is specified by its standard-basis values. *)
Theorem continuous_partials_differential (R : realType) n (Y : lmodType R)
    (NY : Y -> R) (hNY : is_real_norm NY) (A : R_n R n -> Prop)
    (f : R_n R n -> Y) (a : R_n R n) (p : 'I_n -> R_n R n -> Y)
    (L : Hom (R_n R n) Y) :
  (forall i, L (@coordinate_basis R n i)=p i a) ->
  (exists r : R, 0 < r /\ forall x,
    inner_norm (@euclidean_inner_productP R n) (x-a) < r ->
    A x /\ forall i, has_norm_partial_derivative NY f x i (p i x)) ->
  (forall i, forall e : R, 0 < e -> exists d : R, 0 < d /\
    forall x, A x -> inner_norm (@euclidean_inner_productP R n) (x-a) < d ->
      NY (p i x-p i a) < e) ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R n)) NY A f a L.
Proof.
move=> hL [r [hr hp]] hc.
pose NX := inner_norm (@euclidean_inner_productP R n).
have hNX : is_real_norm NX := inner_norm_real_norm (@euclidean_inner_productP R n).
constructor.
- exists r; split=> // h hh.
  have ha : NX (a+h-a) < r by rewrite addrAC subrr add0r.
  exact: (hp (a+h) ha).1.
- exact: (@norm_finite_linear_bounded R (R_n R n) Y NX NY hNX hNY n
    (@coordinate_basis R n) (@coordinate_basisP R n) L).
- move=> e he.
  pose c := e/(n%:R+1).
  have hn : 0 <= (n%:R : R) := ler0n _ _.
  have hden : 0 < (n%:R : R)+1 by lra.
  have hc0 : 0 < c by rewrite /c divr_gt0.
  have hu : exists d : R, 0 < d /\ forall i x,
      NX (x-a) < d -> A x -> NY (p i x-p i a) < c.
    apply: (@finite_common_radius R (Finite.clone 'I_n _) (R_n R n)
      (fun x => NX (x-a)) (fun i x => A x -> NY (p i x-p i a) < c))=> i.
    have [d [hd hb]] := hc i c hc0.
    exists d; split=> // x hx hAx; exact: hb x hAx hx.
  have [d [hd hb]] := hu.
  pose s := Num.min r d.
  have hs : 0 < s by rewrite /s lt_min hr hd.
  have hsr : s <= r by rewrite /s ge_min lexx.
  have hsd : s <= d by rewrite /s ge_min lexx orbT.
  have hg : forall x, NX (x-a) < s -> forall i, exists v : Y,
      has_norm_partial_derivative NY (fun z => f z-L z) x i v /\ NY v <= c.
    move=> x hx i; have [hAx hpx] := hp x (lt_le_trans hx hsr).
    exists (p i x-L (@coordinate_basis R n i)); split.
    + exact: (norm_partial_derivative_subtract_linear L (hpx i)).
    + rewrite hL; exact: ltW (hb i x (lt_le_trans hx hsd) hAx).
  exists s; split=> // h _ hh.
  have hbound := @norm_partial_derivative_ball_increment R n Y NY hNY
    (fun z => f z-L z) a s c (ltW hc0) hg h hh.
  have heq : (f (a+h)-L (a+h))-(f a-L a)=f (a+h)-f a-L h.
    rewrite linearD /= opprD opprB !addrA.
    by rewrite [f (a+h)-L a-L h+L a]addrAC subrK addrAC.
  rewrite heq in hbound; apply: le_trans hbound _.
  have hcEq : c*(n%:R+1)=e by rewrite /c divfK // gt_eqF.
  have hcN : n%:R*c <= e by nra.
  apply: ler_wpM2r; first exact: real_seminorm_nonnegative hNX.1 h.
  exact hcN.
Qed.

(** Source for [continuous_partials_differentiable]: existence
    form of Federer's continuous-partials criterion, 3.1.1, p. 211.
    The basis universal property supplies the candidate linear map;
    its continuity is proved from finite dimension. Dimension zero is
    included, with the domain-neighbourhood condition still explicit. *)
Theorem continuous_partials_differentiable (R : realType) n (Y : lmodType R)
    (NY : Y -> R) (hNY : is_real_norm NY) (A : R_n R n -> Prop)
    (f : R_n R n -> Y) (a : R_n R n) (p : 'I_n -> R_n R n -> Y) :
  (exists r : R, 0 < r /\ forall x,
    inner_norm (@euclidean_inner_productP R n) (x-a) < r ->
    A x /\ forall i, has_norm_partial_derivative NY f x i (p i x)) ->
  (forall i, forall e : R, 0 < e -> exists d : R, 0 < d /\
    forall x, A x -> inner_norm (@euclidean_inner_productP R n) (x-a) < d ->
      NY (p i x-p i a) < e) ->
  norm_differentiable_at (inner_norm (@euclidean_inner_productP R n)) NY A f a.
Proof.
move=> hp hc.
pose L := hom_of_linear (basis_interpolation (@coordinate_basisP R n) (fun i => p i a)).
exists L; apply: (@continuous_partials_differential R n Y NY hNY A f a p L _ hp hc)=> i.
rewrite /L hom_of_linearE; exact: basis_interpolationE.
Qed.
