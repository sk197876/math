(** Federer (1969), 3.1.1, p. 211: partial derivatives of the
    remainder after subtracting the candidate linear approximation,
    and derivatives along coordinate segments. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP FiniteCoordinates GrassmannAbbreviations
  NormPartialDerivative NormedCurveDerivativeUP NormedCurveChainRule RealCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_partial_derivative_subtract_linear]: the
    displayed identity D_i g(x)=D_i f(x)-D_i f(a) in Federer 3.1.1,
    p. 211, with an arbitrary linear approximation L. Subtracting a
    constant has no effect on the quotient; the remainder f-L suffices. *)
Lemma norm_partial_derivative_subtract_linear (R : realType) n
    (Y : lmodType R) (NY : Y -> R) (f : R_n R n -> Y)
    (L : Hom (R_n R n) Y) (x : R_n R n) (i : 'I_n) (v : Y) :
  has_norm_partial_derivative NY f x i v ->
  has_norm_partial_derivative NY (fun z => f z-L z) x i
    (v-L (@coordinate_basis R n i)).
Proof.
move=> hf e he; have [d [hd hb]] := hf e he.
exists d; split=> // t ht.
have ht0 : t != 0 by move: (andP ht).1; rewrite normr_gt0.
have heq : (f (x+t *: (@coordinate_basis R n i))-L (x+t *: (@coordinate_basis R n i)))
    -(f x-L x) = (f (x+t *: (@coordinate_basis R n i))-f x)
      -t *: L (@coordinate_basis R n i).
  rewrite linearD linearZ /= opprD opprB !addrA.
  by rewrite [f (x+t *: (@coordinate_basis R n i))-L x-t *: L ((@coordinate_basis R n i))+L x]addrAC subrK addrAC.
rewrite heq scalerBr scalerA mulVf // scale1r opprB addrA subrK.
exact: hb t ht.
Qed.

(** Source for [norm_partial_coordinate_curve]: supporting
    interpretation of D_i f as the derivative on a coordinate line,
    Federer 3.1.1, p. 211. *)
Lemma norm_partial_coordinate_curve (R : realType) n (Y : lmodType R)
    (NY : Y -> R) (f : R_n R n -> Y) (b : R_n R n)
    (i : 'I_n) (s : R) (v : Y) :
  has_norm_partial_derivative NY f (b+s *: (@coordinate_basis R n i)) i v ->
  has_normed_curve_derivative NY (fun t => f (b+t *: (@coordinate_basis R n i))) s v.
Proof.
move=> hf e he; have [d [hd hb]] := hf e he.
exists d; split=> // t ht.
rewrite scalerDl addrA; exact: hb t ht.
Qed.

(** Source for [norm_partial_scaled_coordinate_curve]: the
    parametrised coordinate segment in the proof of Federer 3.1.1,
    p. 211. Its derivative is c times the corresponding partial
    derivative; c=0 is included by the proved curve chain rule. *)
Lemma norm_partial_scaled_coordinate_curve (R : realType) n (Y : lmodType R)
    (NY : Y -> R) (hNY : is_real_norm NY) (f : R_n R n -> Y)
    (b : R_n R n) (i : 'I_n) (c t : R) (v : Y) :
  has_norm_partial_derivative NY f (b+(t*c) *: (@coordinate_basis R n i)) i v ->
  has_normed_curve_derivative NY
    (fun s => f (b+(s*c) *: (@coordinate_basis R n i))) t (c *: v).
Proof.
move=> hf.
have hs : has_real_curve_derivative (fun s : R => s*c) t c.
  move=> e he; exists 1; split; first exact: ltr01.
  move=> h hh; have hn : h != 0 by move: (andP hh).1; rewrite normr_gt0.
  by rewrite [(t+h)*c]mulrDl [t*c+h*c-t*c]addrAC subrr add0r [h*c]mulrC mulfK // subrr normr0.
apply: (@normed_curve_derivative_compose R Y NY hNY
  (fun s => f (b+s *: (@coordinate_basis R n i))) (fun s => s*c) t c v hs).
exact: norm_partial_coordinate_curve hf.
Qed.
