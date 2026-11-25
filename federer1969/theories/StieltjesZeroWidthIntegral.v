(** Federer (1969), 2.9.24, p. 169: a=b is allowed. The Stieltjes integral
    over the zero-width interval is zero, directly from its defining uniform
    sums, without any global regularity hypothesis. The local Federer
    erratum has no entry for this boundary case. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  reals topology normedtype.
From Federer Require Import StieltjesSums StieltjesIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.

(** Source for [uniform_zero_width_stieltjes_sum]: supporting
    zero-width finite sums for Federer 2.9.24, p. 169.
    Every integrator increment is zero, regardless of tag values. *)
Lemma uniform_zero_width_stieltjes_sum (R : realType) (f g : R -> R) :
  forall (n : nat) (a : R), stieltjes_sum f g (uniform_tagged a 0 n)=0.
Proof.
elim=> [//|n ih] a.
have hhead (m : nat) (t : R) : exists s : seq R, uniform_tagged t 0 m=t::s.
  case: m=> [|m]; eexists; reflexivity.
have [s hs] := hhead n a.
change (stieltjes_sum f g (a::a::uniform_tagged (a+0) 0 n)=0).
rewrite addr0 hs.
change (f a*(g a-g a)+stieltjes_sum f g (a::s)=0).
rewrite subrr mulr0 add0r -hs; exact: ih a.
Qed.

(** Source for [stieltjes_integral_zero_width]: direct diagonal
    case of the integral in Federer 2.9.24, p. 169,
    by the definition of 2.5.17, pp. 110–111. No
    global continuity or variation premise is added at a=b. *)
Lemma stieltjes_integral_zero_width (R : realType) (f g : R -> R) (a : R) :
  stieltjes_integral f g a a=0.
Proof.
rewrite /stieltjes_integral /uniform_sums /uniform_partition.
have he : (fun n : nat => stieltjes_sum g f
    (uniform_tagged a ((a-a)/n.+1%:R) n.+1))=(fun _ => 0).
  apply: funext=> n; by rewrite subrr mul0r uniform_zero_width_stieltjes_sum.
by rewrite he lim_cst //; exact: Rhausdorff.
Qed.
