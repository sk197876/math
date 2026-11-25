(** Federer (1969), 3.1.11, pp. 220–221:
    finite algebra for the normed-vector Taylor integral.
    The tagged lists are exactly those of 2.5.17,
    pp. 110–111. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP StieltjesSums StieltjesIntegral
  NormedStieltjesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [normed_stieltjes_sum_add]:
    linearity of the vector-valued tagged sums,
    supporting the Taylor integral in Federer 3.1.11,
    pp. 220–221, and 2.5.17, p. 111. *)
Lemma normed_stieltjes_sum_add (R : realType) (Y : lmodType R)
    (f q : R->Y) (g : R->R) (w : seq R) :
  normed_stieltjes_sum (fun t=>f t+q t) g w=
    normed_stieltjes_sum f g w+normed_stieltjes_sum q g w.
Proof.
have [n] := ubnP (size w); elim: n w=> // n ih [|t [|u [|t' rest]]] hsize /=;
  rewrite ?addr0 //.
have hs : (size (t'::rest)<n)%N by move: hsize; rewrite /= ltnS; exact: ltnW.
change ((g t'-g t)*:(f u+q u)+normed_stieltjes_sum (fun t=>f t+q t) g (t'::rest)=
  ((g t'-g t)*:f u+normed_stieltjes_sum f g (t'::rest))+
  ((g t'-g t)*:q u+normed_stieltjes_sum q g (t'::rest))).
by rewrite (ih _ hs) scalerDr addrACA.
Qed.

(** Source for [normed_stieltjes_sum_scale]:
    homogeneity of the vector-valued tagged sums,
    supporting the factorial coefficients in Federer
    3.1.11, pp. 220–221. *)
Lemma normed_stieltjes_sum_scale (R : realType) (Y : lmodType R)
    (f : R->Y) (g : R->R) (c : R) (w : seq R) :
  normed_stieltjes_sum (fun t=>c*:f t) g w=c*:normed_stieltjes_sum f g w.
Proof.
have [n] := ubnP (size w); elim: n w=> // n ih [|t [|u [|t' rest]]] hsize /=;
  rewrite ?scaler0 //.
have hs : (size (t'::rest)<n)%N by move: hsize; rewrite /= ltnS; exact: ltnW.
change ((g t'-g t)*:(c*:f u)+normed_stieltjes_sum (fun t=>c*:f t) g (t'::rest)=
  c*:((g t'-g t)*:f u+normed_stieltjes_sum f g (t'::rest))).
by rewrite (ih _ hs) scalerDr !scalerA mulrC.
Qed.

(** Source for [normed_stieltjes_sum_linear_image]:
    applying a linear map to the finite sums commutes
    with summation and real scalar multiplication,
    supporting the general Taylor formula of Federer
    3.1.11, pp. 220–221. *)
Lemma normed_stieltjes_sum_linear_image (R : realType) (Y Z : lmodType R)
    (f : R->Y) (g : R->R) (L : Hom Y Z) (w : seq R) :
  normed_stieltjes_sum (fun t=>L (f t)) g w=L (normed_stieltjes_sum f g w).
Proof.
have [n] := ubnP (size w); elim: n w=> // n ih [|t [|u [|t' rest]]] hsize /=;
  rewrite ?linear0 //.
have hs : (size (t'::rest)<n)%N by move: hsize; rewrite /= ltnS; exact: ltnW.
change ((g t'-g t)*:L (f u)+normed_stieltjes_sum (fun t=>L (f t)) g (t'::rest)=
  L ((g t'-g t)*:f u+normed_stieltjes_sum f g (t'::rest))).
by rewrite (ih _ hs) linearD linearZ.
Qed.

(** Source for [normed_stieltjes_sum_constant]:
    a constant integrand has the endpoint increment
    times its value, supporting the Taylor remainder
    normalization in Federer 3.1.11, pp. 220–221. *)
Lemma normed_stieltjes_sum_constant (R : realType) (Y : lmodType R)
    (g : R->R) (c : Y) (a b : R) (w : seq R) :
  is_tagged_partition a b w ->
  normed_stieltjes_sum (fun _=>c) g w=(g b-g a)*:c.
Proof.
have [n] := ubnP (size w); elim: n w a=> // n ih [|t [|u [|t' rest]]] a hsize hw.
- by case: hw=> [_ [hodd _]].
- have [_ [_ [ht hb]]] := hw; move: ht hb=> /= -> <-.
  by rewrite /= subrr scale0r.
- by case: hw=> [_ [hodd _]].
- have [t'' [rest' [he [hat [htu [hut' htail]]]]]] := tagged_partition_tail hw.
  case: he=> ht'' hrest'; subst t'' rest'.
  have hs : (size (t'::rest)<n)%N by move: hsize; rewrite /= ltnS; exact: ltnW.
  change ((g t'-g t)*:c+normed_stieltjes_sum (fun _=>c) g (t'::rest)=(g b-g a)*:c).
  rewrite (ih _ _ hs htail) hat -scalerDl.
  congr (_*:c); by rewrite addrC addrA subrK.
Qed.

(** Source for [normed_stieltjes_sum_scalar]:
    agreement with the scalar Stieltjes sums of
    Federer 2.5.17, p. 110, when applying
    their definition to the scalar Taylor formula
    in 3.1.11, p. 220. *)
Lemma normed_stieltjes_sum_scalar (R : realType) (f g : R->R) (w : seq R) :
  @normed_stieltjes_sum R R^o f g w=stieltjes_sum f g w.
Proof.
have [n] := ubnP (size w); elim: n w=> // n ih [|t [|u [|t' rest]]] hsize //=.
have hs : (size (t'::rest)<n)%N by move: hsize; rewrite /= ltnS; exact: ltnW.
change ((g t'-g t)*f u+@normed_stieltjes_sum R R^o f g (t'::rest)=
  f u*(g t'-g t)+stieltjes_sum f g (t'::rest)).
by rewrite (ih _ hs) mulrC.
Qed.
