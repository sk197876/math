(** Federer (1969), 3.2.33, p. 270: scalar order
    passage used for positivity of the actual smooth series. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_sequence_limit_lower_bound]: supporting
    positivity of psi in Federer 3.2.33, p. 270.
    A lower bound on every sufficiently late partial sum
    remains a lower bound on its actual scalar limit.
    This follows directly from the absolute-error definition. *)
Lemma scalar_sequence_limit_lower_bound (R:realType) (u:nat->R) z c N:
  (forall e:R,0<e ->exists n:nat,forall M,(n<=M)%N ->`|u M-z|<e) ->
  (forall M,(N<=M)%N ->c<=u M) ->c<=z.
Proof.
move=>hLimit hBound; apply/ler_addgt0Pr=>e he.
have [n hn]:=hLimit e he.
have hMN:(N<=maxn N n)%N:=leq_maxl _ _.
have hMn:(n<=maxn N n)%N:=leq_maxr _ _.
have hClose:=hn _ hMn.
have hError:=ler_norm (u (maxn N n)-z).
have hLow:=hBound _ hMN; lra.
Qed.
