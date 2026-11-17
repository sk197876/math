(** Federer (1969), 3.4.8(11), p. 333:
    successive nonzero punctured-axis restrictions force
    every coordinate of a common zero
    to vanish. This finite induction uses
    the original prefix maps and dual basis. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP LinearBasis GrassmannAbbreviations FiniteCoordinates
  AnalyticPrefixCoordinatesUP AnalyticZeroPrefixAxis AnalyticPrefixSuffixSeparation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [triangular_analytic_zero_isolation]:
    the triangular zero-isolation argument for
    m=0 in 3.4.8(11), p. 333.
    All actual axis conditions are supplied
    by the original regular germs; this
    supporting lemma proves the finite coordinate
    inference, including ambient dimension zero. *)
Theorem triangular_analytic_zero_isolation (R:realType) (X:lmodType R) n
    (e:'I_n->X) (he:is_basis e) (omega:'I_n->Hom X R^o)
    (hDual:forall i j,omega i (e j) = if i==j then 1 else 0)
    (P:forall j:'I_n,Hom X (R_n R (j:nat).+1))
    (f:forall j:'I_n,R_n R (j:nat).+1->R^o) (d:'I_n->R):
  (forall j,is_analytic_prefix_projection omega (ltn_ord j) (P j)) ->
  (forall j t,0<`|t|<d j ->f j (t*:@coordinate_basis R (j:nat).+1 ord_max)<>0) ->
  forall x,(forall j,`|omega j x|<d j) ->(forall j,f j (P j x) = 0) ->x = 0.
Proof.
move=>hP hAxis x hSmall hEquation.
have hZero r:(r<=n)%N ->forall i:'I_n,(i<r)%N ->omega i x = 0.
  elim:r=>[|r IH] hRN i hi;first by move:hi;rewrite ltn0.
  have hPrevious:forall j:'I_n,(j<r)%N ->omega j x = 0.
    exact:IH (leq_trans (leqnSn r) hRN).
  have hLastIndex:(r<n)%N:=hRN.
  pose j:'I_n:=Ordinal hLastIndex.
  have hLast:omega j x = 0.
    apply:contrapT=>hNonzero.
    have hPositive:0<`|omega j x| by rewrite normr_gt0;apply/eqP;exact:hNonzero.
    have hRange:0<`|omega j x|<d j by apply/andP;split.
    have hLine:=hAxis j (omega j x) hRange.
    have hPrefix:=@analytic_zero_prefix_axis R X n omega j (P j) (hP j) x hPrevious.
    apply:hLine;rewrite -hPrefix;exact:hEquation j.
  case:(ltnP i r)=>hIR;first exact:hPrevious i hIR.
  have hEqual:i = j.
    apply:val_inj;apply/eqP;rewrite eqn_leq hIR andbT.
    exact:hi.
  by rewrite hEqual.
have hAll:forall i:'I_n,omega i x = 0 by move=>i;exact:hZero n (leqnn n) i (ltn_ord i).
have hExpansion:=@analytic_original_given_basis_expansion R X n e he omega hDual x.
rewrite {1}hExpansion.
apply:big1=>i _;by rewrite hAll scale0r.
Qed.
